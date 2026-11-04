import Clocrap.Function
import Clocrap.Lex

/-!
# JavaScript and TypeScript

Functions are function declarations and expressions (generators too), methods in classes and
object literals, and arrow functions. A function written as a variable's, a class field's or an
object key's whole value takes that name; any other is `<anonymous>`. Signatures without a body
(overloads, abstract methods, interface members) are not functions, and nor are function types.

Decisions are `if`, `for` (all three kinds), `while`, `do`, each `case` (not `default`), `catch`,
the ternary operator, `&&`, `||` and `??`. `&&=`, `||=` and `??=` are not, and nor is a conditional
type's `?`.

Telling a function type from an arrow, or a type literal from a block, takes the context a parse
has, so this is a small recursive-descent parser over the tokens: statements, expressions, and
types skipped whole. It tolerates what it does not know by stepping over a token.
-/

namespace Clocrap.JsLang

open Lex

structure Ctx where
  ts : Array Tok
  m : Array Nat
  src : ByteArray
  typescript : Bool

structure St where
  weight : Array Int
  found : Array Found

abbrev P := ReaderT Ctx (StateM St)

def tok (i : Nat) : P Tok := do return (← read).ts[i]?.getD default
def close (i : Nat) : P Nat := do return (← read).m[i]?.getD i
def bump (i : Nat) : P Unit := modify fun s => { s with weight := s.weight.modify i (· + 1) }

def isOpen (t : Tok) : Bool := t.kind == .punct && !t.jsx && (t.text == "(" || t.text == "[" || t.text == "{")

/-- Whether a token can end an expression, so a line break after it may end the statement. -/
def endsExpr (t : Tok) : Bool :=
  match t.kind with
  | .num | .str => true
  | .ident => true
  | .punct => t.text == ")" || t.text == "]" || t.text == "}" || t.text == "++" || t.text == "--" ||
    t.text == "!"

/-- Symbols and words that carry an expression on from the line before: no semicolon is inserted
before them. -/
def continues (t : Tok) : Bool :=
  match t.kind with
  | .punct => !(t.text == "{" || t.text == "!" || t.text == "~" || t.text == "++" ||
      t.text == "--" || t.text == "@" || t.text == "}")
  | .ident => t.text == "in" || t.text == "instanceof" || t.text == "as" || t.text == "satisfies"
  | _ => false

/-- Whether a statement ends before `k`, the first token of a line. -/
def lineEnds (i k : Nat) : P Bool := do
  if k ≤ i then return false
  let t ← tok k
  -- A brace inside JSX carries on the element it is in, whatever line it starts.
  if !t.first || continues t || t.jsx then return false
  return endsExpr (← tok (k - 1))

def typeOperator (t : Tok) : Bool :=
  (t.kind == .punct && #[":", "|", "&", "<", ",", "(", "=>", "?", "=", "["].contains t.text) ||
    (t.kind == .ident && #["extends", "keyof", "readonly", "typeof", "is", "infer"].contains t.text)

def typeContinues (t : Tok) : Bool :=
  (t.kind == .punct && #["|", "&", ".", "<", ">", "[", "?", ":", "=>"].contains t.text) ||
    t.isId "extends"

/-- Steps over a type from `i`, up to a token in `stops` outside its brackets. A `{` in `stops`
only stops it where a type cannot start, so `(): { a: T } {` stops at the second brace. -/
def skipType (i e : Nat) (stops : Array String) (asi : Bool) : P Nat := do
  let c ← read
  let mut k := i
  let mut angle := 0
  let mut sawExtends := false
  while k < e do
    let t := c.ts[k]!
    if angle == 0 && t.kind == .punct && stops.contains t.text then
      if t.text == "{" && k > i && typeOperator c.ts[k - 1]! then
        k := c.m[k]! + 1
        continue
      if t.text == "{" && k == i then
        k := c.m[k]! + 1
        continue
      if (t.text == "?" || t.text == ":") && sawExtends then
        k := k + 1
        continue
      return k
    if asi && angle == 0 && k > i && t.first && !typeContinues t && !typeOperator c.ts[k - 1]! then
      return k
    if t.is "<" then angle := angle + 1
    else if t.is ">" && angle > 0 then angle := angle - 1
    else if t.isId "extends" then sawExtends := true
    if isOpen t then k := c.m[k]! + 1 else k := k + 1
  return k

/-- The index after `<…>` at `i`. -/
def skipAngles (i e : Nat) : P Nat := do
  let c ← read
  let mut k := i
  let mut depth := 0
  while k < e do
    let t := c.ts[k]!
    if t.is "<" then depth := depth + 1
    else if t.is ">" then
      depth := depth - 1
      if depth == 0 then return k + 1
    if isOpen t then k := c.m[k]! + 1 else k := k + 1
  return k

/-- The index after type arguments at `<` `k`, as in `f<T>(x)`: balanced angles holding only what
a type may, and a call or a template after them. `none` for a comparison. -/
def typeArgsEnd (k e : Nat) : P (Option Nat) := do
  let c ← read
  let mut j := k
  let mut depth := 0
  while j < e do
    let t := c.ts[j]!
    if t.is "<" then depth := depth + 1
    else if t.is ">" then
      depth := depth - 1
      if depth == 0 then
        let after := c.ts[j + 1]?
        return if after.any (fun n => n.is "(" || (n.kind == .str && !n.jsx)) then some (j + 1) else none
    else if t.kind == .punct && #[";", "&&", "||", "??", "=", "!", "+", "-", "*", "/", "==", "===",
        "!=", "!==", "<=", ">=", "%", "}", ")", "]"].contains t.text then return none
    if isOpen t then j := c.m[j]! + 1 else j := j + 1
  return none

/-- Whether the `(` at `p` holds an arrow function's parameters: `=>` follows it, or a return type
and then `=>`. -/
def arrowParams (p e : Nat) : P Bool := do
  let c ← read
  let q := c.m[p]!
  let next := c.ts[q + 1]?
  if next.any (·.is "=>") then return true
  if !(next.any (·.is ":")) || !c.typescript then return false
  let mut k := q + 2
  let mut angle := 0
  while k < e do
    let t := c.ts[k]!
    if t.jsx then return false
    if t.is "=>" && angle == 0 then return true
    if t.is "<" then angle := angle + 1
    else if t.is ">" && angle > 0 then angle := angle - 1
    else if t.kind == .punct && (#[";", ")", "]", "}", "="].contains t.text ||
        (t.text == "," && angle == 0)) then return false
    if isOpen t then k := c.m[k]! + 1 else k := k + 1
  return false

def record (name : String) (first last : Nat) : P Unit :=
  modify fun s => { s with found := s.found.push { name, first, last, complexity := 0 } }

/-- Names the function that is the whole of `start..stop` after `name`. -/
def bind (start stop : Nat) (name : String) : P Unit := do
  modify fun s =>
    match s.found.findIdx? (fun f => f.first == start && f.last + 1 == stop &&
        f.name == "<anonymous>") with
    | some n => { s with found := s.found.modify n fun f => { f with name } }
    | none => s

def sourceText (first last : Nat) : P String := do
  let c ← read
  return textOf c.src c.ts[first]!.start c.ts[last]!.stop

def exprStops : Array String := #[")", "]", "}", ",", ";", "=", "?", ":", "&&", "||", "??", "=>"]

mutual

/-- An expression from `i`, up to a token in `stops` outside brackets, or with `asi` a line
break that ends the statement. Returns the index it stopped at. -/
partial def expr (i e : Nat) (stops : Array String) (asi : Bool) : P Nat := do
  let c ← read
  let mut k := i
  while k < e do
    let t := c.ts[k]!
    if t.kind == .punct && stops.contains t.text then return k
    if asi && (← lineEnds i k) then return k
    let prevEnds := k > i && endsExpr c.ts[k - 1]! && !(c.ts[k - 1]!.kind == .ident &&
      #["return", "typeof", "void", "delete", "await", "yield", "new", "in", "of", "case",
        "throw", "instanceof"].contains c.ts[k - 1]!.text)
    match t.kind with
    | .punct =>
      if t.jsx || t.text == "[" then
        k := (← group k)
      else if t.text == "(" then
        if ← arrowParams k e then k := (← arrow k k e stops asi)
        else k := (← group k)
      else if t.text == "{" then
        k := (← object k)
      else if t.text == "?" then
        bump k
        let r ← expr (k + 1) e #[":"] false
        k := r + 1
      else if t.text == "&&" || t.text == "||" || t.text == "??" then
        bump k
        k := k + 1
      else if t.text == "<" && c.typescript && !prevEnds then
        let a ← skipAngles k e
        if (c.ts[a]?.any (·.is "(")) && (← arrowParams a e) then k := (← arrow k a e stops asi)
        else k := a
      else if t.text == "<" && c.typescript then
        -- `f<T>(x)`: type arguments, when what follows the `>` is a call.
        match ← typeArgsEnd k e with
        | some a => k := a
        | none => k := k + 1
      else k := k + 1
    | .ident =>
      let next := c.ts[k + 1]?
      if t.text == "function" && !(k > 0 && c.ts[k - 1]!.is ".") then
        k := (← function k)
      else if t.text == "async" && next.any (·.isId "function") then
        k := (← function k)
      else if t.text == "async" && next.any (·.is "(") && (← arrowParams (k + 1) e) then
        k := (← arrow k (k + 1) e stops asi)
      else if t.text == "async" && next.any (·.is "<") && c.typescript then
        let a ← skipAngles (k + 1) e
        if (c.ts[a]?.any (·.is "(")) && (← arrowParams a e) then k := (← arrow k a e stops asi)
        else k := k + 1
      else if t.text == "async" && next.any (·.kind == .ident) &&
          (c.ts[k + 2]?.any (·.is "=>")) then
        k := (← arrow k (k + 1) e stops asi)
      else if t.text == "class" && !(k > 0 && c.ts[k - 1]!.is ".") then
        k := (← classDecl k)
      else if (t.text == "as" || t.text == "satisfies") && prevEnds && c.typescript then
        k := (← skipType (k + 1) e (stops ++ exprStops) asi)
      else if next.any (·.is "=>") && !(k > 0 && c.ts[k - 1]!.is ".") then
        k := (← arrow k k e stops asi)
      else k := k + 1
    | _ => k := k + 1
  return k

/-- A bracketed expression or argument list at `g`. Returns the index after it. -/
partial def group (g : Nat) : P Nat := do
  let q ← close g
  let _ ← expr (g + 1) q #[] false
  return q + 1

/-- An arrow function starting at `first`, with its parameters (a `(` or a name) at `p`. -/
partial def arrow (first p e : Nat) (stops : Array String) (asi : Bool) : P Nat := do
  let c ← read
  let mut j := p + 1
  if c.ts[p]!.is "(" then
    params p
    j := c.m[p]! + 1
  if c.ts[j]?.any (·.is ":") then j := (← skipType (j + 1) e #["=>"] false)
  if !(c.ts[j]?.any (·.is "=>")) then return j
  let body := j + 1
  if c.ts[body]?.any (fun t => t.is "{" && !t.jsx) then
    let q := c.m[body]!
    statements (body + 1) q
    record "<anonymous>" first q
    return q + 1
  -- An arrow's body is one assignment expression: a comma ends it.
  let r ← expr body e (stops ++ #[",", ";"]) asi
  record "<anonymous>" first (r - 1)
  return r

/-- A parameter list at `p`. -/
partial def params (p : Nat) : P Unit := do
  let c ← read
  let q := c.m[p]!
  let mut k := p + 1
  while k < q do
    let t := c.ts[k]!
    if t.is "," || t.is "..." || t.is "?" || t.is "!" then k := k + 1
    else if t.is "@" then k := (← decorator k)
    else if t.is ":" then k := (← skipType (k + 1) q #[",", "="] false)
    else if t.is "=" then k := (← expr (k + 1) q #[","] false)
    else if t.is "{" then k := (← object k)
    else if t.is "[" then k := (← group k)
    else k := k + 1

/-- `@name`, `@a.b`, `@name(…)`. Returns the index after it. -/
partial def decorator (k : Nat) : P Nat := do
  let c ← read
  let mut j := k + 2
  while c.ts[j]?.any (·.is ".") && (c.ts[j + 1]?.any (·.kind == .ident)) do j := j + 2
  if c.ts[j]?.any (·.is "(") then j := (← group j)
  return j

/-- `function`, `async function`, `function*`, at `i`. Returns the index after it. -/
partial def function (i : Nat) : P Nat := do
  let c ← read
  let mut k := i
  if c.ts[k]!.isId "async" then k := k + 1
  k := k + 1
  if c.ts[k]?.any (·.is "*") then k := k + 1
  let mut name := "<anonymous>"
  if let some t := c.ts[k]? then
    if t.kind == .ident then
      name := t.text
      k := k + 1
  if c.ts[k]?.any (·.is "<") then k := (← skipAngles k c.ts.size)
  if !(c.ts[k]?.any (·.is "(")) then return k
  params k
  k := c.m[k]! + 1
  if c.ts[k]?.any (·.is ":") then k := (← skipType (k + 1) c.ts.size #["{", ";"] true)
  if c.ts[k]?.any (fun t => t.is "{" && !t.jsx) then
    let q := c.m[k]!
    statements (k + 1) q
    record name i q
    return q + 1
  return k

/-- A method whose first token is `first`, its key at `key..after`. Returns the index after it, or
`none` when it has no body (a signature). -/
partial def method (first key after : Nat) : P (Option Nat) := do
  let c ← read
  let mut k := after
  if c.ts[k]?.any (·.is "<") then k := (← skipAngles k c.ts.size)
  if !(c.ts[k]?.any (·.is "(")) then return none
  params k
  k := c.m[k]! + 1
  if c.ts[k]?.any (·.is ":") then k := (← skipType (k + 1) c.ts.size #["{", ";", ",", "}"] true)
  if c.ts[k]?.any (fun t => t.is "{" && !t.jsx) then
    let q := c.m[k]!
    statements (k + 1) q
    record (← sourceText key (after - 1)) first q
    return some (q + 1)
  return none

/-- The end of a property key at `k`: a name, string, number or `[…]`. -/
partial def keyEnd (k : Nat) : P Nat := do
  let c ← read
  if c.ts[k]?.any (·.is "[") then return c.m[k]! + 1
  return k + 1

/-- An object literal (or a destructuring pattern) at `b`. Returns the index after it. -/
partial def object (b : Nat) : P Nat := do
  let c ← read
  let q := c.m[b]!
  let mut k := b + 1
  while k < q do
    let t := c.ts[k]!
    if t.is "," then
      k := k + 1
      continue
    if t.is "..." then
      k := (← expr (k + 1) q #[","] false)
      continue
    let start := k
    -- `async`, `get`, `set` and `*` before a key are modifiers; alone they are keys.
    while k < q && (c.ts[k]!.isId "async" || c.ts[k]!.isId "get" || c.ts[k]!.isId "set" ||
        c.ts[k]!.is "*") && !(c.ts[k + 1]?.any fun n =>
          n.is "(" || n.is ":" || n.is "," || n.is "}" || n.is "=" || n.is "<") do
      k := k + 1
    let after ← keyEnd k
    let next := c.ts[after]?
    if next.any (fun n => n.is "(" || n.is "<") then
      match ← method start k after with
      | some r => k := r
      | none => k := (← expr after q #[","] false)
    else if next.any (·.is ":") then
      let v := after + 1
      let r ← expr v q #[","] false
      bind v r (← sourceText k (after - 1))
      k := r
    else if next.any (·.is "=") then
      k := (← expr (after + 1) q #[","] false)
    else
      k := if after > k then after else k + 1
  return q + 1

/-- A class at `i` (`class` or `abstract class`). Returns the index after it. -/
partial def classDecl (i : Nat) : P Nat := do
  let c ← read
  let mut k := i + 1
  -- The body is the first brace at this level: a heritage clause cannot hold a block.
  while k < c.ts.size && !(c.ts[k]!.is "{" && !c.ts[k]!.jsx) do
    if c.ts[k]!.is "(" || c.ts[k]!.is "[" then k := c.m[k]! + 1
    else if c.ts[k]!.is ";" then return k
    else k := k + 1
  if k ≥ c.ts.size then return k
  let q := c.m[k]!
  classBody k
  return q + 1

partial def classBody (b : Nat) : P Unit := do
  let c ← read
  let q := c.m[b]!
  let mods := #["public", "private", "protected", "static", "readonly", "abstract", "override",
    "declare", "accessor", "async", "get", "set"]
  let mut k := b + 1
  while k < q do
    let t := c.ts[k]!
    if t.is ";" || t.is "," then
      k := k + 1
      continue
    if t.is "@" then
      k := (← decorator k)
      continue
    if t.isId "static" && (c.ts[k + 1]?.any (·.is "{")) then
      let r := c.m[k + 1]!
      statements (k + 2) r
      k := r + 1
      continue
    let start := k
    -- A modifier on a line of its own is a field of that name: a line break ends a member.
    while k < q && ((c.ts[k]!.kind == .ident && mods.contains c.ts[k]!.text) || c.ts[k]!.is "*") &&
        (c.ts[k + 1]?.any fun n => n.line == c.ts[k]!.line && !(n.is "(" || n.is "=" ||
          n.is ";" || n.is ":" || n.is "?" || n.is "!" || n.is "<" || n.is "}")) do
      k := k + 1
    let key := k
    let mut after ← keyEnd k
    while c.ts[after]?.any (fun n => n.is "?" || n.is "!") do after := after + 1
    let next := c.ts[after]?
    if next.any (fun n => n.is "(" || n.is "<") then
      match ← method start key (if c.ts[after - 1]!.is "?" || c.ts[after - 1]!.is "!" then
          after - 1 else after) with
      | some r => k := r
      | none =>
        -- A signature: up to its `;` or line end.
        let mut j := after
        while j < q && !c.ts[j]!.is ";" && !(j > after && (← lineEnds after j)) do
          if isOpen c.ts[j]! then j := c.m[j]! + 1 else j := j + 1
        k := j
      continue
    let mut j := after
    if next.any (·.is ":") then j := (← skipType (after + 1) q #["=", ";", "}"] true)
    if c.ts[j]?.any (·.is "=") then
      let v := j + 1
      let r ← expr v q #[";", "}"] true
      bind v r (← sourceText key (after - 1))
      j := r
    k := if j > start then j else start + 1

/-- `const`, `let` or `var` declarators from `i`, after the keyword. Returns where they end. -/
partial def declarators (i e : Nat) (extraStops : Array String := #[]) : P Nat := do
  let c ← read
  let mut k := i
  for _ in [0:e - i + 1] do
    if k ≥ e then break
    let t := c.ts[k]!
    let nameStart := k
    if t.is "{" then k := (← object k)
    else if t.is "[" then k := (← group k)
    else k := k + 1
    let nameEnd := k
    if c.ts[k]?.any (·.is "!") then k := k + 1
    if c.ts[k]?.any (·.is ":") then
      k := (← skipType (k + 1) e (#["=", ",", ";"] ++ extraStops) true)
    if c.ts[k]?.any (·.is "=") then
      let v := k + 1
      let r ← expr v e (#[",", ";"] ++ extraStops) true
      bind v r (← sourceText nameStart (nameEnd - 1))
      k := r
    if c.ts[k]?.any (·.is ",") then k := k + 1 else break
  return k

/-- The statements from `i` to `e`. -/
partial def statements (i e : Nat) : P Unit := do
  let mut k := i
  while k < e do
    let r ← statement k e
    k := if r > k then r else k + 1

/-- The body of a `switch`, at its `{`. -/
partial def switchBody (b : Nat) : P Unit := do
  let c ← read
  let q := c.m[b]!
  let mut k := b + 1
  while k < q do
    let t := c.ts[k]!
    if t.isId "case" then
      bump k
      let r ← expr (k + 1) q #[":"] false
      k := r + 1
    else if t.isId "default" && (c.ts[k + 1]?.any (·.is ":")) then
      k := k + 2
    else
      let r ← statement k q
      k := if r > k then r else k + 1

/-- One statement at `i`. Returns the index after it. -/
partial def statement (i e : Nat) : P Nat := do
  let c ← read
  let t := c.ts[i]!
  let next := c.ts[i + 1]?
  let nextIs (s : String) := next.any (·.is s)
  if t.is ";" then return i + 1
  if t.is "{" && !t.jsx then
    let q := c.m[i]!
    statements (i + 1) q
    return q + 1
  if t.is "@" then return (← decorator i)
  if t.kind != .ident then
    let r ← expr i e #[";"] true
    return if c.ts[r]?.any (·.is ";") then r + 1 else r
  match t.text with
  | "if" | "while" | "for" | "with" =>
    if t.text != "with" then bump i
    let mut g := i + 1
    if next.any (·.isId "await") then g := g + 1
    if !(c.ts[g]?.any (·.is "(")) then return g
    let q := c.m[g]!
    if t.text == "for" then
      let mut k := g + 1
      if c.ts[k]?.any (fun u => u.isId "const" || u.isId "let" || u.isId "var") then
        k := (← declarators (k + 1) q #["of", "in"])
      while k < q do
        let r ← expr k q #[";"] false
        k := r + 1
    else
      let _ ← group g
    let r ← statement (q + 1) e
    if t.text == "if" && (c.ts[r]?.any (·.isId "else")) then return (← statement (r + 1) e)
    return r
  | "do" =>
    bump i
    let r ← statement (i + 1) e
    if c.ts[r]?.any (·.isId "while") then
      if c.ts[r + 1]?.any (·.is "(") then
        let after ← group (r + 1)
        return if c.ts[after]?.any (·.is ";") then after + 1 else after
    return r
  | "switch" =>
    if !nextIs "(" then return i + 1
    let after ← group (i + 1)
    if c.ts[after]?.any (·.is "{") then
      switchBody after
      return c.m[after]! + 1
    return after
  | "try" =>
    let mut k ← statement (i + 1) e
    while c.ts[k]?.any (·.isId "catch") do
      bump k
      k := k + 1
      if c.ts[k]?.any (·.is "(") then
        params k
        k := c.m[k]! + 1
      k := (← statement k e)
    if c.ts[k]?.any (·.isId "finally") then k := (← statement (k + 1) e)
    return k
  | "else" => statement (i + 1) e
  | "function" => function i
  | "async" =>
    if next.any (·.isId "function") then function i
    else
      let r ← expr i e #[";"] true
      return if c.ts[r]?.any (·.is ";") then r + 1 else r
  | "class" => classDecl i
  | "abstract" | "declare" | "export" | "default" =>
    if t.text == "export" && nextIs "default" then
      let k := i + 2
      let d := c.ts[k]?
      if d.any (fun u => u.isId "function" || u.isId "class" || u.isId "abstract" ||
          u.isId "interface") || (d.any (·.isId "async") && (c.ts[k + 1]?.any (·.isId "function"))) then
        return (← statement k e)
      let r ← expr k e #[";"] true
      return if c.ts[r]?.any (·.is ";") then r + 1 else r
    if t.text == "export" && (nextIs "{" || nextIs "*") then
      let mut k := i + 1
      if nextIs "{" then k := c.m[i + 1]! + 1 else k := k + 1
      while k < e && !c.ts[k]!.is ";" && !(← lineEnds i k) do k := k + 1
      return k
    if t.text == "default" && nextIs ":" then return i + 2
    statement (i + 1) e
  | "const" | "let" | "var" =>
    if next.any (fun n => n.kind == .ident || n.is "{" || n.is "[") && !(nextIs "=") then
      if t.text == "const" && next.any (·.isId "enum") then return (← statement (i + 1) e)
      let r ← declarators (i + 1) e
      return if c.ts[r]?.any (·.is ";") then r + 1 else r
    let r ← expr i e #[";"] true
    return if c.ts[r]?.any (·.is ";") then r + 1 else r
  | "interface" | "enum" =>
    if next.any (·.kind == .ident) && c.typescript then
      let mut k := i + 1
      while k < e && !c.ts[k]!.is "{" do
        if c.ts[k]!.is "(" || c.ts[k]!.is "[" then k := c.m[k]! + 1 else k := k + 1
      return if k < e then c.m[k]! + 1 else k
    let r ← expr i e #[";"] true
    return if c.ts[r]?.any (·.is ";") then r + 1 else r
  | "type" =>
    if c.typescript && next.any (·.kind == .ident) &&
        (c.ts[i + 2]?.any (fun n => n.is "=" || n.is "<")) then
      let mut k := i + 2
      if c.ts[k]!.is "<" then k := (← skipAngles k e)
      if c.ts[k]?.any (·.is "=") then k := (← skipType (k + 1) e #[";", "}"] true)
      return if c.ts[k]?.any (·.is ";") then k + 1 else k
    let r ← expr i e #[";"] true
    return if c.ts[r]?.any (·.is ";") then r + 1 else r
  | "namespace" | "module" | "global" =>
    if c.typescript && next.any (fun n => n.kind == .ident || n.kind == .str || n.is "{") &&
        !(nextIs "=") && !(nextIs ".") && !(nextIs "(") then
      let mut k := i + 1
      while k < e && !c.ts[k]!.is "{" && !c.ts[k]!.is ";" do k := k + 1
      if c.ts[k]?.any (·.is "{") then
        statements (k + 1) c.m[k]!
        return c.m[k]! + 1
      return k
    let r ← expr i e #[";"] true
    return if c.ts[r]?.any (·.is ";") then r + 1 else r
  | "import" =>
    if nextIs "(" || nextIs "." then
      let r ← expr i e #[";"] true
      return if c.ts[r]?.any (·.is ";") then r + 1 else r
    let mut k := i + 1
    while k < e && !c.ts[k]!.is ";" && !(← lineEnds i k) do
      if isOpen c.ts[k]! then k := c.m[k]! + 1 else k := k + 1
    return k
  | "return" | "throw" =>
    if next.any (fun n => n.first && !n.jsx) then return i + 1
    let r ← expr (i + 1) e #[";"] true
    return if c.ts[r]?.any (·.is ";") then r + 1 else r
  | "break" | "continue" =>
    let mut k := i + 1
    if next.any (fun n => n.kind == .ident && !n.first) then k := k + 1
    return if c.ts[k]?.any (·.is ";") then k + 1 else k
  | "case" => return i + 1
  | _ =>
    -- A label: `outer: for …`.
    if nextIs ":" then return i + 2
    let r ← expr i e #[";"] true
    return if c.ts[r]?.any (·.is ";") then r + 1 else r

end

/-- The functions of a JavaScript or TypeScript file. `typescript` reads types; `jsx` reads JSX. -/
def functions (s : ByteArray) (typescript jsx : Bool) : Array Function := Id.run do
  let ts := tokens .js s jsx
  if ts.isEmpty then return #[]
  let m := matching ts
  let ctx : Ctx := { ts, m, src := s, typescript }
  let ((), st) := (statements 0 ts.size).run ctx |>.run { weight := Array.replicate ts.size 0, found := #[] }
  let found := st.found
  let mut scored := #[]
  for h : n in [0:found.size] do
    let mut total : Int := 1
    for (lo, hi) in ownTokens found n do
      for i in [lo:hi] do total := total + st.weight[i]!
    scored := scored.push { found[n] with complexity := total }
  return treeOrder ts scored

end Clocrap.JsLang
