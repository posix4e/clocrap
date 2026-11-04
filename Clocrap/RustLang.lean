import Clocrap.Function
import Clocrap.Lex

/-!
# Rust

Functions are `fn` items with a body, found from tokens. Macro invocations and attributes are
opaque token trees, as they are to a parser: a `fn` or an `&&` inside `quote! { … }` or
`assert!(…)` is not code.

Decisions are `if` (not a match guard's), `while`, `for`, `loop`, each match arm less one per
`match`, and the binary `&&` and `||`, except the `&&`s that chain `let`s in a condition.
-/

namespace Clocrap.RustLang

open Lex

/-- Names after which `&&` and `||` start an operand rather than join two. -/
def prefixWords : Array String := #[
  "return", "break", "continue", "in", "match", "if", "while", "else", "let", "mut", "move",
  "yield", "box", "dyn", "impl", "as", "for", "loop", "unsafe", "async", "ref", "where", "const",
  "static", "type", "fn", "pub", "use", "mod", "struct", "enum", "trait"]

def modifiers : Array String := #["const", "async", "unsafe", "extern", "default", "pub", "safe"]

/-- Whether a token ends an operand, so `&&` after it is binary. -/
def endsOperand (t : Tok) : Bool :=
  match t.kind with
  | .num | .str => true
  | .ident => !t.text.startsWith "'" && !prefixWords.contains t.text
  | .punct => t.text == ")" || t.text == "]" || t.text == "}" || t.text == "?"

/-- The tokens inside macro invocations and attributes. -/
def opaqueTokens (ts : Array Tok) (m : Array Nat) : Array Bool := Id.run do
  let mut out := Array.replicate ts.size false
  let mut i := 0
  while i < ts.size do
    let t := ts[i]!
    let next (k : Nat) := ts[i + k]?.map (·.text) |>.getD ""
    let isOpen (s : String) := s == "(" || s == "[" || s == "{"
    let tree : Option Nat :=
      if t.kind == .ident && !prefixWords.contains t.text && next 1 == "!" && isOpen (next 2) then
        some (i + 2)
      else if t.isId "macro_rules" && next 1 == "!" && isOpen (next 3) then some (i + 3)
      else if t.is "#" && next 1 == "[" then some (i + 1)
      else if t.is "#" && next 1 == "!" && next 2 == "[" then some (i + 2)
      else none
    match tree with
    | some o =>
      for k in [o:m[o]! + 1] do out := out.set! k true
      i := m[o]! + 1
    | none => i := i + 1
  return out

/-- The first `{` or `;` from `i` at this level, stepping over `(…)` and `[…]`. -/
def blockOrEnd (ts : Array Tok) (m : Array Nat) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  while j < ts.size do
    let t := ts[j]!
    if t.is "{" || t.is ";" then return some j
    if t.is "(" || t.is "[" then j := m[j]! + 1 else j := j + 1
  return none

/-- The first `{` from `i` at this level, stepping over `(…)` and `[…]`: a condition's or a
scrutinee's block, since neither may hold a struct literal. -/
def blockAfter (ts : Array Tok) (m : Array Nat) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  while j < ts.size do
    let t := ts[j]!
    if t.is "{" then return some j
    if t.is ";" then return none
    if t.is "(" || t.is "[" then j := m[j]! + 1 else j := j + 1
  return none

structure Marks where
  /-- `if`s that are match guards. -/
  guards : Array Bool
  /-- `&&`s that chain `let`s. -/
  chains : Array Bool
  /-- Arms of the `match` at each index. -/
  arms : Array Nat

def mark (ts : Array Tok) (m : Array Nat) (hidden : Array Bool) : Marks := Id.run do
  let mut guards := Array.replicate ts.size false
  let mut chains := Array.replicate ts.size false
  let mut arms := Array.replicate ts.size 0
  for h : i in [0:ts.size] do
    let t := ts[i]
    if hidden[i]! || t.kind != .ident then continue
    if t.text == "if" || t.text == "while" then
      let some b := blockAfter ts m (i + 1) | continue
      let mut j := i + 1
      -- `a && b && let p = x && c` is `((a && b) && let p = x) && c`: the `&&` just before the
      -- first `let`, and every one after it, chain; the ones before are operators.
      let mut hasLet := false
      let mut lastAnd : Option Nat := none
      while j < b do
        if ts[j]!.isId "let" && !hasLet then
          hasLet := true
          if let some a := lastAnd then chains := chains.set! a true
        if ts[j]!.is "&&" then
          if hasLet then chains := chains.set! j true
          lastAnd := some j
        if ts[j]!.is "(" || ts[j]!.is "[" then j := m[j]! + 1 else j := j + 1
    else if t.text == "match" then
      let some b := blockAfter ts m (i + 1) | continue
      let close := m[b]!
      let mut j := b + 1
      let mut inPattern := true
      let mut count := 0
      while j < close do
        let u := ts[j]!
        if inPattern then
          if u.isId "if" then guards := guards.set! j true
          if u.is "=>" then
            inPattern := false
            count := count + 1
          if u.is "(" || u.is "[" || u.is "{" then j := m[j]! + 1 else j := j + 1
        else
          if u.is "," then
            inPattern := true
            j := j + 1
          else if u.is "{" then
            j := m[j]! + 1
            -- A block-like arm needs no comma: the next arm starts unless the expression goes on.
            let next := ts[j]?
            let goesOn := next.any fun n => n.is "," || n.is "." || n.is "?" || n.isId "else" ||
              n.isId "as" || (n.kind == .punct && !(n.is "|") && !(n.is "(") && !(n.is "[") &&
                !(n.is "&") && !(n.is "_") && !(n.is "-") && !(n.is "::") && !(n.is "#"))
            if !goesOn then inPattern := true
          else if u.is "(" || u.is "[" then j := m[j]! + 1
          else j := j + 1
      arms := arms.set! i count
  return { guards, chains, arms }

/-- Whether the `for` at `i` is a loop, not `for<'a>` or `impl … for …`. -/
def isLoop (ts : Array Tok) (m : Array Nat) (i : Nat) : Bool := Id.run do
  if (ts[i + 1]?.any (·.is "<")) then return false
  let some b := blockAfter ts m (i + 1) | return false
  let mut j := i + 1
  while j < b do
    if ts[j]!.isId "in" then return true
    if ts[j]!.is "(" || ts[j]!.is "[" then j := m[j]! + 1 else j := j + 1
  return false

def functions (s : ByteArray) : Array Function := Id.run do
  let ts := tokens .rust s
  if ts.isEmpty then return #[]
  let m := matching ts
  let o := openers m
  let hidden := opaqueTokens ts m
  let marks := mark ts m hidden
  let mut found : Array Found := #[]
  for h : k in [0:ts.size] do
    if hidden[k]! || !ts[k].isId "fn" then continue
    let some name := ts[k + 1]? | continue
    if name.kind != .ident then continue
    let some b := blockOrEnd ts m (k + 2) | continue
    if !ts[b]!.is "{" then continue
    -- Visibility and modifiers belong to the item.
    let mut first := k
    let mut go := true
    while go && first > 0 do
      let p := ts[first - 1]!
      if p.kind == .ident && modifiers.contains p.text then first := first - 1
      else if p.kind == .str && first ≥ 2 && ts[first - 2]!.isId "extern" then first := first - 1
      else if p.is ")" && o[first - 1]! ≥ 1 && ts[o[first - 1]! - 1]!.isId "pub" then
        first := o[first - 1]! - 1
      else go := false
    found := found.push { name := name.text, first, last := m[b]!, complexity := 0 }
  let mut scored := #[]
  for h : n in [0:found.size] do
    let mut total : Int := 1
    for (lo, hi) in ownTokens found n do
      for i in [lo:hi] do
        if hidden[i]! then continue
        let t := ts[i]!
        match t.kind with
        | .ident =>
          match t.text with
          | "if" => if !marks.guards[i]! then total := total + 1
          | "while" | "loop" => total := total + 1
          | "for" => if isLoop ts m i then total := total + 1
          | "match" => total := total - 1 + marks.arms[i]!
          | _ => pure ()
        | .punct =>
          if (t.text == "&&" || t.text == "||") && i > 0 && endsOperand ts[i - 1]! &&
              !marks.chains[i]! then
            total := total + 1
        | _ => pure ()
    scored := scored.push { found[n] with complexity := total }
  return treeOrder ts scored

end Clocrap.RustLang
