import Clocrap.Str
import Clocrap.Bytes
import Clocrap.Count
import Clocrap.Function

/-!
# Lean

Functions in Lean 4 source, found from tokens rather than a grammar.

Lean's syntax is extensible (notation, macros, do-notation), so a fixed grammar misreads real
files. The shape clocrap needs is regular, though:

- A declaration is a command. It starts with attributes, modifiers or a keyword as the first token
  of a line, at column 0 or at the column of the first declaration inside a `mutual` block, and
  runs until the next command.
- `def`, `abbrev`, `instance` and `opaque` declarations are functions. Theorems, lemmas and
  examples are proofs: the kernel checks them and they never run, so they are not scored. Nor are
  structures, inductives, classes, macros and syntax.
- Each helper in a definition's `where` block is a function of its own, named `outer.helper` as
  Lean names it. A `where` with no `:=` before it is structure-instance notation, and its fields
  belong to the definition.

A function's complexity is 1 plus one for each `if` (so each `else if`), `unless`, `for`, `while`,
`repeat`, `catch`, `&&`, `||`, `∧`, `∨`, `<|>` and `|`, less one for each `match`, each `fun` that
matches on alternatives, and a definition by pattern matching. So n arms add n − 1, and a `do`
block's `let some x := e | fallback` adds one. A `termination_by` or `decreasing_by` clause is a
proof, and adds nothing.
-/

namespace Clocrap.LeanLang

inductive Kind where
  | ident | symbol | literal
  deriving DecidableEq, Inhabited

structure Token where
  kind : Kind
  text : String
  line : Nat
  /-- The line the token ends on: a string can span lines. -/
  endLine : Nat
  column : Nat
  firstOnLine : Bool
  deriving Inhabited

def Token.is (t : Token) (s : String) : Bool := t.kind != .literal && t.text == s

/-- Symbols longer than one character that the analysis needs to tell apart. Longest first, so
`<|>` is not read as `<|` and `>`. -/
def symbols : Array ByteArray :=
  #["<|>", "|||", "&&&", "|>.", "&&", "||", "|>", "<|", ":=", "=>", "@["].map String.toUTF8

/-- Lean's `isLetterLike`: Greek but λ, Π and Σ, Coptic, extended Greek, the letter-like symbols
block and the mathematical alphabets. -/
def isLetterLike (v : UInt32) : Bool :=
  (0x3b1 ≤ v && v ≤ 0x3c9 && v != 0x3bb) || (0x391 ≤ v && v ≤ 0x3a9 && v != 0x3a0 && v != 0x3a3) ||
    (0x3ca ≤ v && v ≤ 0x3fb) || (0x1f00 ≤ v && v ≤ 0x1ffe) || (0x2100 ≤ v && v ≤ 0x214f) ||
    (0x1d49c ≤ v && v ≤ 0x1d59f)

def isSubscript (v : UInt32) : Bool :=
  (0x2080 ≤ v && v ≤ 0x2089) || (0x2090 ≤ v && v ≤ 0x209c) || (0x1d62 ≤ v && v ≤ 0x1d6a)

def isIdStart (v : UInt32) : Bool :=
  (v < 128 && (isAlpha v.toUInt8 || v == 95)) || isLetterLike v

def isIdRest (v : UInt32) : Bool :=
  (v < 128 && (isAlnum v.toUInt8 || v == 95 || v == 39 || v == 33 || v == 63)) ||
    isLetterLike v || isSubscript v

/-- `«` and `»` as UTF-8. -/
def guilOpen : ByteArray := "«".toUTF8
def guilClose : ByteArray := "»".toUTF8

/-- The lexer's position. -/
structure Pos where
  i : Nat := 0
  line : Nat := 1
  lineStart : Nat := 0
  hasTok : Bool := false

/-- Steps over one byte, keeping track of lines. -/
@[inline] def bump (s : ByteArray) (p : Pos) : Pos :=
  if byteAt s p.i == 10 then { i := p.i + 1, line := p.line + 1, lineStart := p.i + 1, hasTok := false }
  else { p with i := p.i + 1 }

partial def skipBlockComment (s : ByteArray) (p : Pos) : Pos :=
  let rec go (p : Pos) (depth : Nat) : Pos :=
    if p.i ≥ s.size then p
    else if hasAt s p.i "/-".toUTF8 then go { p with i := p.i + 2 } (depth + 1)
    else if hasAt s p.i "-/".toUTF8 then
      let p := { p with i := p.i + 2 }
      if depth ≤ 1 then p else go p (depth - 1)
    else go (bump s p) depth
  go p 0

/-- Skips a string body up to and including its closing quote. In an interpolated string, `{…}`
holds code, which may hold strings itself. -/
partial def skipString (s : ByteArray) (p : Pos) (interpolated : Bool) : Pos :=
  let rec go (p : Pos) (depth : Nat) : Pos :=
    if p.i ≥ s.size then p
    else
      let b := byteAt s p.i
      if b == 92 && depth == 0 then
        let p := { p with i := p.i + 1 }
        go (if p.i < s.size then bump s p else p) depth
      else if b == 34 && depth == 0 then { p with i := p.i + 1 }
      else if b == 34 then go (skipString s { p with i := p.i + 1 } false) depth
      else if b == 123 && interpolated then go { p with i := p.i + 1 } (depth + 1)
      else if b == 125 && interpolated && depth > 0 then go { p with i := p.i + 1 } (depth - 1)
      else go (bump s p) depth
  go p 0

/-- `r"…"` or `r#"…"#`, with any number of `#`. Returns `none`, consuming nothing, when the `r`
starts a name instead. -/
partial def skipRawString (s : ByteArray) (p : Pos) : Option Pos := Id.run do
  let mut hashes := 0
  while byteAt s (p.i + 1 + hashes) == 35 do hashes := hashes + 1
  if p.i + 1 + hashes ≥ s.size || byteAt s (p.i + 1 + hashes) != 34 then return none
  let close := ByteArray.mk (#[34] ++ Array.replicate hashes 35)
  let mut q := { p with i := p.i + hashes + 2 }
  while q.i < s.size do
    if hasAt s q.i close then return some { q with i := q.i + close.size }
    q := bump s q
  return some q

/-- `'a'`, `'\n'`, `'\x41'`, `'\u{1F600}'`. A prime that ends a name is part of the name, so it
never gets here. -/
def skipCharLiteral (s : ByteArray) (p : Pos) : Option Pos := Id.run do
  if byteAt s (p.i + 1) == 92 && p.i + 1 < s.size then
    let upto := min s.size (p.i + 14)
    for k in [p.i + 3:upto] do
      if byteAt s k == 39 then return some { p with i := k + 1 }
    return none
  if p.i + 1 ≥ s.size then return none
  let (c, len) := decodeAt s (p.i + 1)
  if c != 39 && c != 10 && byteAt s (p.i + 1 + len) == 39 && p.i + 1 + len < s.size then
    return some { p with i := p.i + len + 2 }
  return none

/-- A name: components joined by dots, each plain or in `«»`. -/
partial def skipIdent (s : ByteArray) (p : Pos) : Pos :=
  let rec component (i : Nat) : Nat :=
    if hasAt s i guilOpen then
      let rec find (k : Nat) : Nat :=
        if k ≥ s.size then s.size
        else if hasAt s k guilClose then k + guilClose.size
        else find (k + 1)
      find i
    else
      let rec rest (k : Nat) : Nat :=
        if k ≥ s.size then k
        else
          let (c, len) := decodeAt s k
          if isIdRest c then rest (k + len) else k
      rest i
  let rec go (i : Nat) : Nat :=
    let j := component i
    let continues := byteAt s j == 46 && j + 1 < s.size &&
      (let (c, _) := decodeAt s (j + 1); isIdStart c || hasAt s (j + 1) guilOpen)
    if continues then go (j + 1) else j
  { p with i := go p.i }

/-- Reads one token starting at a non-blank, non-comment byte. -/
def token (s : ByteArray) (p : Pos) : Kind × Pos :=
  let b := byteAt s p.i
  if b == 34 then (.literal, skipString s { p with i := p.i + 1 } false)
  else match (if b == 114 then skipRawString s p else none) with
  | some q => (.literal, q)
  | none =>
  match (if b == 39 then skipCharLiteral s p else none) with
  | some q => (.literal, q)
  | none =>
  if isDigit b then
    let num := Id.run do
      let mut k := p.i
      while k < s.size && (let c := byteAt s k
          isAlnum c || c == 95 || (c == 46 && k + 1 < s.size && isDigit (byteAt s (k + 1)))) do
        k := k + 1
      return k
    (.literal, { p with i := num })
  else
    let (c, len) := decodeAt s p.i
    if isIdStart c || hasAt s p.i guilOpen then
      let q := skipIdent s p
      -- `s!"…{x}…"`, `m!"…"`, `f!"…"`: an interpolated string.
      if byteAt s (q.i - 1) == 33 && byteAt s q.i == 34 && q.i < s.size then
        (.literal, skipString s { q with i := q.i + 1 } true)
      else (.ident, q)
    else
      match symbols.find? (hasAt s p.i ·) with
      | some sym => (.symbol, { p with i := p.i + sym.size })
      | none => (.symbol, { p with i := p.i + len })

/-- Every token of a UTF-8 Lean source. -/
partial def tokens (s : ByteArray) : Array Token := Id.run do
  let mut out := #[]
  let mut p : Pos := {}
  while p.i < s.size do
    let b := byteAt s p.i
    if isWs b then
      p := bump s p
      continue
    if hasAt s p.i "--".toUTF8 then
      while p.i < s.size && byteAt s p.i != 10 do p := { p with i := p.i + 1 }
      continue
    if hasAt s p.i "/-".toUTF8 then
      p := skipBlockComment s p
      continue
    let start := p.i
    let line := p.line
    let column := p.i - p.lineStart
    let first := !p.hasTok
    let (kind, q) := token s p
    -- A token always moves the lexer on.
    let q := if q.i ≤ p.i then { q with i := p.i + 1 } else q
    p := { q with hasTok := true }
    out := out.push { kind, text := textOf s start p.i, line, endLine := p.line, column, firstOnLine := first }
  return out

/-- The kind of every line of a Lean source file, from its tokens: a line a token touches is code
(a string that spans lines makes each of its lines code), and any other line that is not blank
holds only comment text. This reads interpolated strings such as `s!"{f "x"}"` right, which a
quote-matching classifier cannot. `none` for a file that is not UTF-8. -/
def lineKinds (s : ByteArray) : Option (Array LineKind) := do
  let _ ← String.fromUTF8? s
  let ranges := lineRanges s
  let mut code := Array.replicate ranges.size false
  for t in tokens s do
    for line in [t.line:t.endLine + 1] do
      if line ≥ 1 && line - 1 < code.size then code := code.set! (line - 1) true
  return (ranges.zip code).map fun ((a, b), c) =>
    if allWs s a b then .blank else if c then .code else .comment

/-- Words that start a command when they open a line at the command column. -/
def commands : Array String := #[
  "def", "theorem", "lemma", "abbrev", "instance", "example", "opaque", "axiom", "structure",
  "inductive", "coinductive", "class", "namespace", "section", "end", "open", "variable",
  "universe", "set_option", "attribute", "export", "macro", "macro_rules", "syntax", "elab",
  "elab_rules", "notation", "infix", "infixl", "infixr", "prefix", "postfix",
  "declare_syntax_cat", "initialize", "builtin_initialize", "mutual", "deriving", "import",
  "module", "run_cmd", "run_elab", "run_meta", "add_decl_doc", "register_simp_attr",
  "register_option", "omit", "include", "@[", "#"]

/-- Modifiers that may come before a declaration keyword. -/
def modifiers : Array String := #[
  "private", "protected", "public", "noncomputable", "partial", "unsafe", "nonrec", "meta",
  "scoped", "local"]

def startsCommand (t : Token) : Bool :=
  t.kind != .literal && (commands.contains t.text || modifiers.contains t.text)

/-- The index of the `]` that closes the `@[` or `[` at `opener`. -/
def matchingBracket (ts : Array Token) (opener : Nat) : Nat := Id.run do
  let mut depth : Int := 0
  for i in [opener:ts.size] do
    let t := ts[i]!
    if t.is "@[" || t.is "[" then depth := depth + 1
    else if t.is "]" then
      depth := depth - 1
      if depth == 0 then return i
  return ts.size

/-- The index of the command's keyword, after its attributes and modifiers, and whether it is
`private`. -/
def header (ts : Array Token) : Bool × Option Nat := Id.run do
  let mut priv := false
  let mut i := 0
  for _ in [0:ts.size + 1] do
    if i ≥ ts.size then break
    let t := ts[i]!
    if t.is "@[" then i := matchingBracket ts i + 1
    else if modifiers.contains t.text && t.kind == .ident then
      priv := priv || t.text == "private"
      i := i + 1
    else return (priv, some i)
  return (priv, none)

def opens (t : Token) : Bool :=
  t.kind == .symbol && #["(", "[", "{", "⟨", "@[", "⦃"].contains t.text

def closes (t : Token) : Bool :=
  t.kind == .symbol && #[")", "]", "}", "⟩", "⦄"].contains t.text

/-- The index of the first token at bracket depth 0 that is one of `texts`. -/
def firstAtTop (ts : Array Token) (texts : Array String) : Option Nat := Id.run do
  let mut depth : Int := 0
  for h : i in [0:ts.size] do
    let t := ts[i]
    if depth == 0 && t.kind != .literal && texts.contains t.text then return some i
    if opens t then depth := depth + 1
    else if closes t then depth := depth - 1
  return none

/-- The components of a dotted name, with `«»` removed. -/
def components (name : String) : Array String := Id.run do
  let mut parts := #[]
  let mut current := ""
  let mut quoted := false
  for c in name.toList do
    if c == '«' then quoted := true
    else if c == '»' then quoted := false
    else if c == '.' && !quoted then
      parts := parts.push current
      current := ""
    else current := current.push c
  return parts.push current

/-- The full name of a declaration written as `written` inside `scope`. -/
def qualified (scope : Array String) (written : String) : String :=
  if written.startsWith "_root_." then written.dropS 7
  else
    -- A component with a dot in it keeps its `«»`, so it stays one component.
    let parts := (scope ++ components written).map fun p => if p.contains '.' then s!"«{p}»" else p
    ".".intercalate parts.toList

/-- The name Lean gives an instance that has none: `inst` and the type's constants, as
`instance : ToJson Foo` becomes `instToJsonFoo`. Only the capitalised names count, since
lower-case ones are usually variables. -/
def anonymousInstance (ts : Array Token) (scope : Array String) : String × String :=
  let ty := match firstAtTop ts #[":"] with
    | some i => ts.extract (i + 1) ts.size
    | none => #[]
  let ty := ty.extract 0 ((firstAtTop ty #[":=", "where", "|"]).getD ty.size)
  let generated := ty.foldl (init := "inst") fun acc t =>
    if t.kind != .ident then acc
    else
      let last := (components t.text).back!
      if last.front.isUpper && last.front.toNat < 128 && !last.isEmpty then acc ++ last else acc
  let shown := " ".intercalate (ty.map (·.text)).toList
  let shown := shown.replace "( " "(" |>.replace " )" ")" |>.replace "[ " "[" |>.replace " ]" "]"
  let name := s!"instance {shown}"
  let name := if name.length > 48 then name.takeS 47 ++ "…" else name
  (name, qualified scope generated)

/-- 1 plus the decision points in `ts`, before any proof clause. -/
def complexity (ts : Array Token) : Int := Id.run do
  let mut total : Int := 1
  for h : i in [0:ts.size] do
    let t := ts[i]
    if t.kind == .literal then continue
    match t.text with
    | "termination_by" | "decreasing_by" => break
    | "if" | "unless" | "for" | "while" | "repeat" | "catch" =>
      if t.kind == .ident then total := total + 1
    | "&&" | "||" | "∧" | "∨" | "<|>" | "|" =>
      if t.kind == .symbol then total := total + 1
    | "match" => if t.kind == .ident then total := total - 1
    | "fun" | "λ" => if (ts[i + 1]?.map (·.is "|")).getD false then total := total - 1
    | _ => pure ()
  return total

/-- Attributes that let the compiler copy a declaration's body into its callers. -/
def inlineAttributes : Array String := #["inline", "macro_inline", "always_inline", "specialize"]

/-- Words that make a body more than one application of names. -/
def bodyKeywords : Array String := #[
  "do", "fun", "λ", "let", "have", "show", "if", "then", "else", "match", "with", "return", "for",
  "while", "unless", "try", "catch", "by", "termination_by", "decreasing_by"]

/-- Whether the declaration whose keyword is at `keyword` in `ts` may be inlined into its callers:
it has one of `inlineAttributes`, is an `abbrev`, or its body after `:=` is names and literals only,
as `def u8 : Reader UInt8 := ByteReader.readUInt8` or `def f (n : Nat) := g n 1`. Lean inlines a
body that small wherever it is used. -/
def inlinable (ts : Array Token) (keyword : Nat) : Bool := Id.run do
  let attributes := ts.extract 0 keyword
  if attributes.any fun t => t.kind == .ident && inlineAttributes.contains t.text then return true
  if (ts[keyword]?.map (·.is "abbrev")).getD false then return true
  let signature := ts.extract (keyword + 1) ts.size
  let some i := firstAtTop signature #[":=", "|"] | return false
  if !signature[i]!.is ":=" then return false
  let body := signature.extract (i + 1) signature.size
  return !body.isEmpty && body.all fun t =>
    t.kind == .literal || (t.kind == .ident && !bodyKeywords.contains t.text)

def function (name : String) (ts : Array Token) (equations : Bool) (symbol : String)
    (priv : Bool) (inline : Bool) : Function :=
  let startLine := (ts[0]?.map (·.line)).getD 1
  let endLine := ts.foldl (init := startLine) fun m t => max m t.endLine
  let c := complexity ts - (if equations then 1 else 0)
  { name, startLine, endLine, complexity := (max c 1).toNat, symbol := some ⟨symbol, priv, inline⟩ }

/-- The helpers in a `where` block: each starts at the column of the first. -/
def helpers (ts : Array Token) (outer outerSymbol : String) (priv : Bool) : Array Function :=
  Id.run do
  let some first := ts[0]? | return #[]
  let column := first.column
  -- A helper's own `termination_by` may sit at the helpers' column.
  let mut starts := #[]
  for h : i in [0:ts.size] do
    let t := ts[i]
    if i == 0 || (t.firstOnLine && t.column == column && !t.is "|" && !t.is "termination_by" &&
        !t.is "decreasing_by" && !closes t) then
      starts := starts.push i
  let mut out := #[]
  for h : n in [0:starts.size] do
    let start := starts[n]
    let stop := starts[n + 1]?.getD ts.size
    let helper := ts.extract start stop
    let (_, some at_) := header helper | continue
    let t := helper[at_]!
    if t.kind != .ident then continue
    let rest := helper.extract (at_ + 1) helper.size
    let equations := (firstAtTop rest #[":=", "|"]).any fun i => rest[i]!.is "|"
    out := out.push (function s!"{outer}.{t.text}" helper equations s!"{outerSymbol}.{t.text}" priv
      (inlinable helper at_))
  return out

/-- A `def`, `abbrev`, `opaque` or `instance`, with its `where` helpers. -/
def declaration (cmd : Array Token) (keyword : Nat) (priv : Bool) (scope : Array String) :
    Array Function := Id.run do
  let kw := cmd[keyword]!.text
  let mut after := keyword + 1
  -- `instance (priority := low) name : …`
  if kw == "instance" && (cmd[after]?.map (·.is "(")).getD false &&
      (cmd[after + 1]?.map (·.is "priority")).getD false then
    let mut depth : Int := 0
    for _ in [0:cmd.size] do
      if after ≥ cmd.size then break
      let t := cmd[after]!
      if opens t then depth := depth + 1
      else if closes t then
        depth := depth - 1
        if depth == 0 then
          after := after + 1
          break
      after := after + 1
  let named := cmd[after]?.filter (·.kind == .ident)
  let (name, symbolName) ← match named with
    | some t => pure (t.text, qualified scope t.text)
    | none =>
      if kw == "instance" then pure (anonymousInstance (cmd.extract after cmd.size) scope)
      else return #[]
  let body := cmd.extract after cmd.size
  -- `opaque f : T` with no body has no code of its own.
  if kw == "opaque" && (firstAtTop body #[":="]).isNone then return #[]
  -- Helpers follow a `where` that comes after the body. A `where` with no `:=` or `|` before it
  -- is structure-instance notation, part of the body.
  let split : Option Nat :=
    if kw == "instance" then none
    else match firstAtTop body #[":=", "|", "where"] with
      | some i => if body[i]!.is "where" then none else firstAtTop body #["where"]
      | none => none
  let own := cmd.extract 0 (after + split.getD body.size)
  let equations := (firstAtTop body #[":=", "|", "where"]).any fun i => body[i]!.is "|"
  let mut out := #[function name own equations symbolName priv (inlinable own keyword)]
  if let some sp := split then
    out := out ++ helpers (body.extract (sp + 1) body.size) name symbolName priv
  return out

/-- The functions in a Lean source file, in source order. A file that is not UTF-8 has none. -/
def functions (s : ByteArray) : Array Function := Id.run do
  if (String.fromUTF8? s).isNone then return #[]
  let ts := tokens s
  let mut found := #[]
  let mut namespaces : Array (Array String) := #[]
  -- `some none` inside a `mutual` block before its first declaration.
  let mut mutualColumn : Option (Option Nat) := none
  let mut starts : Array Nat := #[]
  for h : index in [0:ts.size] do
    let t := ts[index]
    if !t.firstOnLine || !startsCommand t then continue
    let mut atColumn := false
    match mutualColumn with
    | some (some column) => atColumn := t.column == 0 || t.column == column
    | some none =>
      mutualColumn := some (some t.column)
      atColumn := true
    | none => atColumn := t.column == 0
    if !atColumn then continue
    -- Attributes or modifiers on lines of their own belong to the declaration that follows them.
    let pending := match starts.back? with
      | some last => (header (ts.extract last index)).2.isNone
      | none => false
    if !pending then starts := starts.push index
    -- A `mutual` block's own column is fixed by its first declaration.
    if t.is "mutual" then mutualColumn := some none
    else if t.is "end" && t.column == 0 then mutualColumn := none
  let mut inMutual := false
  for h : n in [0:starts.size] do
    let start := starts[n]
    let stop := starts[n + 1]?.getD ts.size
    let cmd := ts.extract start stop
    let (priv, some keyword) := header cmd | continue
    let rest := cmd.extract (keyword + 1) cmd.size
    match cmd[keyword]!.text with
    | "namespace" => if let some name := rest[0]? then namespaces := namespaces.push (components name.text)
    | "section" => namespaces := namespaces.push #[]
    | "mutual" => inMutual := true
    | "end" => if inMutual then inMutual := false else namespaces := namespaces.pop
    | "def" | "abbrev" | "opaque" | "instance" =>
      let scope := namespaces.foldl (· ++ ·) #[]
      found := found ++ declaration cmd keyword priv scope
    | _ => pure ()
  return (found.toList.mergeSort fun a b =>
    a.startLine < b.startLine || (a.startLine == b.startLine && a.endLine ≤ b.endLine)).toArray

/-- Lowercase hex of `v`, padded to `width` digits. -/
def hex (v : Nat) (width : Nat) : String :=
  let digits := Nat.toDigits 16 v
  String.ofList (List.replicate (width - digits.length) '0' ++ digits)

/-- Lean's mangling of a name into a C identifier: components joined by `_`, `_` doubled, and any
other character that is not an ASCII letter or digit written as `_xHH`, `_uHHHH` or `_UHHHHHHHH`,
with `00` before a component that starts with one. -/
def mangle (name : String) : String := Id.run do
  let mut out := ""
  let parts := components name
  for h : n in [0:parts.size] do
    let part := parts[n]
    if n > 0 then out := out.push '_'
    let alnum (c : Char) := c.toNat < 128 && (c.isAlphanum)
    if let some c := part.toList.head? then
      if !alnum c && c != '_' then out := out ++ "00"
    for c in part.toList do
      let v := c.toNat
      if alnum c then out := out.push c
      else if c == '_' then out := out ++ "__"
      else if v < 0x100 then out := out ++ "_x" ++ hex v 2
      else if v < 0x10000 then out := out ++ "_u" ++ hex v 4
      else out := out ++ "_U" ++ hex v 8
  return out

end Clocrap.LeanLang
