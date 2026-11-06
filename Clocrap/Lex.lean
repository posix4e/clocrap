import Clocrap.Bytes
import Clocrap.Function

/-!
# Tokens

One tokenizer for the languages whose functions clocrap finds from tokens (Lean has its own, in
`Clocrap.LeanLang`). It knows each family's comments, strings and the code inside strings:
template literals' `${…}` and Python's f-string `{…}` are code, so a decision inside one counts, as
it does in a parse. JavaScript's regular expression literals and JSX text are not
code, so a quote or an `if` inside them is not read as one.
-/

namespace Clocrap.Lex

inductive Family where
  | rust | js | python | c
  deriving DecidableEq, Inhabited

inductive Kind where
  | ident | punct | str | num
  deriving DecidableEq, Inhabited

structure Tok where
  kind : Kind
  /-- The text of a name, number or symbol. A string's text is empty: no rule reads it. -/
  text : String
  /-- Byte offsets of the token. -/
  start : Nat
  stop : Nat
  line : Nat := 0
  endLine : Nat := 0
  column : Nat := 0
  /-- Whether no other token starts before it on its line. -/
  first : Bool := false
  /-- A brace that opens or closes code inside JSX, not an object or a block. -/
  jsx : Bool := false
  deriving Inhabited

def Tok.is (t : Tok) (s : String) : Bool := t.kind != .str && t.text == s

/-- Whether the token is the name `s` (not a symbol or string that happens to read the same). -/
def Tok.isId (t : Tok) (s : String) : Bool := t.kind == .ident && t.text == s

/-- Multi-character symbols, longest first. -/
def symbols : Array ByteArray := #[
  ">>>=", "...", "..=", "===", "!==", "<<=", ">>=", "**=", "&&=", "||=", "??=", "=>", "->", "::",
  "==", "!=", "<=", ">=", "&&", "||", "??", "?.", "++", "--", "+=", "-=", "*=", "/=", "%=",
  "&=", "|=", "^=", "<<", "..", "**"].map String.toUTF8

/-- How a string ends, and what may interrupt it. -/
structure StrKind where
  close : ByteArray
  escapes : Bool := true
  /-- The byte sequence that starts code inside the string: `${`, `\(`, `{`. Empty for none. -/
  interp : ByteArray := .empty
  /-- Whether a doubled `{{` is a literal brace (Python's f-strings). -/
  doubledBrace : Bool := false
  multiline : Bool := true
  /-- A raw string's backslash escapes only a quote or another backslash, so `\{` in an
  `rf"…"` is a backslash and then a brace. -/
  raw : Bool := false
  deriving Inhabited

/-- What an open bracket on the lexer's stack is. A string's code part ends at the bracket that
closes it, and the string goes on. -/
inductive Frame where
  | bracket (b : UInt8)
  | interp (k : StrKind)
  /-- `{` in JSX: code, then back to the element's children. -/
  | jsxExpr (base : Nat)
  /-- `{` in a JSX tag's attributes: code, then back to the tag. -/
  | jsxAttr (base : Nat)
  deriving Inhabited

/-- Words after which a `/` starts a regular expression, and a `<` a JSX element. -/
def exprKeywords : Array String := #[
  "return", "typeof", "case", "do", "else", "in", "of", "new", "delete", "void", "throw",
  "instanceof", "yield", "await", "default", "extends"]

structure State where
  i : Nat := 0
  out : Array Tok := #[]
  stack : Array Frame := #[]
  /-- Open JSX elements: each `true` while its children are being read. -/
  jsx : Nat := 0

def isIdByte (b : UInt8) : Bool := isWord b || b ≥ 0x80 || b == 36

/-- Whether the last token ends an expression, so a `/` divides and a `<` compares. -/
def afterOperand (out : Array Tok) : Bool :=
  match out.back? with
  | none => false
  | some t => match t.kind with
    | .num | .str => true
    | .ident => !exprKeywords.contains t.text
    | .punct => t.text == ")" || t.text == "]" || t.text == "}"

/-- The index just past a JavaScript regular expression starting at the `/` at `i`, or `none` when
it does not close on its line. -/
def regexEnd (s : ByteArray) (i : Nat) : Option Nat := Id.run do
  let mut k := i + 1
  let mut inClass := false
  while k < s.size do
    let b := byteAt s k
    if b == 10 then return none
    if b == 92 then k := k + 2; continue
    if b == 91 then inClass := true
    else if b == 93 then inClass := false
    else if b == 47 && !inClass then
      k := k + 1
      while k < s.size && isWord (byteAt s k) do k := k + 1
      return some k
    k := k + 1
  return none

/-- Reads a string body from `i`. Returns where it stopped and whether it stopped at code (the
interpolation opener has been consumed) rather than at the closing quote. -/
def stringBody (s : ByteArray) (k : StrKind) (i : Nat) : Nat × Bool := Id.run do
  let mut j := i
  while j < s.size do
    if !k.interp.isEmpty && hasAt s j k.interp then
      if k.doubledBrace && hasAt s (j + 1) k.interp then
        j := j + 2
        continue
      return (j + k.interp.size, true)
    if k.doubledBrace && byteAt s j == 125 && byteAt s (j + 1) == 125 then
      j := j + 2
      continue
    if k.escapes && byteAt s j == 92 then
      let n := byteAt s (j + 1)
      j := if k.raw && n != 92 && n != 34 && n != 39 then j + 1 else j + 2
      continue
    if hasAt s j k.close then return (j + k.close.size, false)
    if !k.multiline && byteAt s j == 10 then return (j, false)
    j := j + 1
  return (s.size, false)

/-- The string that starts at `i`, if one does: its kind and the length of its opener. -/
def stringAt (fam : Family) (s : ByteArray) (i : Nat) (prevWord : Bool) : Option (StrKind × Nat) :=
  Id.run do
  let b := byteAt s i
  match fam with
  | .rust =>
    -- `r"…"`, `r#"…"#`, `br"…"`, `b"…"`, `c"…"`; a name ending in r before a quote is not one.
    if prevWord then return none
    let mut j := i
    if b == 98 || b == 99 then j := j + 1
    if byteAt s j == 114 then
      let mut h := 0
      while byteAt s (j + 1 + h) == 35 do h := h + 1
      if byteAt s (j + 1 + h) == 34 then
        let close := ByteArray.mk (#[34] ++ Array.replicate h 35)
        return some ({ close, escapes := false }, j + 2 + h - i)
      return none
    if byteAt s j == 34 then return some ({ close := "\"".toUTF8 }, j + 1 - i)
    return none
  | .js =>
    if b == 34 || b == 39 then
      return some ({ close := ByteArray.mk #[b], multiline := false }, 1)
    if b == 96 then return some ({ close := "`".toUTF8, interp := "${".toUTF8 }, 1)
    return none
  | .python =>
    if prevWord then return none
    -- Up to two prefix letters: r, b, u, f, t in either case.
    let mut j := i
    let mut raw := false
    let mut f := false
    for _ in [0:3] do
      let c := byteAt s j
      if c == 34 || c == 39 then break
      let l := if 65 ≤ c && c ≤ 90 then c + 32 else c
      if l == 114 then raw := true
      else if l == 102 || l == 116 then f := true
      else if l != 98 && l != 117 then return none
      j := j + 1
    let q := byteAt s j
    if q != 34 && q != 39 then return none
    let triple := byteAt s (j + 1) == q && byteAt s (j + 2) == q
    let close := if triple then ByteArray.mk #[q, q, q] else ByteArray.mk #[q]
    let kind : StrKind := {
      close
      raw
      interp := if f then "{".toUTF8 else .empty
      doubledBrace := f
      multiline := triple }
    return some (kind, j - i + close.size)
    -- A raw string still lets a backslash escape the quote, so `escapes` stays on for it.
  | .c =>
    -- `"…"`, `L"…"`, `u8"…"`, `@"…"`, `'c'`.
    if b == 34 then return some ({ close := "\"".toUTF8, multiline := false }, 1)
    if b == 39 then return some ({ close := "'".toUTF8, multiline := false }, 1)
    if b == 64 && byteAt s (i + 1) == 34 then
      return some ({ close := "\"".toUTF8, multiline := false }, 2)
    return none

/-- The index past a Rust character literal at `i`, or `none` for a lifetime such as `'a`. -/
def rustChar (s : ByteArray) (i : Nat) : Option Nat :=
  if byteAt s (i + 1) == 92 then Id.run do
    for k in [i + 3:min s.size (i + 14)] do
      if byteAt s k == 39 then return some (k + 1)
    return none
  else
    let (_, len) := decodeAt s (i + 1)
    if byteAt s (i + 1 + len) == 39 && byteAt s (i + 1) != 39 then some (i + 2 + len) else none

/-- Reads one JSX tag from the `<` at `i`, up to and including its `>`, and reports whether it
opens an element whose children follow (`<a>`), closes one (`</a>`), or stands alone (`<a/>`).
Attribute values in braces are code, so the tag stops there: `stop` is then the index after `{`. -/
inductive TagEnd where
  | opens | closes | selfClosing | attr
  deriving DecidableEq

def jsxTag (s : ByteArray) (i : Nat) : Nat × TagEnd := Id.run do
  let closing := byteAt s (i + 1) == 47
  -- `</>` closes a fragment: its `/` is not a self-closing one.
  let mut j := if closing then i + 2 else i + 1
  while j < s.size do
    let b := byteAt s j
    if b == 34 || b == 39 then
      j := j + 1
      while j < s.size && byteAt s j != b do j := j + 1
      j := j + 1
      continue
    if b == 123 then return (j + 1, .attr)
    if b == 47 && byteAt s (j + 1) == 62 then return (j + 2, .selfClosing)
    if b == 62 then return (j + 1, if closing then .closes else .opens)
    j := j + 1
  return (s.size, .selfClosing)

/-- Reads a tag's attributes after a `{…}` value, from `i`, to the tag's end. -/
def jsxTagRest (s : ByteArray) (i : Nat) : Nat × TagEnd := jsxTag s (i - 1)

/-- Reads JSX children from `i` to the next `<` or `{`. -/
def jsxText (s : ByteArray) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j < s.size && byteAt s j != 60 && byteAt s j != 123 do j := j + 1
  return j

def push (st : State) (kind : Kind) (s : ByteArray) (start stop : Nat) (jsx := false) : State :=
  let text := if kind == .str then "" else textOf s start stop
  { st with out := st.out.push { kind, text, start, stop, jsx } }

/-- After a string or a part of one: the string either ended, or code begins inside it. -/
def afterString (st : State) (k : StrKind) (s : ByteArray) (start : Nat) : State :=
  let (stop, code) := stringBody s k st.i
  let st := push { st with i := stop } .str s start stop
  if code then { st with stack := st.stack.push (.interp k) } else st

/-- JSX children, from `st.i`, until a `{` (code) or a tag, or the end of the element that took
the open elements above `base`. -/
partial def jsxChildren (s : ByteArray) (st : State) (base : Nat) : State := Id.run do
  let mut st := st
  while st.i < s.size do
    let j := jsxText s st.i
    st := { st with i := j }
    if j ≥ s.size then return st
    if byteAt s j == 123 then
      st := push { st with i := j + 1, stack := st.stack.push (.jsxExpr base) } .punct s j (j + 1) true
      return st
    -- A tag.
    let (stop, how) := jsxTag s j
    st := { st with i := stop }
    match how with
    | .attr =>
      st := push { st with stack := st.stack.push (.jsxAttr base), jsx := st.jsx + 1 } .punct s (stop - 1) stop true
      return st
    | .opens => st := { st with jsx := st.jsx + 1 }
    | .closes =>
      st := { st with jsx := st.jsx - 1 }
      if st.jsx ≤ base then return push st .str s (stop - 1) stop true
    | .selfClosing => pure ()
  return st

/-- After a tag's `>`: children for an element that opens, nothing for one that closes itself. -/
partial def afterTag (s : ByteArray) (st : State) (how : TagEnd) (base : Nat) : State :=
  match how with
  | .attr => push { st with stack := st.stack.push (.jsxAttr base) } .punct s (st.i - 1) st.i true
  | .opens => jsxChildren s st base
  | .closes | .selfClosing =>
    let st := { st with jsx := st.jsx - 1 }
    if st.jsx ≤ base then push st .str s (st.i - 1) st.i true else jsxChildren s st base

/-- The tokens of `s`. `jsx` reads JSX elements, as in `.js`, `.jsx` and `.tsx` files. -/
partial def tokens (fam : Family) (s : ByteArray) (jsx : Bool := false) : Array Tok := Id.run do
  let mut st : State := {}
  let lineComment := match fam with
    | .python => "#".toUTF8
    | _ => "//".toUTF8
  let blockNests := fam == .rust
  while st.i < s.size do
    let i := st.i
    let b := byteAt s i
    if isWs b || (fam != .python && b == 92 && byteAt s (i + 1) == 10) then
      st := { st with i := i + 1 }
      continue
    if fam == .python && b == 92 then
      st := { st with i := i + 1 }
      continue
    if hasAt s i lineComment then
      let mut j := i
      while j < s.size && byteAt s j != 10 do j := j + 1
      st := { st with i := j }
      continue
    if fam != .python && b == 47 && byteAt s (i + 1) == 42 then
      let mut j := i + 2
      let mut depth := 1
      while j < s.size && depth > 0 do
        if byteAt s j == 42 && byteAt s (j + 1) == 47 then
          depth := depth - 1
          j := j + 2
        else if blockNests && byteAt s j == 47 && byteAt s (j + 1) == 42 then
          depth := depth + 1
          j := j + 2
        else j := j + 1
      st := { st with i := j }
      continue
    -- C: a `#define` and its continuation lines are text, not code.
    if fam == .c && b == 35 then
      let mut j := i + 1
      while byteAt s j == 32 || byteAt s j == 9 do j := j + 1
      if hasAt s j "define".toUTF8 || hasAt s j "include".toUTF8 || hasAt s j "import".toUTF8 ||
          hasAt s j "pragma".toUTF8 || hasAt s j "error".toUTF8 || hasAt s j "warning".toUTF8 then
        while j < s.size && byteAt s j != 10 do
          if byteAt s j == 92 && byteAt s (j + 1) == 10 then j := j + 2
          else if byteAt s j == 13 && byteAt s (j + 1) == 10 && j > 0 && byteAt s (j - 1) == 92 then j := j + 2
          else j := j + 1
        st := { st with i := j }
        continue
    let prevWord := i > 0 && isIdByte (byteAt s (i - 1))
    if let some (k, len) := stringAt fam s i prevWord then
      st := afterString { st with i := i + len } k s i
      continue
    if fam == .rust && b == 39 then
      match rustChar s i with
      | some stop =>
        st := push { st with i := stop } .str s i stop
        continue
      | none =>
        -- A lifetime: `'` and a name.
        let mut j := i + 1
        while j < s.size && isIdByte (byteAt s j) do j := j + 1
        st := push { st with i := j } .ident s i j
        continue
    if isDigit b then
      let mut j := i + 1
      while j < s.size && (isIdByte (byteAt s j) ||
          (byteAt s j == 46 && isDigit (byteAt s (j + 1)))) do j := j + 1
      st := push { st with i := j } .num s i j
      continue
    if isIdByte b || (fam == .js && b == 35 && isIdByte (byteAt s (i + 1))) ||
        (fam == .c && b == 64 && isAlpha (byteAt s (i + 1))) then
      let mut j := i + 1
      -- Rust's raw names: `r#match`.
      if fam == .rust && b == 114 && byteAt s j == 35 && isIdByte (byteAt s (j + 1)) then j := j + 1
      while j < s.size && isIdByte (byteAt s j) do j := j + 1
      st := push { st with i := j } .ident s i j
      continue
    -- Closing brackets: a string's code part may end here.
    if b == 125 || b == 41 || b == 93 then
      match st.stack.back? with
      | some (.interp k) =>
        -- Python's format spec and conversion (`{x:>4}`, `{x!r}`) belong to the string.
        st := { st with stack := st.stack.pop, i := i + 1 }
        st := afterString st k s i
        continue
      | some (.jsxExpr base) =>
        st := push { st with stack := st.stack.pop, i := i + 1 } .punct s i (i + 1) true
        st := jsxChildren s st base
        continue
      | some (.jsxAttr base) =>
        st := push { st with stack := st.stack.pop, i := i + 1 } .punct s i (i + 1) true
        let (stop, how) := jsxTagRest s st.i
        st := afterTag s { st with i := stop } how base
        continue
      | _ =>
        st := push { st with stack := st.stack.pop, i := i + 1 } .punct s i (i + 1)
        continue
    if b == 123 || b == 40 || b == 91 then
      st := push { st with stack := st.stack.push (.bracket b), i := i + 1 } .punct s i (i + 1)
      continue
    -- Python's f-string code ends at a format spec too.
    if fam == .python && (b == 58 || b == 33) then
      if let some (.interp k) := st.stack.back? then
        if b == 58 || byteAt s (i + 1) != 61 then
          -- Skip the spec up to the closing brace, which ends the code part.
          let mut j := i + 1
          let mut depth := 0
          while j < s.size && !(byteAt s j == 125 && depth == 0) do
            if byteAt s j == 123 then depth := depth + 1
            else if byteAt s j == 125 then depth := depth - 1
            j := j + 1
          st := { st with stack := st.stack.pop, i := j + 1 }
          st := afterString st k s i
          continue
    if fam == .js && b == 47 && !afterOperand st.out then
      if let some stop := regexEnd s i then
        st := push { st with i := stop } .str s i stop
        continue
    if fam == .js && jsx && b == 60 && !afterOperand st.out &&
        (isAlpha (byteAt s (i + 1)) || byteAt s (i + 1) == 62) then
      let (stop, how) := jsxTag s i
      -- The element's first and last characters stand for it in the tokens, so it has an extent
      -- and a statement does not end inside it.
      st := push st .str s i (i + 1) true
      st := afterTag s { st with i := stop, jsx := st.jsx + 1 } how st.jsx
      continue
    let len := match symbols.find? (hasAt s i ·) with
      | some sym =>
        -- `a?.5:1` is a ternary.
        if sym == "?.".toUTF8 && isDigit (byteAt s (i + 2)) then 1 else sym.size
      | none => (decodeAt s i).2
    st := push { st with i := i + len } .punct s i (i + len)
  -- Lines and columns, from the byte offsets.
  let starts := (lineRanges s).map (·.1)
  let lineOf (offset : Nat) : Nat := Id.run do
    let mut lo := 0
    let mut hi := starts.size
    while lo + 1 < hi do
      let mid := (lo + hi) / 2
      if starts[mid]! ≤ offset then lo := mid else hi := mid
    return lo + 1
  let mut lastLine := 0
  let mut out := st.out
  for n in [0:out.size] do
    let t := out[n]!
    let line := lineOf t.start
    let endLine := lineOf (max t.start (t.stop - 1))
    -- A token that follows a string spanning lines is not the first on its line.
    out := out.set! n { t with
      line := line
      endLine := endLine
      column := t.start - starts[line - 1]!
      first := line != lastLine }
    lastLine := endLine
  return out

/-- For each opening bracket, the index of the token that closes it; every other token maps to
itself. An unclosed bracket maps to the last token. -/
def matching (ts : Array Tok) : Array Nat := Id.run do
  let mut out := Array.range ts.size
  let mut stack : Array Nat := #[]
  for h : n in [0:ts.size] do
    let t := ts[n]
    if t.kind != .punct then continue
    if t.text == "(" || t.text == "[" || t.text == "{" then stack := stack.push n
    else if t.text == ")" || t.text == "]" || t.text == "}" then
      if let some o := stack.back? then
        out := out.set! o n
        stack := stack.pop
  for o in stack do out := out.set! o (ts.size - 1)
  return out

end Clocrap.Lex

namespace Clocrap.Lex

/-- For each closing bracket, the index of the token that opens it; every other token maps to
itself. -/
def openers (m : Array Nat) : Array Nat := Id.run do
  let mut out := Array.range m.size
  for h : n in [0:m.size] do
    let c := m[n]
    if c != n && c < out.size then out := out.set! c n
  return out

/-- A function as an analyzer finds it, with the token span it covers. -/
structure Found where
  name : String
  /-- Token indices of the function's first and last tokens. -/
  first : Nat
  last : Nat
  complexity : Int
  /-- The last line, when it is not the last token's: Python's trailing comments. -/
  endLine : Option Nat := none
  deriving Inhabited

/-- The functions in the order a tree-sitter walk reported them: a parse tree walked from a stack
finds a function before the functions inside it, and a later sibling before an earlier one. The
caller sorts by lines with a stable sort, so this order decides ties. -/
def treeOrder (ts : Array Tok) (found : Array Found) : Array Function :=
  let walk := found.toList.mergeSort fun a b =>
    ts[a.last]!.stop > ts[b.last]!.stop ||
      (ts[a.last]!.stop == ts[b.last]!.stop && ts[a.first]!.start ≤ ts[b.first]!.start)
  let fns := walk.map fun f =>
    { name := f.name, startLine := ts[f.first]!.line, endLine := f.endLine.getD ts[f.last]!.endLine,
      complexity := (max f.complexity 1).toNat : Function }
  (fns.mergeSort fun a b =>
    a.startLine < b.startLine || (a.startLine == b.startLine && a.endLine ≤ b.endLine)).toArray

/-- Marks every token inside a function in `found` other than the one being scored, so a nested
function's decisions are its own. Returns, for function `n`, the token indices to score. -/
def ownTokens (found : Array Found) (n : Nat) : Array (Nat × Nat) := Id.run do
  let f := found[n]!
  -- The direct children: functions inside `f` and not inside another one inside it.
  let inner := found.filter fun g => g.first > f.first && g.last ≤ f.last
  let mut gaps := #[]
  let mut at_ := f.first
  for g in inner.toList.mergeSort (fun a b => a.first ≤ b.first) do
    if g.first < at_ then continue
    gaps := gaps.push (at_, g.first)
    at_ := g.last + 1
  return gaps.push (at_, f.last + 1)

end Clocrap.Lex
