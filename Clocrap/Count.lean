import Clocrap.Bytes
import Clocrap.Lang

/-!
# Line classification

One pass over the bytes of a file decides, for every line, whether it is blank, comment or code.
Comment and string state carries from line to line, so a `//` inside a string is code and a `/*`
that opens on one line stays open until its `*/`.
-/

namespace Clocrap

/-- What one line holds. -/
inductive LineKind where
  /-- Only whitespace. -/
  | blank
  /-- Only comment text. -/
  | comment
  /-- Code, possibly with a trailing comment. -/
  | code
  deriving DecidableEq, Repr, Inhabited

instance : BEq LineKind := ⟨fun a b => decide (a = b)⟩

/-- Line totals for one file or a sum of files. -/
structure LineCounts where
  blank : Nat := 0
  comment : Nat := 0
  code : Nat := 0
  deriving DecidableEq, Repr, Inhabited

namespace LineCounts

/-- Every line, of any kind. -/
def total (c : LineCounts) : Nat := c.blank + c.comment + c.code

/-- Adds one line of the given kind. -/
def record (c : LineCounts) : LineKind → LineCounts
  | .blank => { c with blank := c.blank + 1 }
  | .comment => { c with comment := c.comment + 1 }
  | .code => { c with code := c.code + 1 }

/-- Adds another set of totals to this one. -/
def add (c d : LineCounts) : LineCounts :=
  ⟨c.blank + d.blank, c.comment + d.comment, c.code + d.code⟩

end LineCounts

/-- Where the lexer is when a line begins. -/
inductive LexState where
  | code
  /-- Inside a block comment, with the nesting depth (1 when not nested). -/
  | block (depth : Nat)
  /-- Inside the string at this index in the syntax's `strings`. -/
  | str (index : Nat)
  deriving DecidableEq, Inhabited

/-- Whether `marker` starts at byte `i` of the line as its own token. A marker that begins with a
letter must not follow another identifier character, so `bar"` is not a raw string opener. A `#`
comment must follow whitespace or the start of the line, so `$#` in a shell script is not a
comment. -/
def startsToken (s : ByteArray) (lineStart i : Nat) (marker : ByteArray) : Bool :=
  hasAt s i marker &&
    let before := if i == lineStart then none else some (byteAt s (i - 1))
    let first := byteAt marker 0
    if first == 35 then before.all isWs
    else if isAlpha first then before.all fun b => !(isAlnum b || b == 95)
    else true

/-- The length of the character literal at byte `i`, if it is one, within a line ending at
`stop`. `'a'` and `'\n'` are literals; `'a` followed by anything else is a lifetime. -/
def charLiteralLen (s : ByteArray) (i stop : Nat) : Option Nat := Id.run do
  let len := stop - i
  if len ≥ 3 && byteAt s (i + 1) == 92 then
    let upto := min stop (i + 12)
    for k in [i + 2:upto] do
      if byteAt s k == 39 then return some (k - i + 1)
    return none
  if len ≥ 3 && byteAt s (i + 1) != 39 && byteAt s (i + 2) == 39 then return some 3
  return none

/-- For each byte value, whether a comment, string or character literal can start with it. Code
bytes that cannot are skipped without trying every marker. -/
def markerStarts (syn : Syntax) : ByteArray := Id.run do
  let mut out := ByteArray.mk (Array.replicate 256 0)
  let mut firsts := syn.lineComments.map (byteAt · 0) ++ syn.strings.map (byteAt ·.opener 0)
  if let some block := syn.block then firsts := firsts.push (byteAt block.opener 0)
  if syn.charLiterals then firsts := firsts.push 39
  for b in firsts do out := out.set! b.toNat 1
  return out

/-- Classifies the line `[start, stop)` of `s`, carrying the lexer state across lines. `starts`
is `markerStarts syn`. -/
def classifyLine (s : ByteArray) (start stop : Nat) (syn : Syntax) (starts : ByteArray)
    (state : LexState) : LineKind × LexState := Id.run do
  if allWs s start stop then return (.blank, state)
  let mut state := state
  let mut hasCode := false
  let mut i := start
  -- Each step moves `i` forward, so `stop - start` steps of fuel are plenty.
  for _ in [0:stop - start + 1] do
    if i ≥ stop then break
    match state with
    | .block depth =>
      match syn.block with
      | none => state := .code
      | some block =>
        if hasAt s i block.closer then
          i := i + block.closer.size
          state := if depth ≤ 1 then .code else .block (depth - 1)
        else if block.nests && hasAt s i block.opener then
          i := i + block.opener.size
          state := .block (depth + 1)
        else i := i + 1
    | .str index =>
      hasCode := true
      let string := syn.strings[index]!
      let close := byteAt string.closer 0
      while i < stop && byteAt s i != close && byteAt s i != 92 do i := i + 1
      if i ≥ stop then break
      if string.escapes && byteAt s i == 92 then i := i + 2
      else if hasAt s i string.closer then
        i := i + string.closer.size
        state := .code
      else i := i + 1
    | .code =>
      let b := byteAt s i
      if isWs b then
        i := i + 1
        continue
      if byteAt starts b.toNat == 0 then
        hasCode := true
        i := i + 1
        continue
      if syn.lineComments.any (startsToken s start i ·) then break
      if let some block := syn.block then
        if hasAt s i block.opener then
          i := i + block.opener.size
          state := .block 1
          continue
      hasCode := true
      if syn.charLiterals && b == 39 then
        if let some len := charLiteralLen s i stop then
          i := i + len
          continue
      match syn.strings.findIdx? (fun st => startsToken s start i st.opener) with
      | some index =>
        i := i + syn.strings[index]!.opener.size
        state := .str index
      | none => i := i + 1
  -- A string that cannot span lines ends with its line, even if it never closed.
  if let .str index := state then
    if !syn.strings[index]!.multiline then state := .code
  return (if hasCode then .code else .comment, state)

/-- The kind of every line of `s`, in order. A final line without a newline is a line, so the
number of lines matches `wc -l` for files that end in a newline and is one more for files that do
not. A file that is empty has no lines. -/
def lineKinds (s : ByteArray) (syn : Syntax) : Array LineKind := Id.run do
  let mut state := LexState.code
  let mut out := #[]
  let starts := markerStarts syn
  for (start, stop) in lineRanges s do
    let (kind, next) := classifyLine s start stop syn starts state
    out := out.push kind
    state := next
  return out

end Clocrap
