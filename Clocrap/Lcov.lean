import Clocrap.Bytes
import Std.Data.HashMap
import Std.Data.TreeMap

/-!
# lcov

Line coverage from lcov files: the format `cargo llvm-cov --lcov` and most other coverage tools
write. The `SF:`, `DA:`, `FN:` and `FNDA:` records are read: `FN:` names each function's first
line and `FNDA:` counts its calls, which Lean's coverage needs (see `Clocrap.LeanCov`).
-/

namespace Clocrap

/-- Hit counts per line, for every source file in one or more lcov reports. -/
structure Coverage where
  /-- Keyed by the file's path as the report gives it, canonicalised when the file exists. Each
  value is the file's 1-based lines with their hit counts, sorted by line, one entry per line. -/
  files : Std.HashMap String (Array (Nat × Nat)) := {}
  /-- Each file's functions: first line to name. -/
  functions : Std.HashMap String (Std.TreeMap Nat String) := {}
  /-- Each file's functions by name, with how many times each was called. A file whose report has
  no `FNDA:` records has no entry. -/
  calls : Std.HashMap String (Std.HashMap String Nat) := {}
  deriving Inhabited

namespace Coverage

/-- `FN:<line>,<name>`, or `FN:<line>,<end line>,<name>` as newer lcov writes. -/
def parseFn (record : String) : Option (Nat × String) := do
  let comma ← record.toList.findIdx? (· == ',')
  let number ← (record.take comma).toString.trimAscii.toString.toNat?
  let rest := (record.drop (comma + 1)).toString
  let name := match rest.toList.findIdx? (· == ',') with
    | some c =>
      if ((rest.take c).toString.trimAscii.toString.toNat?).isSome then (rest.drop (c + 1)).toString
      else rest
    | none => rest
  return (number, name.trimAscii.toString)

/-- `FNDA:<calls>,<name>`. -/
def parseFnda (record : String) : Option (String × Nat) := do
  let comma ← record.toList.findIdx? (· == ',')
  let count ← (record.take comma).toString.trimAscii.toString.toNat?
  return ((record.drop (comma + 1)).toString.trimAscii.toString, count)

/-- Two files' call counts as one: the calls of a function in both add up. -/
def addCalls (a b : Std.HashMap String Nat) : Std.HashMap String Nat :=
  b.fold (init := a) fun acc name n => acc.insert name (acc.getD name 0 + n)

/-- The canonical path when the file exists, else the path as given. -/
def canonicalOrSame (path : String) : IO String := do
  try return (← IO.FS.realPath path).toString catch _ => return path

/-- Two files' lines, each sorted with one entry per line, as one: the hits of a line in both add
up. -/
def addLines (a b : Array (Nat × Nat)) : Array (Nat × Nat) := Id.run do
  let mut out := Array.mkEmpty (a.size + b.size)
  let mut i := 0
  let mut j := 0
  while i < a.size || j < b.size do
    if j ≥ b.size || (i < a.size && a[i]!.1 < b[j]!.1) then
      out := out.push a[i]!
      i := i + 1
    else if i ≥ a.size || b[j]!.1 < a[i]!.1 then
      out := out.push b[j]!
      j := j + 1
    else
      out := out.push (a[i]!.1, a[i]!.2 + b[j]!.2)
      i := i + 1
      j := j + 1
  return out

/-- One record's `DA:` lines in the order the report gave them, sorted with one entry per line. -/
def normalize (lines : Array (Nat × Nat)) : Array (Nat × Nat) := Id.run do
  let mut ordered := true
  for k in [1:lines.size] do
    if lines[k - 1]!.1 ≥ lines[k]!.1 then ordered := false
  if ordered then return lines
  let sorted := lines.toList.mergeSort (fun a b => a.1 ≤ b.1) |>.toArray
  let mut out : Array (Nat × Nat) := #[]
  for (n, h) in sorted do
    match out.back? with
    | some (m, g) => if m == n then out := out.pop.push (n, g + h) else out := out.push (n, h)
    | none => out := out.push (n, h)
  return out

/-- The number in bytes `[lo, hi)` of `s`, with ASCII whitespace around it, as Rust's `trim` and
`parse::<u64>` read it. -/
def natIn (s : ByteArray) (lo hi : Nat) : Option Nat := Id.run do
  let mut lo := lo
  let mut hi := hi
  while lo < hi && isWs (byteAt s lo) do lo := lo + 1
  while hi > lo && isWs (byteAt s (hi - 1)) do hi := hi - 1
  if lo < hi && byteAt s lo == 43 then lo := lo + 1
  if lo ≥ hi then return none
  let mut n := 0
  for k in [lo:hi] do
    let b := byteAt s k
    if !isDigit b then return none
    n := n * 10 + (b - 48).toNat
  return some n

/-- The index of the first `,` in bytes `[lo, hi)` of `s`, or `hi`. -/
def commaIn (s : ByteArray) (lo hi : Nat) : Nat := Id.run do
  let mut k := lo
  while k < hi && byteAt s k != 44 do k := k + 1
  return k

/-- Parses the text of one lcov report. Each record's lines are gathered on their own and added to
the totals when the record ends, so the maps of every file are not rebuilt per line. -/
def parse (text : String) : IO Coverage := do
  let s := text.toUTF8
  let mut c : Coverage := {}
  let mut current : Option String := none
  let mut lines : Array (Nat × Nat) := #[]
  let mut fns : Std.TreeMap Nat String := {}
  let mut calls : Std.HashMap String Nat := {}
  let flush (c : Coverage) (file : Option String) (lines : Array (Nat × Nat))
      (fns : Std.TreeMap Nat String) (calls : Std.HashMap String Nat) : Coverage := Id.run do
    let some file := file | return c
    let mut c := c
    if !lines.isEmpty then
      let lines := normalize lines
      let mine := match c.files.get? file with
        | some old => addLines old lines
        | none => lines
      c := { c with files := c.files.insert file mine }
    if !fns.isEmpty then
      let mine := match c.functions.get? file with
        | some old => fns.foldl (init := old) fun acc n name => acc.insert n name
        | none => fns
      c := { c with functions := c.functions.insert file mine }
    if !calls.isEmpty then
      c := { c with calls := c.calls.insert file (addCalls (c.calls.getD file {}) calls) }
    return c
  -- Rust's `lines()`: split on `\n`, drop one trailing `\r`, no empty last line.
  let mut i := 0
  while i < s.size do
    let mut j := i
    while j < s.size && byteAt s j != 10 do j := j + 1
    let next := j + 1
    if j > i && byteAt s (j - 1) == 13 then j := j - 1
    if hasAt s i "SF:".toUTF8 && j ≥ i + 3 then
      c := flush c current lines fns calls
      lines := #[]
      fns := {}
      calls := {}
      current := some (← canonicalOrSame (String.fromUTF8! (s.extract (i + 3) j)))
    else if hasAt s i "DA:".toUTF8 && j ≥ i + 3 then
      if current.isSome then
        let a := commaIn s (i + 3) j
        let b := commaIn s (min j (a + 1)) j
        if a < j then
          if let (some number, some hits) := (natIn s (i + 3) a, natIn s (a + 1) b) then
            lines := lines.push (number, hits)
    else if hasAt s i "FN:".toUTF8 && j ≥ i + 3 then
      if current.isSome then
        if let some (number, name) := parseFn (String.fromUTF8! (s.extract (i + 3) j)) then
          fns := fns.insert number name
    else if hasAt s i "FNDA:".toUTF8 && j ≥ i + 5 then
      if current.isSome then
        if let some (name, n) := parseFnda (String.fromUTF8! (s.extract (i + 5) j)) then
          calls := calls.insert name (calls.getD name 0 + n)
    else if j == i + 13 && hasAt s i "end_of_record".toUTF8 then
      c := flush c current lines fns calls
      lines := #[]
      fns := {}
      calls := {}
      current := none
    i := next
  return flush c current lines fns calls

/-- Adds another report's hit counts to this one. -/
def merge (c other : Coverage) : Coverage := Id.run do
  let mut c := c
  for (path, lines) in other.files do
    c := { c with files := c.files.insert path (addLines (c.files.getD path #[]) lines) }
  for (path, fns) in other.functions do
    let mut mine := c.functions.getD path {}
    for (number, name) in fns do
      if !mine.contains number then mine := mine.insert number name
    c := { c with functions := c.functions.insert path mine }
  for (path, counts) in other.calls do
    c := { c with calls := c.calls.insert path (addCalls (c.calls.getD path {}) counts) }
  return c

/-- Reads and merges several lcov files. Hit counts for the same line add up. -/
def read (paths : Array String) : IO Coverage := do
  let mut c : Coverage := {}
  for path in paths do
    let text ← try IO.FS.readFile path
      catch e => throw <| IO.userError s!"cannot read lcov file {path}: {e}"
    c := c.merge (← parse text)
  return c

/-- Every file the report has line records for. -/
def fileList (c : Coverage) : Array String := c.files.toArray.map (·.1)

/-- The functions the report names in `path`, by first line. -/
def functionsOf (c : Coverage) (path : String) : Option (Std.TreeMap Nat String) :=
  c.functions.get? path

/-- How many times each function in `path` was called, by name. `none` when the report has no call
counts for the file. -/
def callsOf (c : Coverage) (path : String) : Option (Std.HashMap String Nat) := c.calls.get? path

/-- The report's lines for `path`, sorted. The path is looked up as given: see `resolve`. -/
def linesOf (c : Coverage) (path : String) : Option (Array (Nat × Nat)) := c.files.get? path

/-- The key the report uses for `path`: the path itself, or its canonical form. -/
def resolve (c : Coverage) (path : String) : IO String := do
  if c.files.contains path then return path
  canonicalOrSame path

/-- The index of the first entry at or after `line`. -/
def lowerBound (lines : Array (Nat × Nat)) (line : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := lines.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if lines[mid]!.1 < line then lo := mid + 1 else hi := mid
  return lo

/-- The instrumented lines in `start..=stop`, and how many of them ran. -/
def hits (c : Coverage) (path : String) (start stop : Nat) : Nat × Nat := Id.run do
  let some lines := c.linesOf path | return (0, 0)
  let mut total := 0
  let mut covered := 0
  for k in [lowerBound lines start:lines.size] do
    let (number, h) := lines[k]!
    if number > stop then break
    total := total + 1
    if h > 0 then covered := covered + 1
  return (total, covered)

/-- Whether the report has any record for `path`. -/
def hasFile (c : Coverage) (path : String) : Bool := (c.linesOf path).isSome

/-- The fraction of instrumented lines in `start..=stop` that ran, between 0 and 1. A range with no
instrumented lines counts as 0, since nothing shows that it ran. `none` if the report has no record
for the file at all. -/
def ratio (c : Coverage) (path : String) (start stop : Nat) : Option Float := do
  let _ ← c.linesOf path
  let (total, covered) := c.hits path start stop
  if total == 0 then return 0.0
  return covered.toFloat / total.toFloat

end Coverage
end Clocrap
