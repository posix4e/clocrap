import Clocrap.Str
/-!
# Bytes

Source files are read as bytes and scanned by index, so a file that is not UTF-8 still counts and
nothing is copied while scanning. These are the small helpers every scanner shares.
-/

namespace Clocrap

/-- The byte at `i`, or 0 past the end. -/
@[inline] def byteAt (s : ByteArray) (i : Nat) : UInt8 :=
  if h : i < s.size then s[i] else 0

/-- ASCII whitespace as Rust's `u8::is_ascii_whitespace` has it: space, tab, LF, FF and CR. -/
@[inline] def isWs (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 12 || b == 13

@[inline] def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

@[inline] def isAlpha (b : UInt8) : Bool := (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)

@[inline] def isAlnum (b : UInt8) : Bool := isAlpha b || isDigit b

/-- A letter, digit or `_`. -/
@[inline] def isWord (b : UInt8) : Bool := isAlnum b || b == 95

/-- Whether `pat` occurs in `s` at byte `i`. -/
def hasAt (s : ByteArray) (i : Nat) (pat : ByteArray) : Bool := Id.run do
  if i + pat.size > s.size then return false
  for k in [0:pat.size] do
    if byteAt s (i + k) != byteAt pat k then return false
  return true

/-- Whether bytes `start` to `stop` (exclusive) are all whitespace. -/
def allWs (s : ByteArray) (start stop : Nat) : Bool := Id.run do
  for k in [start:stop] do
    if !isWs (byteAt s k) then return false
  return true

/-- The `[start, stop)` byte ranges of the lines of `s`, without their `\n`. A final line with no
newline is a line; an empty file has none. -/
def lineRanges (s : ByteArray) : Array (Nat × Nat) := Id.run do
  let mut out := #[]
  let mut start := 0
  for k in [0:s.size] do
    if s[k]! == 10 then
      out := out.push (start, k)
      start := k + 1
  if start < s.size then out := out.push (start, s.size)
  return out

/-- The bytes `start` to `stop` as a string, replacing invalid UTF-8. -/
def textOf (s : ByteArray) (start stop : Nat) : String :=
  let b := s.extract start stop
  match String.fromUTF8? b with
  | some t => t
  | none => String.ofList (b.toList.map fun c => if c < 128 then Char.ofNat c.toNat else '�')

/-- The Unicode scalar starting at byte `i` and its length in bytes; a byte that does not start a
valid sequence reads as U+FFFD of length 1. -/
def decodeAt (s : ByteArray) (i : Nat) : UInt32 × Nat :=
  let b0 := byteAt s i
  if b0 < 0x80 then (b0.toUInt32, 1)
  else
    let cont (k : Nat) : Option UInt32 :=
      let b := byteAt s (i + k)
      if b &&& 0xC0 == 0x80 then some (b &&& 0x3F).toUInt32 else none
    let bad : UInt32 × Nat := (0xFFFD, 1)
    if b0 &&& 0xE0 == 0xC0 then
      match cont 1 with
      | some c1 => (((b0 &&& 0x1F).toUInt32 <<< 6) ||| c1, 2)
      | none => bad
    else if b0 &&& 0xF0 == 0xE0 then
      match cont 1, cont 2 with
      | some c1, some c2 => (((b0 &&& 0x0F).toUInt32 <<< 12) ||| (c1 <<< 6) ||| c2, 3)
      | _, _ => bad
    else if b0 &&& 0xF8 == 0xF0 then
      match cont 1, cont 2, cont 3 with
      | some c1, some c2, some c3 =>
        (((b0 &&& 0x07).toUInt32 <<< 18) ||| (c1 <<< 12) ||| (c2 <<< 6) ||| c3, 4)
      | _, _, _ => bad
    else bad

/-- A string whose order is path order as Rust's `PathBuf` has it: component by component, each
compared as bytes, so `a/b` sorts before `a-b/c`. Sorting by the key splits each path once instead
of at every comparison. -/
def pathKey (p : String) : String := Id.run do
  -- An absolute path's root component sorts before any name, and each separator below any byte
  -- of a name, so a component sorts before the longer names it is a prefix of.
  let mut out := if p.startsWith "/" then "\x00" else ""
  let mut pending := false
  for c in p.toList do
    if c == '/' then
      pending := true
    else
      if pending && !(out.isEmpty || out == "\x00") then out := out.push '\x01'
      pending := false
      out := out.push c
  return out

/-- Path order: see `pathKey`. -/
def pathLt (a b : String) : Bool := pathKey a < pathKey b

/-- `s` without `pre` in front, or `none` when it does not start with it. -/
def stripPrefix? (s pre : String) : Option String :=
  if s.startsWith pre then some (s.drop pre.length).toString else none

/-- `s` without `suf` at the end, or `none` when it does not end with it. -/
def stripSuffix? (s suf : String) : Option String :=
  if s.endsWith suf then some (s.dropEnd suf.length).toString else none

/-- The text before and after the first `sep`. -/
def splitOnce? (s sep : String) : Option (String × String) :=
  match s.splitOn sep with
  | first :: rest@(_ :: _) => some (first, sep.intercalate rest)
  | _ => none

/-- The text before and after the last `sep`. -/
def rsplitOnce? (s sep : String) : Option (String × String) :=
  match s.splitOn sep with
  | parts@(_ :: _ :: _) => some (sep.intercalate parts.dropLast, parts.getLast!)
  | _ => none

/-- `s` without trailing whitespace. -/
def trimEnd (s : String) : String := (s.trimAsciiEnd).toString

end Clocrap
