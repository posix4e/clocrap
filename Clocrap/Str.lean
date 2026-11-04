/-!
# String helpers

Lean 4.35's `String.drop` and friends return a `String.Slice`. These return a `String`.
-/

namespace String

@[inline] def dropS (s : String) (n : Nat) : String := (s.drop n).toString
@[inline] def takeS (s : String) (n : Nat) : String := (s.take n).toString
@[inline] def dropRight (s : String) (n : Nat) : String := (s.dropEnd n).toString
@[inline] def dropRightWhile (s : String) (p : Char → Bool) : String := (s.dropEndWhile p).toString
@[inline] def trimS (s : String) : String := s.trimAscii.toString

end String
