import Clocrap.Str
/-!
# Printing floats

Lean's `Float.toString` prints six fixed decimals. The reports print coverage and CRAP scores the
way Rust does, so these work from a double's exact value (`m · 2^e`) in `Nat` arithmetic:

- `fixed x p` is `x` rounded to `p` decimals, half to even on an exact tie, as Rust's `{:.p}`.
- `shortest x` is the fewest digits that read back as `x`, as Rust's `{}` and serde's JSON use.
-/

namespace Clocrap.Num

/-- A finite double's magnitude as `m · 2^e`. -/
def decompose (x : Float) : Nat × Int :=
  let bits := x.toBits
  let exp := ((bits >>> 52) &&& 0x7FF).toNat
  let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if exp == 0 then (frac, -1074) else (frac + 2 ^ 52, (exp : Int) - 1075)

/-- `n · 2^p2 · 10^p10`. -/
structure Q where
  n : Nat
  p2 : Int
  p10 : Int

/-- Compares two `Q`s exactly, by scaling both by the same power of 2 and of 10. -/
def Q.cmp (a b : Q) : Ordering :=
  let s2 := min a.p2 b.p2
  let s10 := min a.p10 b.p10
  let x := a.n * 2 ^ (a.p2 - s2).toNat * 10 ^ (a.p10 - s10).toNat
  let y := b.n * 2 ^ (b.p2 - s2).toNat * 10 ^ (b.p10 - s10).toNat
  compare x y

/-- `num / den` rounded to the nearest integer, half to even. -/
def roundHalfEven (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den then q + 1
  else if 2 * r < den then q
  else if q % 2 == 0 then q else q + 1

/-- `x · 10^(-k)` rounded half to even, for `m · 2^e = x`. -/
def scaled (m : Nat) (e k : Int) : Nat :=
  let num := m * 2 ^ (max e 0).toNat * 10 ^ (max (-k) 0).toNat
  let den := 2 ^ (max (-e) 0).toNat * 10 ^ (max k 0).toNat
  roundHalfEven num den

def zeros (n : Nat) : String := String.ofList (List.replicate n '0')

/-- `x` with `p` decimals, rounded half to even on its exact value. -/
def fixed (x : Float) (p : Nat) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x < 0 then "-inf" else "inf")
  else
    let sign := if x < 0 || (x == 0 && x.toBits >>> 63 == 1) then "-" else ""
    let (m, e) := decompose x
    let q := scaled m e (-(p : Int))
    let ip := q / 10 ^ p
    let fp := toString (q % 10 ^ p)
    let frac := if p == 0 then "" else "." ++ zeros (p - fp.length) ++ fp
    sign ++ toString ip ++ frac

/-- The shortest digits `d` and exponent `k` with `d · 10^k` reading back as `|x|`, which is finite
and not zero. Reading back rounds to nearest, ties to even, so the interval's ends count when `m`
is even. -/
def shortest (x : Float) : String × Int := Id.run do
  let (m, e) := decompose x
  let halfGapBelow := m == 2 ^ 52 && e > -1074
  let low : Q := if halfGapBelow then ⟨4 * m - 1, e - 2, 0⟩ else ⟨2 * m - 1, e - 1, 0⟩
  let high : Q := ⟨2 * m + 1, e - 1, 0⟩
  let inclusive := m % 2 == 0
  let value : Q := ⟨m, e, 0⟩
  -- The decimal exponent of the leading digit: 10^big ≤ x < 10^(big+1).
  let mut big : Int := (Float.floor (Float.log10 x.abs)).toInt64.toInt
  while (Q.cmp ⟨1, 0, big⟩ value) == .gt do big := big - 1
  while (Q.cmp ⟨1, 0, big + 1⟩ value) != .gt do big := big + 1
  for p in [1:18] do
    let k := big - p + 1
    let c := scaled m e k
    let cand : Q := ⟨c, 0, k⟩
    let aboveLow := match Q.cmp cand low with
      | .gt => true
      | .eq => inclusive
      | .lt => false
    let belowHigh := match Q.cmp cand high with
      | .lt => true
      | .eq => inclusive
      | .gt => false
    if aboveLow && belowHigh then
      let mut digits := c
      let mut exp := k
      while digits % 10 == 0 && digits > 0 do
        digits := digits / 10
        exp := exp + 1
      return (toString digits, exp)
  return (toString m, 0)

/-- Rust's `{}` for a float: the shortest digits, in plain decimal, with no `.0` on a whole
number. -/
def display (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x < 0 then "-inf" else "inf")
  else if x == 0 then (if x.toBits >>> 63 == 1 then "-0" else "0")
  else
    let sign := if x < 0 then "-" else ""
    let (d, k) := shortest x
    let len : Int := d.length
    let body :=
      if k ≥ 0 then d ++ zeros k.toNat
      else
        let point := len + k
        if point > 0 then
          d.takeS point.toNat ++ "." ++ d.dropS point.toNat
        else "0." ++ zeros (-point).toNat ++ d
    sign ++ body

/-- serde's JSON for a float, as the `ryu` crate prints it: `1.0`, `0.5`, `0.001234`, `1e30`,
`1.234e33`. -/
def json (x : Float) : String :=
  if x.isNaN || x.isInf then "null"
  else if x == 0 then (if x.toBits >>> 63 == 1 then "-0.0" else "0.0")
  else
    let sign := if x < 0 then "-" else ""
    let (d, k) := shortest x
    let len : Int := d.length
    let kk := len + k
    let body :=
      if 0 ≤ k && kk ≤ 16 then d ++ zeros k.toNat ++ ".0"
      else if 0 < kk && kk ≤ 16 then d.takeS kk.toNat ++ "." ++ d.dropS kk.toNat
      else if -5 < kk && kk ≤ 0 then "0." ++ zeros (-kk).toNat ++ d
      else if len == 1 then d ++ "e" ++ toString (kk - 1)
      else d.takeS 1 ++ "." ++ d.dropS 1 ++ "e" ++ toString (kk - 1)
    sign ++ body

/-- Parses a decimal such as `30`, `-2.5` or `1e3` to the nearest double, as Rust's
`str::parse::<f64>` does for the forms a person types. -/
def parse? (text : String) : Option Float := Id.run do
  let s := text.trimAscii.toString
  if s.isEmpty then return none
  let (neg, body) := if s.startsWith "-" then (true, s.dropS 1) else if s.startsWith "+" then (false, s.dropS 1) else (false, s)
  let lower := body.toLower
  if lower == "inf" || lower == "infinity" then
    return some (if neg then -(1.0 / 0.0) else 1.0 / 0.0)
  if lower == "nan" then return some (0.0 / 0.0)
  let (mant, exp10) := match body.splitOn "e" with
    | [a] => match a.splitOn "E" with
      | [a] => (a, some (0 : Int))
      | [a, b] => (a, b.toInt?)
      | _ => (a, none)
    | [a, b] => (a, b.toInt?)
    | _ => (body, none)
  let some exp10 := exp10 | return none
  let (ip, fp) := match mant.splitOn "." with
    | [a] => (a, "")
    | [a, b] => (a, b)
    | _ => ("x", "")
  if ip.isEmpty && fp.isEmpty then return none
  if !(ip.all Char.isDigit && fp.all Char.isDigit) then return none
  let digits := (ip ++ fp).foldl (fun n c => n * 10 + (c.toNat - 48)) 0
  let k := exp10 - fp.length
  let v := Float.ofScientific digits (k < 0) (if k < 0 then (-k).toNat else k.toNat)
  return some (if neg then -v else v)

end Clocrap.Num
