import Clocrap.Num

/-!
# JSON

Just enough JSON to print the reports the way `serde_json::to_writer_pretty` did: keys sorted,
two-space indents, floats in their shortest form.
-/

namespace Clocrap

inductive Json where
  | null
  | bool (b : Bool)
  | nat (n : Nat)
  | float (x : Float)
  | str (s : String)
  | arr (items : Array Json)
  | obj (fields : Array (String × Json))
  deriving Inhabited

namespace Json

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n]!

/-- A string literal, escaped as serde_json escapes it. -/
def quote (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := match c with
      | '"' => out ++ "\\\""
      | '\\' => out ++ "\\\\"
      | '\n' => out ++ "\\n"
      | '\r' => out ++ "\\r"
      | '\t' => out ++ "\\t"
      | '\x08' => out ++ "\\b"
      | '\x0c' => out ++ "\\f"
      | c => if c.toNat < 0x20 then out ++ "\\u00" |>.push (hexDigit (c.toNat / 16)) |>.push (hexDigit (c.toNat % 16))
        else out.push c
  return out.push '"'

def option (f : α → Json) : Option α → Json
  | some a => f a
  | none => .null

partial def render (j : Json) (indent : Nat := 0) : String :=
  let pad (n : Nat) := String.ofList (List.replicate n ' ')
  match j with
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .nat n => toString n
  | .float x => Num.json x
  | .str s => quote s
  | .arr items =>
    if items.isEmpty then "[]"
    else
      let inner := items.toList.map fun i => pad (indent + 2) ++ render i (indent + 2)
      "[\n" ++ ",\n".intercalate inner ++ "\n" ++ pad indent ++ "]"
  | .obj fields =>
    if fields.isEmpty then "{}"
    else
      let sorted := fields.toList.mergeSort fun a b => a.1 ≤ b.1
      let inner := sorted.map fun (k, v) => pad (indent + 2) ++ quote k ++ ": " ++ render v (indent + 2)
      "{\n" ++ ",\n".intercalate inner ++ "\n" ++ pad indent ++ "}"

end Json
end Clocrap
