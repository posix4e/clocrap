import Clocrap.Function
import Clocrap.Lex

/-!
# C and Objective-C

Functions are function definitions, and in Objective-C also method definitions, which are named
by their selector (`-tap:at:`, `+shared`). A block (`^{ … }`) belongs to the function around it.
Preprocessor lines are not code: their conditions do not count, and the code in every branch of an
`#if` does.

Decisions are every `if`, `for`, `while`, `do` (its closing `while` is part of it), `?:`,
`@catch`, `case` (not `default`), `&&` and `||`.
-/

namespace Clocrap.CLang

open Lex

/-- The tokens outside preprocessor lines, and the `&&` and `||` of `#if` and `#elif` conditions,
which tree-sitter parses as expressions. A directive runs to the end of its line and on through
lines that end in a backslash. -/
def code (s : ByteArray) (ts : Array Tok) : Array Tok × Array Tok := Id.run do
  let mut out := #[]
  let mut conditions := #[]
  let mut directive := false
  let mut condition := false
  for h : n in [0:ts.size] do
    let t := ts[n]
    if t.first then
      let continued := directive && n > 0 && Id.run do
        let p := ts[n - 1]!
        let mut k := p.stop
        while k < t.start do
          if byteAt s k == 92 && (byteAt s (k + 1) == 10 ||
              (byteAt s (k + 1) == 13 && byteAt s (k + 2) == 10)) then return true
          k := k + 1
        return false
      if !continued then
        directive := t.is "#"
        condition := directive && (ts[n + 1]?.any fun d => d.isId "if" || d.isId "elif")
    if !directive then out := out.push t
    else if condition && (t.is "&&" || t.is "||") then conditions := conditions.push t
  return (out, conditions)

/-- Words that read like a call but are part of a declaration, not its name. -/
def attributeWords : Array String :=
  #["__attribute__", "__attribute", "__declspec", "__asm__", "__asm", "asm", "alignas", "_Alignas",
    "__typeof__", "typeof", "_Static_assert", "static_assert"]

/-- The name of the function whose body opens at `brace`, from the declaration that runs from
`first`: the name before the last parameter list outside brackets. A macro that takes a selector,
as React Native's `RCT_EXPORT_METHOD(run:(id)x rejecter:(id)reject)` does, is read by tree-sitter
as a declarator named by its last word. -/
def cName (ts : Array Tok) (m : Array Nat) (first brace : Nat) : Option String := Id.run do
  let mut name := none
  let mut i := first
  while i < brace do
    let t := ts[i]!
    if t.is "(" || t.is "[" then
      if t.is "(" && i > first && ts[i - 1]!.kind == .ident &&
          !attributeWords.contains ts[i - 1]!.text then
        let close := m[i]!
        let selector := Id.run do
          let mut k := i + 1
          while k < close do
            if ts[k]!.is ":" then return true
            k := if ts[k]!.is "(" || ts[k]!.is "[" then m[k]! + 1 else k + 1
          return false
        name := some (if selector && ts[close - 1]!.kind == .ident then ts[close - 1]!.text
          else ts[i - 1]!.text)
      i := m[i]! + 1
    else i := i + 1
  return name

/-- Whether the declaration from `first` up to the brace at `brace` is a function's: it has a
parameter list, and is not a type, an initializer or a `typedef`. -/
def isFunction (ts : Array Tok) (m : Array Nat) (first brace : Nat) : Bool := Id.run do
  if brace == first then return false
  let before := ts[brace - 1]!
  if (brace ≥ first + 2 && (ts[brace - 2]!.isId "struct" || ts[brace - 2]!.isId "union" ||
      ts[brace - 2]!.isId "enum")) || before.isId "struct" || before.isId "union" ||
      before.isId "enum" then return false
  let mut i := first
  let mut call := false
  while i < brace do
    let t := ts[i]!
    if t.isId "typedef" || t.is "=" || (t.kind == .ident && t.text.startsWith "@") then
      return false
    if t.is "(" || t.is "[" then
      if t.is "(" && i > first && ts[i - 1]!.kind == .ident &&
          !attributeWords.contains ts[i - 1]!.text then call := true
      i := m[i]! + 1
    else i := i + 1
  return call

/-- An Objective-C method's selector, from its `-` or `+` at `first` to its body at `brace`. -/
def selector (ts : Array Tok) (m : Array Nat) (first brace : Nat) : String := Id.run do
  let mut out := ts[first]!.text
  let mut i := first + 1
  let skipType (i : Nat) : Nat := if i < brace && ts[i]!.is "(" then m[i]! + 1 else i
  i := skipType i
  let mut args := false
  while i < brace do
    let t := ts[i]!
    if t.kind == .ident && i + 1 < brace && ts[i + 1]!.is ":" then
      if args then out := out ++ ":"
      out := out ++ t.text
      args := true
      i := skipType (i + 2)
      if i < brace && ts[i]!.kind == .ident then i := i + 1
    else if t.is ":" then
      args := true
      i := skipType (i + 1)
      if i < brace && ts[i]!.kind == .ident then i := i + 1
    else if t.kind == .ident && !args then
      out := out ++ t.text
      i := i + 1
    else break
  return if args then out ++ ":" else out

/-- 1 plus the decisions between token `lo` and token `hi`. -/
def complexity (ts : Array Tok) (m : Array Nat) (lo hi : Nat) : Int := Id.run do
  let o := openers m
  let mut total : Int := 1
  for i in [lo:hi + 1] do
    let t := ts[i]!
    if t.kind == .ident then
      match t.text with
      | "if" | "for" | "do" | "case" | "@catch" => total := total + 1
      | "while" =>
        -- `do { … } while (…)`: the `while` closes the `do`.
        let closesDo := i > 0 && ts[i - 1]!.is "}" && o[i - 1]! > 0 && ts[o[i - 1]! - 1]!.isId "do"
        if !closesDo then total := total + 1
      | _ => pure ()
    else if t.kind == .punct && (t.text == "?" || t.text == "&&" || t.text == "||") then
      total := total + 1
  return total

def functions (s : ByteArray) : Array Function := Id.run do
  let (ts, conditions) := code s (tokens .c s)
  if ts.isEmpty then return #[]
  let m := matching ts
  let mut found : Array Found := #[]
  -- The first token of the declaration being read.
  let mut first := 0
  -- Methods are only read between `@implementation` and `@end`.
  let mut inImplementation := false
  let mut i := 0
  while i < ts.size do
    let t := ts[i]!
    if t.is ";" then
      i := i + 1
      first := i
    else if t.is "}" then
      -- The end of an `extern "C" { … }` block.
      i := i + 1
      first := i
    else if (t.is "-" || t.is "+") && t.first && ts[first]!.text.startsWith "@" then
      -- A method after `@implementation Name`, which has no `;`.
      first := i
      i := i + 1
    else if t.kind == .ident && (t.text == "@implementation" || t.text == "@interface" ||
        t.text == "@protocol" || t.text == "@end") then
      first := i
      i := i + 1
      if t.text == "@end" then first := i
      inImplementation := t.text == "@implementation"
    else if t.is "(" || t.is "[" then
      i := m[i]! + 1
    else if t.is "{" then
      let close := m[i]!
      if i == first + 2 && ts[first]!.isId "extern" && ts[first + 1]!.kind == .str then
        -- A linkage block: what is inside is declarations as at the top.
        i := i + 1
        first := i
      else if inImplementation && (ts[first]!.is "-" || ts[first]!.is "+") then
        found := found.push { name := selector ts m first i, first, last := close, complexity := complexity ts m first close }
        i := close + 1
        first := i
      else if isFunction ts m first i then
        found := found.push { name := (cName ts m first i).getD "<anonymous>", first, last := close,
                              complexity := complexity ts m first close }
        i := close + 1
        first := i
      else
        -- A struct, union, enum or initializer: the declaration goes on to its `;`. An
        -- `@implementation`'s instance variables end it.
        i := close + 1
        if ts[first]!.text.startsWith "@" then first := i
    else i := i + 1
  let scored := found.map fun f =>
    let lo := ts[f.first]!.start
    let hi := ts[f.last]!.stop
    { f with complexity := f.complexity + (conditions.filter fun c => lo ≤ c.start && c.stop ≤ hi).size }
  return treeOrder ts scored

end Clocrap.CLang
