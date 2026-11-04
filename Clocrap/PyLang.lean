import Clocrap.Function
import Clocrap.Lex

/-!
# Python

Functions are `def` and `async def` statements; a decorator is not part of the function, and a
lambda belongs to the function around it. A function with an indented body ends at its last
statement, or at a comment after it that is indented at least as far as the body: tree-sitter's
scanner keeps such comments in the block.

Decisions are every `if` (statements, conditional expressions, comprehension filters, case
guards), `elif`, `for` (loops and comprehensions), `while`, `except`, `and`, `or`, and each `case`
less one per `match`. Code inside f-strings counts.
-/

namespace Clocrap.PyLang

open Lex

/-- The width of the indentation that `s` has at `start`, counting a tab as 8, as tree-sitter's
scanner does. -/
def indentAt (s : ByteArray) (start : Nat) : Nat := Id.run do
  let mut w := 0
  let mut i := start
  while i < s.size do
    let b := byteAt s i
    if b == 32 then w := w + 1
    else if b == 9 then w := w + 8
    else if b == 12 then w := 0
    else break
    i := i + 1
  return w

/-- For each token, whether it starts a logical line: first on its line, outside brackets, and not
after a backslash continuation. -/
def logicalStarts (s : ByteArray) (ts : Array Tok) : Array Bool := Id.run do
  let mut out := Array.replicate ts.size false
  let mut depth : Int := 0
  for h : n in [0:ts.size] do
    let t := ts[n]
    if t.first && depth ≤ 0 then
      -- A backslash right before the line break joins the lines; one in a comment does not.
      let continued := n > 0 && Id.run do
        let p := ts[n - 1]!
        let mut k := p.stop
        while k < t.start do
          let c := byteAt s k
          if c == 35 then
            while k < t.start && byteAt s k != 10 do k := k + 1
          else if c == 92 && (byteAt s (k + 1) == 10 ||
              (byteAt s (k + 1) == 13 && byteAt s (k + 2) == 10)) then
            return true
          else k := k + 1
        return false
      if !continued then out := out.set! n true
    if t.kind == .punct then
      if t.text == "(" || t.text == "[" || t.text == "{" then depth := depth + 1
      else if t.text == ")" || t.text == "]" || t.text == "}" then depth := depth - 1
  return out

/-- The index of the last token of the logical line that starts at `i`. -/
def lineEnd (starts : Array Bool) (i : Nat) : Nat := Id.run do
  let mut j := i + 1
  while j < starts.size && !starts[j]! do j := j + 1
  return j - 1

def functions (s : ByteArray) : Array Function := Id.run do
  let ts := tokens .python s
  if ts.isEmpty then return #[]
  let m := matching ts
  let starts := logicalStarts s ts
  let lines := lineRanges s
  let indentOf (t : Tok) : Nat := indentAt s (lines[t.line - 1]!.1)
  -- Soft keywords: `match` and `case` lines that end in a colon.
  let mut weight : Array Int := Array.replicate ts.size 0
  for h : i in [0:ts.size] do
    let t := ts[i]
    if t.kind != .ident then continue
    match t.text with
    | "if" | "elif" | "for" | "while" | "except" | "and" | "or" => weight := weight.set! i 1
    | "match" | "case" =>
      if starts[i]! && (ts[i + 1]?.any fun n => !n.is "=" && !n.is "." && !n.is ":" &&
          !n.is "," && !n.is ")" && !(n.kind == .punct && n.text.endsWith "=" && n.text != "==")) then
        if ts[lineEnd starts i]!.is ":" then
          weight := weight.set! i (if t.text == "match" then -1 else 1)
    | _ => pure ()
  let mut found : Array Found := #[]
  for h : k in [0:ts.size] do
    if !ts[k].isId "def" then continue
    let some name := ts[k + 1]? | continue
    if name.kind != .ident then continue
    let first := if k > 0 && ts[k - 1]!.isId "async" && starts[k - 1]! then k - 1 else k
    -- The header's colon: the first one outside brackets after the name.
    let mut j := k + 2
    while j < ts.size && !ts[j]!.is ":" do
      if ts[j]!.is "(" || ts[j]!.is "[" || ts[j]!.is "{" then j := m[j]! + 1 else j := j + 1
    if j + 1 ≥ ts.size then continue
    let mut last := j
    if !starts[j + 1]! then
      -- `def f(): return 1`
      last := lineEnd starts j
    else
      let body := indentOf ts[j + 1]!
      if body ≤ indentOf ts[first]! then continue
      let mut b := j + 1
      while b < ts.size && !(starts[b]! && indentOf ts[b]! < body) do b := b + 1
      last := b - 1
    -- Comments after the body that are indented as far as it still belong to it.
    let mut endLine := ts[last]!.endLine
    if starts[j + 1]?.getD false then
      let body := indentOf ts[j + 1]!
      let mut line := endLine + 1
      while line ≤ lines.size do
        let (a, z) := lines[line - 1]!
        if allWs s a z then
          line := line + 1
          continue
        let w := indentAt s a
        let mut c := a
        while c < z && (byteAt s c == 32 || byteAt s c == 9 || byteAt s c == 12) do c := c + 1
        if byteAt s c != 35 || w < body then break
        endLine := line
        line := line + 1
    found := found.push { name := name.text, first, last, complexity := 0, endLine }
  let mut scored := #[]
  for h : n in [0:found.size] do
    let mut total : Int := 1
    for (lo, hi) in ownTokens found n do
      for i in [lo:hi] do total := total + weight[i]!
    scored := scored.push { found[n] with complexity := total }
  return treeOrder ts scored

end Clocrap.PyLang
