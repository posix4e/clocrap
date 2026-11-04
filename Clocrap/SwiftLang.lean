import Clocrap.Function
import Clocrap.Lex

/-!
# Swift

Functions are `func` declarations with a body and `init` declarations, with or without one (a
protocol's `init()` is one, its `func`s are not). Accessors, `deinit` and `subscript` are not
functions; closures belong to the function around them. A declaration starts at its first
attribute or modifier.

Decisions are `if`, `guard`, `for`, `while`, `repeat … while`, each `catch`, each switch entry less
one per `switch`, `&&` and `||`. The ternary operator and `??` are not. Code inside a string's
`\(…)` counts; a `#if` line's condition does not, but both branches of a `#if` do.
-/

namespace Clocrap.SwiftLang

open Lex

def modifiers : Array String := #[
  "public", "private", "fileprivate", "internal", "open", "package", "static", "class", "final",
  "override", "mutating", "nonmutating", "convenience", "required", "dynamic", "optional",
  "nonisolated", "isolated", "distributed", "indirect", "lazy", "weak", "unowned", "prefix",
  "postfix", "infix", "consuming", "borrowing", "__consuming"]

/-- Words that start a new declaration or statement on a line of their own, so a signature that
reaches one has no body. -/
def declStarts : Array String := #[
  "func", "var", "let", "init", "subscript", "case", "static", "class", "struct", "enum",
  "protocol", "typealias", "associatedtype", "extension", "deinit", "public", "private",
  "fileprivate", "internal", "open", "mutating", "override", "nonisolated", "#if", "#else",
  "#elseif", "#endif", "@", "}", "import", "actor", "macro", "required", "convenience"]

/-- The first token of the declaration whose keyword is at `k`: attributes and modifiers before it
belong to it. -/
def declarationStart (ts : Array Tok) (o : Array Nat) (k : Nat) : Nat := Id.run do
  let mut first := k
  for _ in [0:k + 1] do
    if first == 0 then break
    let p := ts[first - 1]!
    if p.kind == .ident && modifiers.contains p.text then
      -- `class func` but not `class Foo {` … `func`: the token before is only a modifier when it
      -- directly precedes, which it does here.
      first := first - 1
    else if p.kind == .ident && first ≥ 2 && ts[first - 2]!.is "@" then first := first - 2
    else if p.is ")" then
      let op := o[first - 1]!
      -- `@available(…)`, `private(set)`, `nonisolated(unsafe)`.
      if op ≥ 1 && ts[op - 1]!.kind == .ident then
        if op ≥ 2 && ts[op - 2]!.is "@" then first := op - 2
        else if modifiers.contains ts[op - 1]!.text then first := op - 1
        else break
      else break
    else break
  return first

/-- Where a signature starting at `i` ends: `some (b, true)` with `b` its body's `{`, or
`some (last, false)` for one with no body, `last` its final token. -/
def signatureEnd (ts : Array Tok) (m : Array Nat) (i : Nat) : Option (Nat × Bool) := Id.run do
  let mut j := i
  let mut last := i
  let mut seenParams := false
  while j < ts.size do
    let t := ts[j]!
    if t.is "{" then return some (j, true)
    if seenParams && t.first && j > i && (declStarts.contains t.text) then return some (last, false)
    if t.is "}" || t.is ";" then return some (last, false)
    if t.is "(" || t.is "[" then
      seenParams := seenParams || t.is "("
      last := m[j]!
      j := m[j]! + 1
    else
      last := j
      j := j + 1
  return some (last, false)

/-- For each `switch`, its entries; and the `while` tokens that end a `repeat`. -/
structure Marks where
  entries : Array Nat
  repeatWhile : Array Bool
  /-- Tokens on a `#if` or `#elseif` line, which are not code. -/
  directive : Array Bool

def blockAfter (ts : Array Tok) (m : Array Nat) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  while j < ts.size do
    let t := ts[j]!
    if t.is "{" then return some j
    if t.is "}" || t.is ";" then return none
    if t.is "(" || t.is "[" then j := m[j]! + 1 else j := j + 1
  return none

def mark (ts : Array Tok) (m : Array Nat) : Marks := Id.run do
  let mut entries := Array.replicate ts.size 0
  let mut repeatWhile := Array.replicate ts.size false
  let mut directive := Array.replicate ts.size false
  for h : i in [0:ts.size] do
    let t := ts[i]
    if t.isId "#if" || t.isId "#elseif" then
      let mut j := i + 1
      while j < ts.size && ts[j]!.line == t.line do
        directive := directive.set! j true
        j := j + 1
    else if t.isId "repeat" then
      if ts[i + 1]?.any (·.is "{") then
        let close := m[i + 1]!
        if ts[close + 1]?.any (·.isId "while") then repeatWhile := repeatWhile.set! (close + 1) true
    else if t.isId "switch" then
      let some b := blockAfter ts m (i + 1) | continue
      let close := m[b]!
      let mut j := b + 1
      let mut count := 0
      while j < close do
        let u := ts[j]!
        if u.isId "default" && !ts[j - 1]!.is "." then count := count + 1
        else if u.isId "case" then
          let prev := ts[j - 1]!
          if !(prev.isId "if" || prev.isId "guard" || prev.isId "while" || prev.isId "for" ||
              prev.is ",") then count := count + 1
        if u.is "(" || u.is "[" || u.is "{" then j := m[j]! + 1 else j := j + 1
      entries := entries.set! i count
  return { entries, repeatWhile, directive }

/-- Whether the keyword at `i` is used as a name: an argument label (`for:`), a parameter's
external name (`(for record: T)`) or a member (`.for`). -/
def isName (ts : Array Tok) (i : Nat) : Bool :=
  let next (k : Nat) := ts[i + k]?
  let prev := if i > 0 then ts[i - 1]? else none
  (next 1).any (·.is ":") || prev.any (·.is ".") ||
    (prev.any (fun p => p.is "(" || p.is ",") && (next 1).any (·.kind == .ident) &&
      (next 2).any (·.is ":"))

def functions (s : ByteArray) : Array Function := Id.run do
  let ts := tokens .swift s
  if ts.isEmpty then return #[]
  let m := matching ts
  let o := openers m
  let marks := mark ts m
  let mut found : Array Found := #[]
  -- Operator names, which are not decisions.
  let mut names := Array.replicate ts.size false
  for h : k in [0:ts.size] do
    let t := ts[k]
    if t.isId "func" then
      let some n := ts[k + 1]? | continue
      let mut name := n.text
      let mut j := k + 2
      names := names.set! (k + 1) true
      -- An operator's name may be several symbols: `<=>`.
      if n.kind == .punct then
        while j < ts.size && ts[j]!.kind == .punct && ts[j]!.start == ts[j - 1]!.stop &&
            !ts[j]!.is "(" && !ts[j]!.is "<" do
          name := name ++ ts[j]!.text
          names := names.set! j true
          j := j + 1
      let some (e, hasBody) := signatureEnd ts m j | continue
      if !hasBody then continue
      found := found.push { name, first := declarationStart ts o k, last := m[e]!, complexity := 0 }
    else if t.isId "init" then
      if k > 0 && ts[k - 1]!.is "." then continue
      let some n := ts[k + 1]? | continue
      if !(n.is "(" || n.is "?" || n.is "!" || n.is "<") then continue
      let some (e, hasBody) := signatureEnd ts m (k + 1) | continue
      let last := if hasBody then m[e]! else e
      found := found.push { name := "init", first := declarationStart ts o k, last, complexity := 0 }
  let mut scored := #[]
  for h : n in [0:found.size] do
    let mut total : Int := 1
    for (lo, hi) in ownTokens found n do
      for i in [lo:hi] do
        let t := ts[i]!
        if marks.directive[i]! || names[i]! then continue
        match t.kind with
        | .ident =>
          if isName ts i then continue
          match t.text with
          | "if" =>
            -- tree-sitter reads `if case 1 = x` as something else, and so scores it as nothing.
            let literal := (ts[i + 1]?.any (·.isId "case")) && (ts[i + 2]?.any fun u =>
              u.kind == .num || u.kind == .str)
            if !literal then total := total + 1
          | "guard" | "for" | "repeat" | "catch" => total := total + 1
          | "while" => if !marks.repeatWhile[i]! then total := total + 1
          | "switch" => total := total - 1 + marks.entries[i]!
          | _ => pure ()
        | .punct => if t.text == "&&" || t.text == "||" then total := total + 1
        | _ => pure ()
    scored := scored.push { found[n] with complexity := total }
  return treeOrder ts scored

end Clocrap.SwiftLang
