import Clocrap.Str
/-!
# Languages

The languages clocrap counts, the file extensions that select them, and the comment and string
syntax the line classifier needs for each one.
-/

namespace Clocrap

/-- The languages clocrap counts, in the order the README lists them. Reports group by this order. -/
inductive Language where
  | rust | toml | json | markdown | python | swift | typeScript | javaScript | kotlin | shell
  | yaml | c | html | css | lean | objectiveC
  deriving DecidableEq, Ord, Repr, Inhabited, Hashable

instance : LT Language := ltOfOrd
instance : BEq Language := ⟨fun a b => decide (a = b)⟩

/-- A block comment such as `/* ... */`. -/
structure BlockComment where
  opener : ByteArray
  closer : ByteArray
  /-- Whether a block comment may contain another one, as in Rust and Swift. -/
  nests : Bool
  deriving Inhabited

/-- A string literal. Code inside a string is code, so a comment marker inside one does not start a
comment. -/
structure StringSyntax where
  opener : ByteArray
  closer : ByteArray
  /-- Whether a backslash escapes the next byte inside the string. -/
  escapes : Bool
  /-- Whether the string may run across lines. -/
  multiline : Bool
  deriving Inhabited

/-- How one language marks comments and strings. -/
structure Syntax where
  lineComments : Array ByteArray
  block : Option BlockComment
  /-- Longer openers come first, so `"""` is tried before `"`. -/
  strings : Array StringSyntax
  /-- Whether `'x'` and `'\n'` are character literals. Rust and Kotlin need this, because a
  lifetime such as `'a` must not open a string. -/
  charLiterals : Bool
  deriving Inhabited

namespace Syntax

private def str (o c : String) (escapes multiline : Bool) : StringSyntax :=
  ⟨o.toUTF8, c.toUTF8, escapes, multiline⟩

def dq := str "\"" "\"" true false
def sq := str "'" "'" false false
def sqEsc := str "'" "'" true false
def tripleDq := str "\"\"\"" "\"\"\"" true true
def tripleSq := str "'''" "'''" true true
def backtick := str "`" "`" true true
/-- TOML literal strings: `'''` never processes escapes. -/
def tripleSqLiteral := str "'''" "'''" false true
/-- Kotlin raw strings: `"""` has no escapes. -/
def tripleDqRaw := str "\"\"\"" "\"\"\"" false true

def cBlock : BlockComment := ⟨"/*".toUTF8, "*/".toUTF8, false⟩
def nestedCBlock : BlockComment := ⟨"/*".toUTF8, "*/".toUTF8, true⟩
def htmlBlock : BlockComment := ⟨"<!--".toUTF8, "-->".toUTF8, false⟩
/-- Lean's block comment, which nests; doc comments and module docs are block comments too. -/
def leanBlock : BlockComment := ⟨"/-".toUTF8, "-/".toUTF8, true⟩

def slash := #["//".toUTF8]
def hash := #["#".toUTF8]
def dash := #["--".toUTF8]

def rustStrings : Array StringSyntax :=
  #[str "r##\"" "\"##" false true, str "r#\"" "\"#" false true, str "r\"" "\"" false true, dq]

/-- Lean's raw strings have no escapes; plain strings may span lines. -/
def leanStrings : Array StringSyntax :=
  #[str "r##\"" "\"##" false true, str "r#\"" "\"#" false true, str "r\"" "\"" false true,
    str "\"" "\"" true true]

end Syntax

namespace Language

/-- Every language, in the order they are documented. -/
def all : Array Language :=
  #[.rust, .toml, .json, .markdown, .python, .swift, .typeScript, .javaScript, .kotlin, .shell,
    .yaml, .c, .html, .css, .lean, .objectiveC]

/-- The name printed in reports. -/
def name : Language → String
  | .rust => "Rust" | .toml => "TOML" | .json => "JSON" | .markdown => "Markdown"
  | .python => "Python" | .swift => "Swift" | .typeScript => "TypeScript"
  | .javaScript => "JavaScript" | .kotlin => "Kotlin" | .shell => "Shell" | .yaml => "YAML"
  | .c => "C" | .html => "HTML" | .css => "CSS" | .lean => "Lean" | .objectiveC => "Objective-C"

/-- The language a file extension selects, matched case-insensitively. -/
def fromExtension (extension : String) : Option Language :=
  match extension.toLower with
  | "rs" => some .rust
  | "toml" => some .toml
  | "json" | "jsonl" | "ndjson" => some .json
  | "md" | "markdown" => some .markdown
  | "py" => some .python
  | "swift" => some .swift
  | "ts" | "tsx" | "mts" | "cts" => some .typeScript
  | "js" | "jsx" | "mjs" | "cjs" => some .javaScript
  | "kt" | "kts" => some .kotlin
  | "sh" | "bash" | "zsh" => some .shell
  | "yml" | "yaml" => some .yaml
  | "c" | "h" => some .c
  | "html" | "htm" => some .html
  | "css" => some .css
  | "lean" => some .lean
  | "m" | "mm" => some .objectiveC
  | _ => none

/-- Rust's `char::is_whitespace`, which `str::split_whitespace` splits on. -/
def isUnicodeSpace (c : Char) : Bool :=
  let v := c.toNat
  (9 ≤ v && v ≤ 13) || v == 32 || v == 0x85 || v == 0xA0 || v == 0x1680 ||
    (0x2000 ≤ v && v ≤ 0x200A) || v == 0x2028 || v == 0x2029 || v == 0x202F || v == 0x205F ||
    v == 0x3000

/-- The language a `#!` first line names, for a file with no extension: Python, the POSIX shells
and Node, by path or through `env` (whose options, such as `-S`, are skipped). Version suffixes
such as `python3.12` select the same language. -/
def fromShebang (firstLine : ByteArray) : Option Language := do
  guard (firstLine.size ≥ 2 && firstLine[0]! == 35 && firstLine[1]! == 33)
  let text ← String.fromUTF8? (firstLine.extract 2 firstLine.size)
  let words := (text.toList.splitBy (fun a b => isUnicodeSpace a == isUnicodeSpace b)).filterMap
    fun w => if w.any isUnicodeSpace then none else some (String.ofList w)
  let last (w : String) : String := (w.splitOn "/").getLast!
  let first ← words.head?
  let mut program := last first
  if program == "env" then
    let found ← (words.drop 1).find? fun w => !w.startsWith "-" && !w.contains '='
    program := last found
  let name := program.dropRightWhile fun c => c.isDigit || c == '.'
  match name with
  | "python" => some .python
  | "sh" | "bash" | "zsh" | "dash" | "ksh" => some .shell
  | "node" => some .javaScript
  | _ => none

/-- The comment and string syntax the line classifier uses. -/
def lexSyntax : Language → Syntax
  | .rust => ⟨Syntax.slash, some Syntax.nestedCBlock, Syntax.rustStrings, true⟩
  | .toml => ⟨Syntax.hash, none, #[Syntax.tripleDq, Syntax.tripleSqLiteral, Syntax.dq, Syntax.sq], false⟩
  | .json => ⟨#[], none, #[Syntax.dq], false⟩
  -- cloc's convention: prose has no comments, so every non-blank line is code.
  | .markdown => ⟨#[], none, #[], false⟩
  | .python => ⟨Syntax.hash, none, #[Syntax.tripleDq, Syntax.tripleSq, Syntax.dq, Syntax.sqEsc], false⟩
  | .swift => ⟨Syntax.slash, some Syntax.nestedCBlock, #[Syntax.tripleDq, Syntax.dq], false⟩
  | .typeScript | .javaScript =>
    ⟨Syntax.slash, some Syntax.cBlock, #[Syntax.dq, Syntax.sqEsc, Syntax.backtick], false⟩
  | .kotlin => ⟨Syntax.slash, some Syntax.nestedCBlock, #[Syntax.tripleDqRaw, Syntax.dq], true⟩
  | .shell | .yaml => ⟨Syntax.hash, none, #[Syntax.dq, Syntax.sq], false⟩
  | .c | .objectiveC => ⟨Syntax.slash, some Syntax.cBlock, #[Syntax.dq], true⟩
  -- Markup has no strings the classifier must respect: text between tags is prose, so a quote
  -- in it must not open a string.
  | .html => ⟨#[], some Syntax.htmlBlock, #[], false⟩
  | .css => ⟨#[], some Syntax.cBlock, #[Syntax.dq, Syntax.sqEsc], false⟩
  -- `'a'` is a character literal. The prime in a name such as `x'` is not, since no single
  -- character and closing quote follow it.
  | .lean => ⟨Syntax.dash, some Syntax.leanBlock, Syntax.leanStrings, true⟩

end Language

end Clocrap
