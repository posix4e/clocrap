import Clocrap.Lang
import Clocrap.Function
import Clocrap.LeanLang
import Clocrap.RustLang
import Clocrap.JsLang
import Clocrap.PyLang
import Clocrap.CLang

/-!
# Cyclomatic complexity

A function's complexity is 1 plus one for each decision point in its body: `if`, `while`, `for`,
`loop`, each `match` arm beyond the first, `&&`, `||`, `??`, `catch`, `except`, `case`, and the
ternary operator. Closures and lambdas are part of the function they sit in. A nested function is
scored on its own and does not add to the function that contains it.

The `?` operator, `try` and `else` are not decision points.

Each language has its own reader, built on tokens rather than a full grammar: Lean in
`Clocrap.LeanLang`, and the C family, Rust, Python and JavaScript/TypeScript in their own modules.
Swift is the exception. It is read by the compiler's own parser, as a batch, so `Clocrap.Walk`
calls `Clocrap.SwiftReader` itself.
-/

namespace Clocrap.Complexity

/-- Whether clocrap finds functions in a file of this language. -/
def supports (language : Language) (_path : String) : Bool :=
  match language with
  | .lean | .rust | .swift | .typeScript | .javaScript | .python | .c | .objectiveC => true
  | _ => false

/-- The functions in `source`, in source order. Empty for languages without a reader and for files
the reader cannot read, and empty for Swift, which `Clocrap.SwiftReader` reads. -/
def functions (language : Language) (path : String) (source : ByteArray) : Array Function :=
  -- TSX is its own grammar: `.ts` reads `<T>x` as a type assertion, `.tsx` as JSX.
  let tsx := path.toLower.endsWith ".tsx"
  match language with
  | .lean => LeanLang.functions source
  | .rust => RustLang.functions source
  | .typeScript => JsLang.functions source true tsx
  | .javaScript => JsLang.functions source false true
  | .python => PyLang.functions source
  | .c | .objectiveC => CLang.functions source
  | _ => #[]

end Clocrap.Complexity
