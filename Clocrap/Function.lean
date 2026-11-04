/-!
# Functions

One function found in a source file, with the measures clocrap reports for it.
-/

namespace Clocrap

/-- A Lean declaration's full name, as the compiler knows it. -/
structure Symbol where
  /-- The name with its namespaces, such as `WinnowApp.Main.trace`. -/
  name : String
  /-- Whether it is `private`, which puts the module's name into the C name. -/
  private_ : Bool
  /-- Whether the compiler may copy its body into its callers instead of calling it: `@[inline]`,
  `@[macro_inline]`, `@[always_inline]`, `@[specialize]`, an `abbrev`, or a body that is one
  application of names (Lean inlines definitions that small on its own). -/
  inline : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- One function found in a source file. -/
structure Function where
  name : String
  /-- 1-based first line of the function. -/
  startLine : Nat
  /-- 1-based last line of the function. -/
  endLine : Nat
  complexity : Nat
  /-- The name the compiler gives the function, when coverage is matched by symbol rather than by
  line. Lean only: its coverage comes from the C it compiles to. -/
  symbol : Option Symbol := none
  deriving DecidableEq, Repr, Inhabited

end Clocrap
