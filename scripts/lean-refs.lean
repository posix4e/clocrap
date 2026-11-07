/-
Prints which declarations of some compiled Lean modules use which others: one line per declaration,
its name and then the names it uses, separated by tabs. Theorems are left out, since nothing runs
them. The arguments are `.olean` files. `Clocrap/LeanRefs.lean` runs this with the project's own
`lean`, as only the toolchain that wrote an `.olean` can read it.

The modules are read one by one rather than imported, so two executables that each define `main`
do not clash.
-/
import Lean
open Lean

def plain (name : Name) : String := name.toString (escape := false)

def main (paths : List String) : IO Unit := do
  let mut modules := #[]
  for path in paths do
    -- A module-system file keeps its bodies apart from its public signatures.
    let whole := path ++ ".private"
    let (data, _) ← readModuleData (if ← System.FilePath.pathExists whole then whole else path)
    modules := modules.push data
  let out ← IO.getStdout
  for data in modules do
    for constant in data.constants do
      if constant matches .thmInfo _ then continue
      let name := constant.name
      -- A `partial def`'s value is only an inhabitant: what it runs is in `_unsafe_rec`.
      if let .str parent "_unsafe_rec" := name then
        out.putStrLn s!"{plain parent}\t{plain name}"
      let some value := constant.value? (allowOpaque := true) | continue
      -- All of them: a name from another project is only known once every project has been read.
      out.putStrLn ("\t".intercalate (plain name :: value.getUsedConstantsAsSet.toList.map plain))
