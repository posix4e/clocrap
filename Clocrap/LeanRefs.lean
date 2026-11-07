import Std.Data.HashMap
import Std.Data.HashSet
import Clocrap.Bytes
import Clocrap.LeanLang

/-!
# Who uses a Lean declaration

The compiler inlines freely, so the C says little about a declaration that nothing in it calls: the
code may have run inside a caller, or nothing may use it at all. Only the source can tell those
apart, and only after elaboration, since an instance or a coercion is used without being named: an
`.ilean` file has no reference from `x == y` to `instBEqT`. So the references here come from the
compiled modules themselves, read by `scripts/lean-refs.lean`.
-/

namespace Clocrap.LeanRefs

/-- The script, compiled into clocrap. -/
def script : String := include_str "../scripts/lean-refs.lean"

/-- The declarations of a project, by the name their C carries (see `key`), with those they use. -/
abbrev Uses := Std.HashMap String (Array String)

/-- A declaration's name as its C has it, without the package prefix. A private name is
`_private.<Module>.0.<name>`. -/
def key (name : String) : String :=
  match stripPrefix? name "_private." with
  | none => LeanLang.mangle name
  | some rest => match splitOnce? rest ".0." with
    | none => LeanLang.mangle name
    | some (module, inner) => s!"__private_{LeanLang.mangle module}_0__{LeanLang.mangle inner}"

/-- The script's output added to `uses`. A name can come twice: each executable has a `main`. -/
def addLines (uses : Uses) (printed : String) : Uses :=
  printed.splitOn "\n" |>.foldl (init := uses) fun uses line =>
    match line.splitOn "\t" with
    | name :: used =>
      if name.isEmpty then uses
      else
        let k := key name
        uses.insert k (uses.getD k #[] ++ (used.toArray.map key))
    | [] => uses

/-- The uses recorded in one project's `.olean` files, named relative to its root. `none`, said on
stderr, if they could not be read. -/
def readProject (script : System.FilePath) (root : String) (oleans : Array String) :
    IO (Option String) := do
  try
    -- `lean` here is elan's, which picks the project's toolchain from its working directory.
    let out ← IO.Process.output {
      cmd := "lean", args := #["--run", script.toString] ++ oleans, cwd := some root }
    if out.exitCode == 0 then return some out.stdout
    IO.eprintln s!"clocrap: could not read {root}'s compiled modules:\n{out.stdout}{out.stderr}"
    return none
  catch e =>
    IO.eprintln s!"clocrap: could not read {root}'s compiled modules: {e}"
    return none

/-- The uses recorded in the `.olean` files of each project, given as its root and the files
relative to it. `none` if any project's could not be read. -/
def read (projects : Array (String × Array String)) : IO (Option Uses) := do
  let (handle, file) ← IO.FS.createTempFile
  handle.putStr script
  handle.flush
  try
    let mut uses : Uses := {}
    for (root, oleans) in projects do
      let some printed ← readProject file root oleans | return none
      uses := addLines uses printed
    return some uses
  finally
    IO.FS.removeFile file

/-- Everything `roots` use, and they themselves. -/
partial def reached (uses : Uses) (roots : Array String) : Std.HashSet String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut todo := roots
  while !todo.isEmpty do
    let next := todo.back!
    todo := todo.pop
    if seen.contains next then continue
    seen := seen.insert next
    for used in uses.getD next #[] do
      if !seen.contains used then todo := todo.push used
  return seen

end Clocrap.LeanRefs
