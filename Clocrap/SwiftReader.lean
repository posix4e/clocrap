import Clocrap.Function

/-!
# Swift

Swift's functions come from SwiftSyntax, the parser the compiler itself uses, rather than from a
reader of clocrap's own. Every Swift toolchain carries a built copy, so reading Swift takes no
download. `SwiftReader.swift` is compiled against that copy the first time it is needed, and kept
in the cache directory under a name that depends on its source and on the toolchain, so a new
toolchain gets a new build. It reads every Swift file of a scan in one run.

A function is a `func`, `init` or `deinit` with a body, a getter written as a `var`'s or a
`subscript`'s braces, and an accessor with a body, which is named `value.set`. A declaration starts
at its first attribute or modifier. Closures belong to the function around them.

Decisions are `if`, `guard`, `for`, `while`, `repeat`, each `catch`, each switch entry less one per
`switch`, the ternary operator, `&&`, `||` and `??`. Code inside a string's `\(…)` counts; a `#if`
line's condition does not, and both branches of a `#if` do.
-/

namespace Clocrap.SwiftReader

/-- The reader's source, compiled into clocrap. -/
def source : String := include_str "SwiftReader.swift"

/-- The lines a command prints, or `none` if it cannot run or fails. -/
def outputOf (cmd : String) (args : Array String) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd, args }
    return if out.exitCode == 0 then some out.stdout else none
  catch _ => return none

/-- The Swift compiler in use. On macOS `swiftc` on the path is a shim, and `xcrun` knows the real
one, whose folder holds the libraries. -/
def compiler : IO (Option System.FilePath) := do
  if let some found ← outputOf "xcrun" #["--find", "swiftc"] then
    return some found.trimAscii.toString
  let some found ← outputOf "which" #["swiftc"] | return none
  try return some (← IO.FS.realPath found.trimAscii.toString) catch _ => return none

def cacheDir : IO System.FilePath := do
  if let some dir ← IO.getEnv "XDG_CACHE_HOME" then return dir ++ "/clocrap"
  let home := (← IO.getEnv "HOME").getD "."
  return home ++ "/.cache/clocrap"

/-- The built reader, compiling it if this source and toolchain have not been built yet. `none`
when there is no Swift toolchain to build it with. -/
def built : IO (Option System.FilePath) := do
  let some swiftc ← compiler | return none
  let some version ← outputOf swiftc.toString #["--version"] | return none
  let dir ← cacheDir
  let name := s!"swift-reader-{(hash (source ++ version)).toNat}"
  let binary := dir / name
  if ← binary.pathExists then return some binary
  let some bin := swiftc.parent | return none
  let some usr := bin.parent | return none
  let host := (usr / "lib" / "swift" / "host").toString
  IO.FS.createDirAll dir
  -- Named for its process so that two scans at once cannot build over each other.
  let building := dir / s!"{name}.{← IO.Process.getPID}"
  IO.FS.createDirAll building
  let file := building / "main.swift"
  IO.FS.writeFile file source
  let output := building / "reader"
  -- Run by its full path, the macOS compiler is not told where the SDK is.
  let sdk := match ← outputOf "xcrun" #["--show-sdk-path"] with
    | some path => #["-sdk", path.trimAscii.toString]
    | none => #[]
  let out ← IO.Process.output {
    cmd := swiftc.toString
    args := sdk ++ #["-O", "-I", host, "-L", host, "-lSwiftSyntax", "-lSwiftParser", "-Xlinker", "-rpath",
      "-Xlinker", host, file.toString, "-o", output.toString] }
  if out.exitCode != 0 then
    IO.FS.removeDirAll building
    throw <| IO.userError s!"could not build the Swift reader:\n{out.stderr}"
  IO.FS.rename output binary
  IO.FS.removeDirAll building
  return some binary

/-- One line of the reader's output: the index of the path, and the function. -/
def parseLine (line : String) : Option (Nat × Function) :=
  match line.splitOn "\t" with
  | [index, first, last, complexity, name] => do
    return (← index.toNat?, { name, startLine := ← first.toNat?, endLine := ← last.toNat?,
                              complexity := ← complexity.toNat? })
  | _ => none

/-- Hands `paths` to the reader. Dropping `stdin` at the end closes it, which starts the reader. -/
def send (stdin : IO.FS.Handle) (paths : Array String) : IO Unit := do
  for path in paths do
    stdin.putStr path
    stdin.write (ByteArray.mk #[0])
  stdin.flush

/-- The functions in each of `paths`, in source order. `none` when there is no Swift toolchain. -/
def functions (paths : Array String) : IO (Option (Array (Array Function))) := do
  if paths.isEmpty then return some #[]
  let some reader ← built | return none
  let child ← IO.Process.spawn {
    cmd := reader.toString, stdin := .piped, stdout := .piped, stderr := .inherit }
  let (stdin, child) ← child.takeStdin
  send stdin paths
  let printed ← child.stdout.readToEnd
  let code ← child.wait
  if code != 0 then throw <| IO.userError s!"the Swift reader failed with code {code}"
  let mut found := Array.replicate paths.size #[]
  for line in printed.splitOn "\n" do
    if line.isEmpty then continue
    let some (index, function) := parseLine line
      | throw <| IO.userError s!"the Swift reader printed {line.quote}"
    found := found.modify index (·.push function)
  return some found

end Clocrap.SwiftReader
