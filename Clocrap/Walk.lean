import Clocrap.Count
import Clocrap.Function
import Clocrap.Vcs
import Clocrap.Gitignore
import Clocrap.Diff
import Clocrap.Complexity
import Clocrap.SwiftReader
import Clocrap.LeanLang

/-!
# Scanning

Finds the files under each root, then reads, classifies and counts them on worker threads.
-/

namespace Clocrap

/-- Bytes read when looking for a NUL, the usual sign of a binary file. -/
def binaryProbe : Nat := 8000

/-- The counts for one source file. -/
structure FileReport where
  /-- The path as the walk found it, under one of the roots. -/
  path : String
  language : Language
  counts : LineCounts
  /-- The functions in the file, when the scan asked for them. In diff mode, only the functions
  that contain a changed line. -/
  functions : Array Function
  deriving Inhabited

/-- Where the list of files to count comes from. -/
inductive Listing where
  /-- The files git would commit: tracked files, plus untracked files that git does not ignore. A
  root that is not in a git repository is walked. -/
  | vcs
  /-- Every file under the roots, found by walking the directories. Hidden files are skipped and
  `.gitignore` is honoured, with or without git. -/
  | walk
  deriving DecidableEq

/-- What a scan should count. -/
structure ScanOptions where
  listing : Listing := .vcs
  /-- When set, only the lines in here are counted, and a file with none of them is left out. -/
  changed : Option Diff.ChangedLines := none
  /-- Whether to find each file's functions. -/
  functions : Bool := false
  /-- Worker threads that read and count files. Zero picks `defaultThreads`. -/
  threads : Nat := 0

/-- Workers used when the caller does not say. File opens contend in the kernel past about four
threads on macOS, so more workers make the scan slower, not faster (see the README). -/
def defaultThreads : Nat := 4

/-- Files handed to a worker at a time. -/
def chunk : Nat := 64

/-- A file's extension as Rust's `Path::extension` reads it: `.bashrc` has none, `a.` has an empty
one. -/
def extensionOf (path : String) : Option String :=
  let name := (path.splitOn "/").getLast!
  if name == ".." then none
  else match name.splitOn "." with
    | [] | [_] => none
    | parts =>
      let before := String.intercalate "." parts.dropLast
      if before.isEmpty then none else some parts.getLast!

/-- Whether the path has an extension clocrap knows, or none at all: a file without one is read
and kept only if its `#!` line names a language. -/
def recognised (path : String) : Bool :=
  match extensionOf path with
  | none => true
  | some e => (Language.fromExtension e).isSome

/-- Every file under `root` that the ignore files allow, found by walking. -/
partial def walkRoot (root : String) (globalM : Option Gitignore.Matcher) : IO (Array String) := do
  if !(← System.FilePath.isDir root) then return #[root]
  -- The ignore files of the directories above the root apply too.
  let mut parents : Array Gitignore.Level := #[]
  let parts := (root.splitOn "/").filter (· ≠ "")
  for k in [0:parts.length] do
    let dir := "/" ++ String.intercalate "/" (parts.take k)
    parents := parents.push (← Gitignore.Level.read dir)
  let rec go (dir : String) (levels : Array Gitignore.Level) (acc : Array String) :
      IO (Array String) := do
    let levels := levels.push (← Gitignore.Level.read dir)
    let entries ← try (System.FilePath.readDir dir) catch e => do
      IO.eprintln s!"clocrap: {e}"
      pure #[]
    let mut acc := acc
    for entry in entries do
      let path := entry.path.toString
      let kind ← try pure (some (← entry.path.symlinkMetadata).type) catch _ => pure none
      let isDir := kind == some .dir
      let hidden := entry.fileName.startsWith "."
      let decided := Gitignore.decide levels globalM path isDir
      let skip := match decided with
        | some ignored => ignored
        | none => hidden
      if skip then continue
      if isDir then acc ← go path levels acc
      else if kind == some .file && recognised path then acc := acc.push path
    return acc
  go root parents #[]

/-- The functions that hold a changed line, or all of them outside diff mode. -/
def changedOnly (change : Option Diff.FileChange) (functions : Array Function) : Array Function :=
  match change with
  | none => functions
  | some c => functions.filter fun f => Id.run do
    for line in [f.startLine:f.endLine + 1] do
      if c.contains line then return true
    return false

/-- Counts one file, or returns `none` if it is not a recognised text file or, in diff mode, has no
changed lines. -/
def scanFile (path : String) (options : ScanOptions) : IO (Option FileReport) := do
  let byExtension ← match extensionOf path with
    | some e => match Language.fromExtension e with
      | some l => pure (some l)
      | none => return none
    | none => pure none
  let change ← match options.changed with
    | some changed => match changed.get path with
      | some c => pure (some c)
      | none => return none
    | none => pure none
  let source ← try IO.FS.readBinFile path catch e => do
    IO.eprintln s!"clocrap: {path}: {e}"
    return none
  let probe := min source.size binaryProbe
  for k in [0:probe] do
    if source[k]! == 0 then return none
  let language ← match byExtension with
    | some l => pure l
    | none =>
      let mut firstEnd := source.size
      for k in [0:source.size] do
        if source[k]! == 10 then
          firstEnd := k
          break
      match Language.fromShebang (source.extract 0 firstEnd) with
      | some l => pure l
      | none => return none
  let kinds := match language with
    | .lean => (LeanLang.lineKinds source).getD (lineKinds source language.lexSyntax)
    | _ => lineKinds source language.lexSyntax
  let mut counts : LineCounts := {}
  for h : n in [0:kinds.size] do
    if change.all (·.contains (n + 1)) then counts := counts.record kinds[n]
  if change.isSome && counts.total == 0 then return none
  let functions := if options.functions then Complexity.functions language path source else #[]
  return some { path, language, counts, functions := changedOnly change functions }

/-- Reports with their Swift functions filled in. Swift is read apart from the other languages, in
one run of the Swift reader for all its files. -/
def withSwiftFunctions (reports : Array FileReport) (options : ScanOptions) :
    IO (Array FileReport) := do
  let swift := reports.filter (·.language == .swift)
  if !options.functions || swift.isEmpty then return reports
  let some found ← SwiftReader.functions (swift.map (·.path)) | do
    IO.eprintln "clocrap: no Swift toolchain found, so Swift functions are not scored"
    return reports
  let mut byPath : Std.HashMap String (Array Function) := {}
  for h : k in [0:swift.size] do
    let path := swift[k].path
    let change := options.changed.bind (·.get path)
    byPath := byPath.insert path (changedOnly change found[k]!)
  return reports.map fun r =>
    if r.language == .swift then { r with functions := byPath.getD r.path #[] } else r

/-- Counts every recognised source file under every root.

By default the files are the ones git lists (see `Vcs.filesUnder`): the tracked files and the
untracked files that git does not ignore. A root that is not inside a git repository is walked
instead, and with `.walk` every root is. A walk skips hidden files and directories and honours
`.gitignore` files even outside a git repository. The result is sorted by path, so the output does
not depend on thread scheduling. -/
def scan (roots : Array String) (options : ScanOptions) : IO (Array FileReport) := do
  let mut canonical := #[]
  for root in roots do
    try canonical := canonical.push (← IO.FS.realPath root).toString
    catch e => throw <| IO.userError s!"{root}: {e}"
  let mut paths : Array String := #[]
  let mut walked := #[]
  for root in canonical do
    if options.listing == .vcs then
      if let some files ← Vcs.filesUnder root then
        paths := paths ++ (files.map (·.toString)).filter recognised
        continue
    walked := walked.push root
  if !walked.isEmpty then
    let globalM ← Gitignore.global (← IO.currentDir).toString
    for root in walked do
      paths := paths ++ (← walkRoot root globalM)
  -- Roots can overlap, and git can list a path twice.
  let keyed := paths.map fun p => (pathKey p, p)
  let sorted := (keyed.toList.mergeSort (fun a b => !(b.1 < a.1))).toArray.map (·.2)
  let unique := sorted.foldl (init := #[]) fun acc p => if acc.back? == some p then acc else acc.push p
  let threads := if options.threads == 0 then defaultThreads else options.threads
  let next ← IO.mkRef 0
  let worker : IO (Array FileReport) := do
    let mut found := #[]
    repeat
      let start ← next.modifyGet fun n => (n, n + chunk)
      if start ≥ unique.size then break
      for k in [start:min unique.size (start + chunk)] do
        if let some report ← scanFile unique[k]! options then found := found.push report
    return found
  let tasks ← (List.range threads).mapM fun _ => IO.asTask (prio := .dedicated) worker
  let mut reports := #[]
  for t in tasks do
    match ← IO.wait t with
    | .ok found => reports := reports ++ found
    | .error e => throw e
  reports ← withSwiftFunctions reports options
  let keyed := reports.map fun r => (pathKey r.path, r)
  return (keyed.toList.mergeSort (fun a b => !(b.1 < a.1))).toArray.map (·.2)

end Clocrap
