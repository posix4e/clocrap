import Clocrap.Str
/-!
# The files git would commit

Tracked files, plus untracked files that git does not ignore. This is the default list of files to
count.
-/

namespace Clocrap.Vcs

/-- Runs git, or returns `none` when git cannot be started at all (it is not installed). -/
def runGit (args : Array String) : IO (Option IO.Process.Output) := do
  try
    return some (← IO.Process.output { cmd := "git", args })
  catch
    | .noFileOrDirectory .. => return none
    | e => throw e

/-- Whether `path` is a plain file, not a symlink, directory or submodule. -/
def isPlainFile (path : System.FilePath) : IO Bool := do
  try
    return (← path.symlinkMetadata).type == .file
  catch _ => return false

/-- A pathspec that matches the named file and nothing else, whatever characters its name holds. -/
def literalPathspec (name : String) : String := s!":(literal){name}"

/-- The files git lists under `root`, as paths under `root`: every tracked file and every untracked
file that `.gitignore` and the other standard ignore files do not exclude. Hidden files are included
when git lists them. A tracked file that has been deleted from the working tree is left out, and so
is anything that is not a plain file, such as a symlink or a submodule.

`root` may be a directory or a single file. Returns `none` when `root` is not inside a git
repository, or when git is not installed, so the caller can fall back to walking the directory.
Throws if git runs and fails for any other reason, so that a repository git refuses to read is not
silently counted as a plain tree. -/
def filesUnder (root : System.FilePath) : IO (Option (Array System.FilePath)) := do
  let (dir, only) ← if ← root.isDir then pure (root, none) else
    match root.parent, root.fileName with
    | some parent, some name => pure (parent, some name)
    | _, _ => return none
  let mut args := #["-C", dir.toString, "ls-files", "-z", "--cached", "--others", "--exclude-standard"]
  if let some name := only then args := args ++ #["--", literalPathspec name]
  let some out ← runGit args | return none
  if out.exitCode != 0 then
    if out.stderr.contains "not a git repository" then return none
    throw <| IO.userError s!"git ls-files failed in {dir}: {out.stderr.trimS}"
  let mut files := #[]
  for name in out.stdout.splitOn "\x00" do
    if name.isEmpty then continue
    let path := dir / name
    if ← isPlainFile path then files := files.push path
  return some files

end Clocrap.Vcs
