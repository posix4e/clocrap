import Clocrap.Str
import Std.Data.HashMap

/-!
# `--diff <ref>`

The lines added or changed against a git ref, read from `git diff -U0`. Lines are only added or
changed when the diff says so, so a line that was merely moved or re-indented counts as changed.
-/

namespace Clocrap.Diff

/-- Which lines of one file a diff touched. -/
inductive FileChange where
  /-- A file untracked by git. Every line is new. -/
  | everything
  /-- 1-based inclusive ranges of added or changed lines in the new file. -/
  | lines (ranges : Array (Nat × Nat))
  deriving DecidableEq, Repr, Inhabited

/-- Whether the given 1-based line is in this change. -/
def FileChange.contains : FileChange → Nat → Bool
  | .everything, _ => true
  | .lines ranges, line => ranges.any fun (a, b) => a ≤ line && line ≤ b

/-- The changed lines of every file that a diff touched, keyed by absolute path. -/
structure ChangedLines where
  files : Std.HashMap String FileChange := {}

/-- The change to `path`, if the diff touched it. -/
def ChangedLines.get (c : ChangedLines) (path : String) : Option FileChange := c.files.get? path

def git (dir : String) (args : Array String) : IO String := do
  let out ← try IO.Process.output { cmd := "git", args := #["-C", dir] ++ args }
    catch e => throw <| IO.userError s!"cannot run git: {e}"
  if out.exitCode != 0 then
    throw <| IO.userError
      s!"git {args[0]?.getD ""} failed in {dir}: {(out.stderr.dropRightWhile Char.isWhitespace)}"
  return out.stdout

def toplevel (dir : String) : IO String := do
  let out ← git dir #["rev-parse", "--show-toplevel"]
  let top := out.dropRightWhile Char.isWhitespace
  try return (← IO.FS.realPath top).toString
  catch e => throw <| IO.userError s!"{top}: {e}"

/-- `start,count`, where a missing count means one line. -/
def parseRange (text : String) : Option (Nat × Nat) :=
  match text.splitOn "," with
  | [start] => start.toNat?.map (·, 1)
  | [start, count] => do pure (← start.toNat?, ← count.toNat?)
  | _ => none

/-- The counts a `@@ -a,b +c,d @@` header announces: lines removed, the new start, lines added. -/
def parseHunk (line : String) : Option (Nat × Nat × Nat) := do
  let parts := (line.splitOn " ").filter (· ≠ "") |>.drop 1
  let old ← parts[0]?
  let new ← parts[1]?
  guard (old.startsWith "-" && new.startsWith "+")
  let (_, removed) ← parseRange (old.dropS 1)
  let (newStart, newCount) ← parseRange (new.dropS 1)
  return (removed, newStart, newCount)

/-- Reads a `git diff -U0` text. Hunk bodies are skipped by their line counts, not by their first
character, so an added line that starts with `++ ` is not taken for a file header. -/
def parseDiff (top text : String) : Array (String × FileChange) := Id.run do
  let mut out := #[]
  let mut current : Option (String × Array (Nat × Nat)) := none
  -- Removed and added lines still to come in the current hunk.
  let mut body : Option (Nat × Nat) := none
  let finish (current : Option (String × Array (Nat × Nat))) (out : Array (String × FileChange)) :=
    match current with
    | some (path, ranges) => out.push (path, .lines ranges)
    | none => out
  for line in text.splitOn "\n" do
    if let some (removed, added) := body then
      let next :=
        if line.startsWith "-" then (removed - 1, added)
        else if line.startsWith "+" then (removed, added - 1)
        else (removed, added)
      body := if next == (0, 0) then none else some next
      continue
    if line.startsWith "diff --git " then
      out := finish current out
      current := none
    else if line.startsWith "+++ " then
      out := finish current out
      let rest := (line.dropS 4).dropRightWhile (· == '\t')
      current := if rest.startsWith "b/" then some (s!"{top}/{rest.dropS 2}", #[]) else none
    else if line.startsWith "@@ " then
      if let some (removed, newStart, newCount) := parseHunk line then
        body := some (removed, newCount)
        if body == some (0, 0) then body := none
        if newCount > 0 then
          if let some (path, ranges) := current then
            current := some (path, ranges.push (newStart, newStart + newCount - 1))
  return finish current out

/-- The changed lines between `ref` and the working tree, for every git repository that holds one
of `roots`. Untracked files that git does not ignore count as all new. -/
def changedSince (roots : Array String) (ref : String) : IO ChangedLines := do
  let mut tops : Array String := #[]
  for root in roots do
    let dir ← if ← System.FilePath.isDir root then pure root
      else pure ((System.FilePath.parent root).map (·.toString) |>.getD root)
    let top ← toplevel dir
    if !tops.contains top then tops := tops.push top
  let mut files : Std.HashMap String FileChange := {}
  for top in tops.qsort (· < ·) do
    let diff ← git top #["-c", "core.quotepath=off", "diff", "--no-color", "--no-ext-diff",
      "--src-prefix=a/", "--dst-prefix=b/", "-U0", ref, "--"]
    for (path, change) in parseDiff top diff do files := files.insert path change
    let untracked ← git top #["ls-files", "--others", "--exclude-standard", "-z"]
    for name in untracked.splitOn "\x00" do
      if !name.isEmpty then files := files.insert s!"{top}/{name}" .everything
  return ⟨files⟩

end Clocrap.Diff
