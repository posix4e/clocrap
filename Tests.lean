import Lean.Data.Json
import Clocrap

/-!
# Tests

`lake build clocrap clocrap-test && .lake/build/bin/clocrap-test` runs them all.

Most are end to end: they run the built `clocrap` on small fixture trees in a temporary directory,
with git where the case needs it, and read its JSON as a user's script would. The rest are tables
of source snippets and the functions, complexities and spans each analyzer must find in them: the
cases the Rust version's tests pinned, and the ones this port had to learn from diffing the two
binaries on real repositories.
-/

open Clocrap

/-! ## Helpers -/

/-- A failed check, with what was expected and what came instead. -/
def fail {α : Type} (msg : String) : IO α := throw <| IO.userError msg

def expectEq {α : Type} [BEq α] [Repr α] (what : String) (actual expected : α) : IO Unit := do
  unless actual == expected do
    fail s!"{what}: expected {reprStr expected}, got {reprStr actual}"

def expect (what : String) (ok : Bool) : IO Unit := do
  unless ok do fail what

/-- The `clocrap` binary built next to this one. -/
def binary : IO System.FilePath := do
  return ((← IO.appPath).parent.getD ".") / "clocrap"

/-- A fresh, empty directory for one test, canonical so it matches the paths clocrap prints. -/
def fixture : IO System.FilePath := do
  IO.FS.realPath (← IO.FS.createTempDir)

def write (path : System.FilePath) (contents : String) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path contents

def clocrap (dir : System.FilePath) (args : Array String) : IO IO.Process.Output := do
  IO.Process.output { cmd := (← binary).toString, args, cwd := dir }

def git (dir : System.FilePath) (args : Array String) : IO Unit := do
  let out ← IO.Process.output {
    cmd := "git"
    args := #["-C", dir.toString, "-c", "user.name=clocrap",
      "-c", "user.email=clocrap@example.invalid"] ++ args }
  unless out.exitCode == 0 do fail s!"git {args} failed: {out.stderr}"

def stdoutJson (out : IO.Process.Output) : IO Lean.Json :=
  match Lean.Json.parse out.stdout with
  | .ok j => pure j
  | .error e => fail s!"not JSON ({e}): {out.stdout}\nstderr: {out.stderr}"

/-- The value at a path of object keys and array indices, or `null`. -/
def Lean.Json.at (j : Lean.Json) : List String → Lean.Json
  | [] => j
  | k :: rest =>
    let next := match k.toNat? with
      | some n => j.getArrVal? n
      | none => j.getObjVal? k
    match next with
    | .ok v => Lean.Json.at v rest
    | .error _ => .null

def nat (j : Lean.Json) (path : List String) : Option Nat := (Lean.Json.at j path).getNat?.toOption
def str (j : Lean.Json) (path : List String) : Option String := (Lean.Json.at j path).getStr?.toOption
def num (j : Lean.Json) (path : List String) : Option Float :=
  (Lean.Json.at j path).getNum?.toOption.map (·.toFloat)

def rowsAt (j : Lean.Json) (path : List String) : Array Lean.Json :=
  (Lean.Json.at j path).getArr?.toOption.getD #[]

def contains (text part : String) : Bool := (text.splitOn part).length > 1

/-- The row of the language table for `name`. -/
def language (j : Lean.Json) (name : String) : IO Lean.Json := do
  match (rowsAt j ["languages"]).find? (fun r => str r ["language"] == some name) with
  | some r => pure r
  | none => fail s!"no {name} row in {j.compress}"

/-- The number `wc -l` reports for a file: its newlines. -/
def wcLines (path : System.FilePath) : IO Nat := do
  let bytes ← IO.FS.readBinFile path
  return bytes.foldl (fun n b => if b == 10 then n + 1 else n) 0

def libRs : String := "//! Crate docs.

/// A function.
pub fn f(x: u32) -> u32 {
    // comment
    if x > 1 {
        return 1;
    }
    if x > 2 {
        return 2;
    }
    0
}
"

/-! ## The command line -/

def totalLinesAgreeWithWc : IO Unit := do
  let dir ← fixture
  write (dir / "src/lib.rs") libRs
  write (dir / "README.md") "# Title\n\nSome prose.\n"
  write (dir / "tool/run.py") "\"\"\"Doc.\n\nmore\n\"\"\"\n# note\nprint(1)\n"
  write (dir / "Cargo.toml") "[package]\n# c\nname = \"x\"\n"
  write (dir / "web/app.ts") "// top\nconst a = 1; /* c */\n\n"
  let files : List String := ["src/lib.rs", "README.md", "tool/run.py", "Cargo.toml", "web/app.ts"]
  let expected ← files.foldlM (fun n f => return n + (← wcLines (dir / System.FilePath.mk f))) 0
  let out ← clocrap dir #["--json"]
  expectEq "exit status" out.exitCode 0
  let json ← stdoutJson out
  let counted := (nat json ["total", "blank"]).getD 0 + (nat json ["total", "comment"]).getD 0 +
    (nat json ["total", "code"]).getD 0
  expectEq "lines counted" counted expected
  expectEq "files" (nat json ["total", "files"]) (some 5)
  expectEq "file rows" (rowsAt json ["files"]).size 5
  IO.FS.removeDirAll dir

def perLanguageTotalsAndTable : IO Unit := do
  let dir ← fixture
  write (dir / "src/lib.rs") libRs
  let json ← stdoutJson (← clocrap dir #["--json"])
  expectEq "language" (str json ["languages", "0", "language"]) (some "Rust")
  expectEq "files" (nat json ["languages", "0", "files"]) (some 1)
  expectEq "blank" (nat json ["languages", "0", "blank"]) (some 1)
  expectEq "comment" (nat json ["languages", "0", "comment"]) (some 3)
  expectEq "code" (nat json ["languages", "0", "code"]) (some 9)
  let text := (← clocrap dir #[]).stdout
  expect s!"a Rust row in {text}" ((text.splitOn "\n").any (·.startsWith "Rust"))
  expect s!"a SUM row in {text}" (contains text "SUM:")
  IO.FS.removeDirAll dir

def filesWithoutAnExtensionByShebang : IO Unit := do
  let dir ← fixture
  write (dir / "bin/tool") "#!/usr/bin/env python3\n# a comment\nprint(1)\n"
  write (dir / "bin/run") "#!/bin/sh\necho hi\n"
  write (dir / "bin/data") "plain text\n"
  write (dir / "LICENSE") "MIT\n"
  let json ← stdoutJson (← clocrap dir #["--json"])
  expectEq "files" (nat json ["total", "files"]) (some 2)
  let python ← language json "Python"
  expectEq "Python" (nat python ["files"], nat python ["comment"], nat python ["code"])
    (some 1, some 2, some 1)
  let shell ← language json "Shell"
  expectEq "Shell" (nat shell ["comment"], nat shell ["code"]) (some 1, some 1)
  IO.FS.removeDirAll dir

def cHtmlCssAndJsonLines : IO Unit := do
  let dir ← fixture
  write (dir / "probe.c") "/* block\n comment */\nint main(void) { return '/'; } // tail\n"
  write (dir / "page.html") "<!-- note -->\n<p>\"quoted\" text</p>\n<!--\nmulti\n-->\n"
  write (dir / "site.css") "/* theme */\nbody { content: \"/*\"; }\n"
  write (dir / "events.jsonl") "{\"a\":1}\n{\"b\":2}\n"
  let json ← stdoutJson (← clocrap dir #["--json"])
  for (name, comment, code) in [("C", 2, 1), ("HTML", 4, 1), ("CSS", 1, 1), ("JSON", 0, 2)] do
    let row ← language json name
    expectEq name (nat row ["comment"], nat row ["code"]) (some comment, some code)
  IO.FS.removeDirAll dir

def gitignoredFilesAreNotCounted : IO Unit := do
  let dir ← fixture
  write (dir / ".gitignore") "generated/\n"
  write (dir / "keep.rs") "fn k() {}\n"
  write (dir / "generated/skip.rs") "fn s() {}\n"
  let json ← stdoutJson (← clocrap dir #["--json"])
  expectEq "files" (nat json ["total", "files"]) (some 1)
  IO.FS.removeDirAll dir

/-- Writes `libRs` and an lcov file in which two of the four lines of `f`'s two `if`s ran. -/
def crapFixture : IO (System.FilePath × String) := do
  let dir ← fixture
  let source := dir / "src/lib.rs"
  write source libRs
  let lcov := dir / "lcov.info"
  write lcov s!"SF:{← IO.FS.realPath source}\nDA:6,1\nDA:7,1\nDA:9,0\nDA:10,0\nend_of_record\n"
  return (dir, lcov.toString)

def crapScoreMatchesTheHandComputedValue : IO Unit := do
  -- Complexity 3 (base 1, two ifs). Lines 6, 7, 9, 10 are instrumented and two of them ran, so
  -- coverage is 0.5. CRAP = 3^2 * 0.5^3 + 3 = 9 / 8 + 3 = 4.125.
  let (dir, lcov) ← crapFixture
  let json ← stdoutJson (← clocrap dir #["--json", "--lcov", lcov])
  let f := ["functions", "functions", "0"]
  expectEq "name" (str json (f ++ ["name"])) (some "f")
  expectEq "complexity" (nat json (f ++ ["complexity"])) (some 3)
  expectEq "coverage" (num json (f ++ ["coverage"])) (some 0.5)
  expectEq "crap" (num json (f ++ ["crap"])) (some 4.125)
  expectEq "over threshold" (nat json ["functions", "over_threshold"]) (some 0)
  IO.FS.removeDirAll dir

def thresholdGateExitsOneOnlyAboveIt : IO Unit := do
  let (dir, lcov) ← crapFixture
  -- Default threshold 30: 4.125 passes.
  expectEq "default threshold" (← clocrap dir #["--lcov", lcov]).exitCode 0
  -- 4.2 is above 4.125: still passes.
  expectEq "threshold 4.2" (← clocrap dir #["--lcov", lcov, "--threshold", "4.2"]).exitCode 0
  -- 4 is below 4.125: fails with status 1.
  let failed ← clocrap dir #["--lcov", lcov, "--threshold", "4"]
  expectEq "threshold 4" failed.exitCode 1
  expect s!"OVER in {failed.stdout}" (contains failed.stdout "OVER")
  IO.FS.removeDirAll dir

def withoutCoverageComplexityOnlyAndNeverGates : IO Unit := do
  let dir ← fixture
  write (dir / "src/lib.rs") libRs
  let out ← clocrap dir #["--threshold", "1"]
  expectEq "exit status" out.exitCode 0
  expect s!"complexity only in {out.stdout}" (contains out.stdout "complexity only")
  expect s!"f at src/lib.rs:4 in {out.stdout}" <| (out.stdout.splitOn "\n").any fun line =>
    (line.splitOn " ").any (· == "f") && contains line "src/lib.rs:4"
  IO.FS.removeDirAll dir

def diffCountsAddedLinesAndUntrackedFiles : IO Unit := do
  let dir ← fixture
  write (dir / "src/lib.rs") libRs
  git dir #["init", "-q"]
  git dir #["add", "."]
  git dir #["commit", "-q", "-m", "init"]
  -- One new code line in a tracked file, and a new untracked file of two lines.
  write (dir / "src/lib.rs") (libRs ++ "fn g() {}\n")
  write (dir / "new.rs") "fn n() {}\n\n"
  let json ← stdoutJson (← clocrap dir #["--diff", "HEAD", "--json"])
  expectEq "files" (nat json ["total", "files"]) (some 2)
  expectEq "code" (nat json ["total", "code"]) (some 2)
  expectEq "blank" (nat json ["total", "blank"]) (some 1)
  expectEq "comment" (nat json ["total", "comment"]) (some 0)
  IO.FS.removeDirAll dir

def diffAgainstAnUnknownRefIsAnError : IO Unit := do
  let dir ← fixture
  write (dir / "a.rs") "fn a() {}\n"
  git dir #["init", "-q"]
  expectEq "exit status" (← clocrap dir #["--diff", "no-such-ref"]).exitCode 2
  IO.FS.removeDirAll dir

def countsTheFilesGitLists : IO Unit := do
  let dir ← fixture
  git dir #["init", "-q"]
  write (dir / ".gitignore") "ignored.rs\n"
  write (dir / "tracked.rs") "fn t() {}\n"
  write (dir / ".github/ci.yml") "name: ci\n"
  write (dir / "untracked.rs") "fn u() {}\n"
  write (dir / "ignored.rs") "fn i() {}\n"
  git dir #["add", "tracked.rs", ".github/ci.yml"]
  -- Tracked, hidden but tracked, and untracked but not ignored.
  let byGit ← stdoutJson (← clocrap dir #["--json"])
  expectEq "files git lists" (nat byGit ["total", "files"]) (some 3)
  IO.FS.removeDirAll dir

def outsideGitTheDirectoriesAreWalked : IO Unit := do
  let dir ← fixture
  write (dir / ".gitignore") "ignored.rs\n"
  write (dir / "kept.rs") "fn k() {}\n"
  write (dir / ".hidden/h.rs") "fn h() {}\n"
  write (dir / "ignored.rs") "fn i() {}\n"
  let walked ← stdoutJson (← clocrap dir #["--json"])
  expectEq "files walked" (nat walked ["total", "files"]) (some 1)
  IO.FS.removeDirAll dir

/-- A Rust file of `n` functions, each of complexity 6, so untested each scores 42. -/
def manyFunctions (n : Nat) : String :=
  String.join ((List.range n).map fun k =>
    s!"fn f{k}(a: bool) \{\n" ++
      String.join (List.replicate 5 "    if a { return; }\n") ++ "}\n")

def tableShowsTheWorstAndJsonEveryFunction : IO Unit := do
  let dir ← fixture
  write (dir / "a.rs") (manyFunctions 25)
  let out ← clocrap dir #[]
  expect s!"the rest said in {out.stdout}" (contains out.stdout "5 more functions")
  expectEq "rows" ((out.stdout.splitOn "a.rs:").length - 1) 20
  let json ← stdoutJson (← clocrap dir #["--json"])
  expectEq "functions" (rowsAt json ["functions", "functions"]).size 25
  expectEq "files" (str json ["files", "0", "path"]) (some "a.rs")
  IO.FS.removeDirAll dir

def filesTheReportOmitsCountAsUntested : IO Unit := do
  let dir ← fixture
  write (dir / "a.rs") (manyFunctions 25)
  write (dir / "lcov.info") "SF:elsewhere.rs\nDA:1,1\nend_of_record\n"
  let out ← clocrap dir #["--lcov", "lcov.info"]
  expectEq "exit status" out.exitCode 1
  -- All of them are over the threshold, so the table cuts none.
  expectEq "rows" ((out.stdout.splitOn "OVER").length - 1) 25
  expect s!"said in {out.stdout}" (contains out.stdout "25 functions in files the coverage report does not list count as 0% covered")
  IO.FS.removeDirAll dir

def removedOptionsAreRefused : IO Unit := do
  let dir ← fixture
  for flag in ["--crap", "--by-file", "--walk", "--count-unlisted", "--threads=2"] do
    expectEq flag (← clocrap dir #[flag]).exitCode 2
  IO.FS.removeDirAll dir

def diffKeepsChangedFunctions : IO Unit := do
  let dir ← fixture
  write (dir / "src/lib.rs") libRs
  git dir #["init", "-q"]
  git dir #["add", "."]
  git dir #["commit", "-q", "-m", "init"]
  -- A new function after `f`; `f` itself is untouched.
  write (dir / "src/lib.rs")
    (libRs ++ "\npub fn g(y: u32) -> u32 {\n    if y > 0 { y } else { 0 }\n}\n")
  let json ← stdoutJson (← clocrap dir #["--diff", "HEAD", "--json"])
  expectEq "functions" ((rowsAt json ["functions", "functions"]).toList.map (str · ["name"]))
    [some "g"]
  IO.FS.removeDirAll dir

/-- The functions of a Lean coverage run: name, complexity and coverage to three places. -/
def leanCoverage (json : Lean.Json) : List (Option String × Option Nat × Option Float) :=
  (rowsAt json ["functions", "functions"]).toList.map fun f =>
    (str f ["name"], nat f ["complexity"], (num f ["coverage"]).map fun c => (c * 1000).round / 1000)

def leanCoverageComesFromItsC : IO Unit := do
  let dir ← fixture
  write (dir / "pkg/Cov/Basic.lean") "namespace Cov
/-- Tested. -/
def classify (n : Nat) : String :=
  if n == 0 then \"zero\" else if n % 2 == 0 then \"even\" else \"odd\"
def unused (n : Nat) : Nat := match n with
  | 0 => 1
  | k + 1 => k * 2
@[inline] def inlined (n : Nat) : Nat := n
theorem t : 1 = 1 := rfl
end Cov
"
  -- The C file must exist, so its path canonicalises like the Lean file's.
  let cFile := dir / "pkg/.lake/build/ir/Cov/Basic.c"
  write cFile ""
  write (dir / "lcov.info") (s!"SF:{← IO.FS.realPath cFile}\n" ++
    "FN:10,lp_pkg_Cov_classify\nFN:20,lp_pkg_Cov_classify___boxed\nFN:30,lp_pkg_Cov_unused\n" ++
    "FN:40,initialize_pkg_Cov_Basic\nDA:10,1\nDA:11,1\nDA:12,0\nDA:20,0\nDA:30,0\nDA:40,1\n" ++
    "end_of_record\n")
  let json ← stdoutJson (← clocrap dir #["--json", "--lcov", "lcov.info", "pkg"])
  let lean ← language json "Lean"
  expectEq "Lean code" (nat lean ["code"]) (some 9)
  expectEq "Lean comment" (nat lean ["comment"]) (some 1)
  -- unused: complexity 2, untested, CRAP 6; classify: complexity 3, two of its three C lines ran.
  expectEq "functions" (leanCoverage json)
    [(some "unused", some 2, some 0.0), (some "classify", some 3, some 0.667)]
  expectEq "no code" (nat json ["functions", "no_code"]) (some 1)
  IO.FS.removeDirAll dir

def leanSpecialisedCopiesBelongToTheCallee : IO Unit := do
  let dir ← fixture
  write (dir / "pkg/Cov/Basic.lean") "namespace Cov
def majority {α} [BEq α] (xs : Array α) : Option α :=
  if xs.isEmpty then none else xs[0]?
end Cov
"
  write (dir / "pkg/Cov/Use.lean") "namespace Cov
def count (xs : Array Nat) : Option Nat := majority xs
end Cov
"
  let basic := dir / "pkg/.lake/build/ir/Cov/Basic.c"
  let use := dir / "pkg/.lake/build/ir/Cov/Use.c"
  write basic ""
  write use ""
  -- The generic `majority` never runs; its copy specialised for `count`, in another module's C,
  -- does, though not the loop of the standard library specialised inside that copy. Its copy for
  -- `other` never runs, as `other` itself never did.
  let fold := "lp_pkg___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00" ++
    "Cov_majority___at___00Cov_count_spec__0_spec__1"
  write (dir / "lcov.info") (s!"SF:{← IO.FS.realPath basic}\n" ++
    "FN:10,lp_pkg_Cov_majority\nFN:20,initialize_pkg_Cov_Basic\n" ++
    "FNDA:0,lp_pkg_Cov_majority\nFNDA:1,initialize_pkg_Cov_Basic\n" ++
    "DA:10,0\nDA:11,0\nDA:20,1\nend_of_record\n" ++
    s!"SF:{← IO.FS.realPath use}\n" ++
    s!"FN:10,lp_pkg_Cov_majority___at___00Cov_count_spec__0\nFN:15,{fold}\n" ++
    "FN:20,lp_pkg_Cov_count\nFN:25,lp_pkg_Cov_majority___at___00Cov_other_spec__0___redArg\n" ++
    "FN:30,initialize_pkg_Cov_Use\n" ++
    s!"FNDA:3,lp_pkg_Cov_majority___at___00Cov_count_spec__0\nFNDA:0,{fold}\n" ++
    "FNDA:3,lp_pkg_Cov_count\nFNDA:0,lp_pkg_Cov_majority___at___00Cov_other_spec__0___redArg\n" ++
    "FNDA:1,initialize_pkg_Cov_Use\n" ++
    "DA:10,3\nDA:11,3\nDA:12,0\nDA:15,0\nDA:16,0\nDA:20,3\nDA:21,3\nDA:25,0\nDA:26,0\n" ++
    "DA:30,1\nend_of_record\n")
  let json ← stdoutJson (← clocrap dir #["--json", "--lcov", "lcov.info", "pkg"])
  -- majority: two of the five lines of its copy for `count` ran. Its own generic body and its
  -- copy for `other`, never called, are left out. count keeps only its own two lines.
  expectEq "functions" (leanCoverage json)
    [(some "majority", some 2, some 0.4), (some "count", some 1, some 1.0)]
  IO.FS.removeDirAll dir

def leanInlinedDeclarationsAreShownApart : IO Unit := do
  let dir ← fixture
  write (dir / "pkg/Cov/Basic.lean") "namespace Cov
@[inline] def double (n : Nat) : Nat := if n > 0 then n * 2 else 0
def next (n : Nat) : Nat := Nat.succ n
def untested (n : Nat) : Nat := if n > 0 then n * 2 else 0
def run (n : Nat) : Nat := double (next n)
@[inline] def called (n : Nat) : Nat := n
end Cov
"
  let cFile := dir / "pkg/.lake/build/ir/Cov/Basic.c"
  write cFile ""
  -- `double` and the one-call `next` ran inside `run`, so their own C was never called;
  -- `untested` is not inlined and never ran; `called` is inlined somewhere but also called.
  write (dir / "lcov.info") (s!"SF:{← IO.FS.realPath cFile}\n" ++
    "FN:10,lp_pkg_Cov_double\nFN:20,lp_pkg_Cov_next\nFN:30,lp_pkg_Cov_untested\n" ++
    "FN:40,lp_pkg_Cov_run\nFN:45,lp_pkg_Cov_called\nFN:50,initialize_pkg_Cov_Basic\n" ++
    "FNDA:0,lp_pkg_Cov_double\nFNDA:0,lp_pkg_Cov_next\nFNDA:0,lp_pkg_Cov_untested\n" ++
    "FNDA:4,lp_pkg_Cov_run\nFNDA:2,lp_pkg_Cov_called\nFNDA:1,initialize_pkg_Cov_Basic\n" ++
    "DA:10,0\nDA:11,0\nDA:20,0\nDA:30,0\nDA:31,0\nDA:40,4\nDA:41,4\nDA:45,2\nDA:50,1\n" ++
    "end_of_record\n")
  let json ← stdoutJson (← clocrap dir #["--json", "--lcov", "lcov.info", "pkg"])
  expectEq "functions" (leanCoverage json)
    [(some "untested", some 2, some 0.0), (some "run", some 1, some 1.0),
     (some "called", some 1, some 1.0)]
  expectEq "inlined" (nat json ["functions", "inlined"]) (some 2)
  let table := (← clocrap dir #["--lcov", "lcov.info", "pkg"]).stdout
  expect s!"the table says how many were inlined: {table}"
    (contains table "2 Lean functions were inlined into their callers")
  IO.FS.removeDirAll dir

/-- Each way C can use a declaration, and each way it can seem not to. `run` is the only function
that ran. The C is written by hand, in the shape Lean writes it; the `.olean` is compiled for real,
since what the source uses after elaboration is the point. -/
def silentFixture : IO System.FilePath := do
  let dir ← fixture
  write (dir / "lean-toolchain") (← IO.FS.readFile "lean-toolchain")
  write (dir / "Cov/Basic.lean") "namespace Cov
structure T where
  n : Nat
def eqT (a b : T) : Bool := a.n == b.n
instance : BEq T := ⟨eqT⟩
def direct (n : Nat) : Nat := n + 1
def byClosure (n : Nat) : Nat := n + 2
def byStatic (n : Nat) : Nat := n + 3
def byClosedTerm (n : Nat) : Nat := n + 4
def inlinedAway (n : Nat) : Nat := n + 5
def ownPartsOnly (n : Nat) : Nat := n + 6
private def hidden (n : Nat) : Nat := n + 7
def dead (n : Nat) : Nat := n + 8
def provedOnly (n : Nat) : Nat := n + 9
theorem provedOnly_eq : provedOnly 0 = 9 := rfl
def run (a : T) : Nat := if a == a then inlinedAway 1 + ownPartsOnly 2 + hidden 3 else 0
end Cov
"
  let lean := dir / ".lake/build/lib/lean/Cov/Basic.olean"
  IO.FS.createDirAll (lean.parent.getD ".")
  let compiled ← IO.Process.output {
    cmd := "lean", args := #["-o", lean.toString, "Cov/Basic.lean"], cwd := some dir }
  unless compiled.exitCode == 0 do fail s!"lean: {compiled.stdout}{compiled.stderr}"
  let silent := ["direct", "byClosure", "byStatic", "byClosedTerm", "inlinedAway", "ownPartsOnly",
    "eqT", "dead", "provedOnly"]
  let names := (silent.map ("lp_pkg_Cov_" ++ ·)) ++ ["lp_pkg___private_Cov_Basic_0__Cov_hidden",
    "lp_pkg_Cov_ownPartsOnly___lam__0", "lp_pkg_Cov_ownPartsOnly___boxed",
    "_init_lp_pkg_Cov_table___closed__0"]
  let functions := names.zipIdx.map fun (name, k) => (name, 100 + 10 * k)
  let lines := functions.foldl (init := Array.replicate 400 "") fun lines (name, line) =>
    lines.set! (line - 1) s!"static lean_object* {name}(lean_object* x_1)\{"
  let body (name text : String) (lines : Array String) : Array String :=
    match functions.find? (·.1 == name) with
    | some (_, line) => lines.set! line text
    | none => lines
  let lines := lines
    |>.set! 0 "LEAN_EXPORT lean_object* lp_pkg_Cov_dead(lean_object*);"
    |>.set! 1 "static const lean_closure_object lp_pkg_Cov_run___closed__0_value = {.m_fun = (void*)lp_pkg_Cov_byStatic___boxed, .m_arity = 1};"
    |>.set! 2 "static const lean_object* lp_pkg_Cov_dead___closed__0 = (const lean_object*)&lp_pkg_Cov_dead___closed__0_value;"
    |>.set! 49 "lean_object* lp_pkg_Cov_run(lean_object* x_1){"
    |>.set! 50 "x_2 = lp_pkg_Cov_direct(x_1);"
    |>.set! 51 "x_3 = lean_alloc_closure((void*)(lp_pkg_Cov_byClosure___boxed), 1, 0);"
    |>.set! 299 "void initialize_pkg_Cov_Basic(void){"
    |>.set! 300 "lp_pkg_Cov_dead = _init_lp_pkg_Cov_dead();"
    |> body "_init_lp_pkg_Cov_table___closed__0" "x_2 = lp_pkg_Cov_byClosedTerm(x_1);"
    |> body "lp_pkg_Cov_ownPartsOnly___lam__0" "x_2 = lp_pkg_Cov_ownPartsOnly(x_1);"
    |> body "lp_pkg_Cov_ownPartsOnly___boxed" "x_2 = lp_pkg_Cov_ownPartsOnly(x_1);"
    |> body "lp_pkg_Cov_dead" "x_2 = lp_pkg_Cov_dead(x_1);"
  let cFile := dir / ".lake/build/ir/Cov/Basic.c"
  write cFile ("\n".intercalate lines.toList ++ "\n")
  let all := functions ++ [("lp_pkg_Cov_run", 50), ("initialize_pkg_Cov_Basic", 300)]
  let record := all.foldl (init := "") fun out (name, line) => out ++ s!"FN:{line},{name}\n"
  let counts := all.foldl (init := "") fun out (name, _) =>
    let calls := if name == "lp_pkg_Cov_run" then 1 else 0
    out ++ s!"FNDA:{calls},{name}\n"
  let hits := all.foldl (init := "") fun out (name, line) =>
    let calls := if name == "lp_pkg_Cov_run" then 1 else 0
    out ++ s!"DA:{line},{calls}\n"
  write (dir / "lcov.info") (s!"SF:{← IO.FS.realPath cFile}\n" ++ record ++ counts ++ hits ++
    "end_of_record\n")
  return dir

/-- The functions of a report by name, with their coverage and whether they are unused. -/
def silentRows (json : Lean.Json) : List (String × Option Float × Bool) :=
  let rows := (rowsAt json ["functions", "functions"]).toList.filter fun r =>
    (str r ["path"]).any (·.endsWith ".lean")
  let found := rows.map fun r =>
    ((str r ["name"]).getD "?", num r ["coverage"],
      (Lean.Json.at r ["unused"]).getBool?.toOption.getD false)
  found.mergeSort fun a b => a.1 ≤ b.1

def leanSilentDeclarations : IO Unit := do
  let dir ← silentFixture
  let json ← stdoutJson (← clocrap dir #["--json", "--lcov", "lcov.info", "Cov"])
  -- A call site, however it is written, makes a 0 real; `dead`'s only mentions are its own, and a
  -- theorem runs nothing, so `provedOnly` is unused too. `run` ran.
  expectEq "functions" (silentRows json)
    [("byClosedTerm", some 0.0, false), ("byClosure", some 0.0, false),
     ("byStatic", some 0.0, false), ("dead", some 0.0, true), ("direct", some 0.0, false),
     ("provedOnly", some 0.0, true), ("run", some 1.0, false)]
  -- `inlinedAway` and `hidden` are named by `run`, `eqT` is only reached through `a == a`, and
  -- `ownPartsOnly` is mentioned by nothing but its parts.
  expectEq "inlined" (nat json ["functions", "inlined"]) (some 4)
  let table := (← clocrap dir #["--lcov", "lcov.info", "Cov"]).stdout
  expect s!"the table marks them: {table}" (contains table "UNUSED")
  expect s!"and says how many: {table}"
    (contains table "2 Lean functions never ran and nothing that ran reaches them")
  IO.FS.removeDirAll dir

def leanSilentWithoutCompiledModules : IO Unit := do
  let dir ← silentFixture
  let out ← IO.Process.output {
    cmd := (← binary).toString, args := #["--json", "--lcov", "lcov.info", "Cov"], cwd := dir,
    env := #[("PATH", some "/nonexistent")] }
  expect s!"said so: {out.stderr}" (contains out.stderr "could not read")
  -- Nothing can be called unused or inlined now, so they stay as never run.
  let rows := silentRows (← stdoutJson out)
  expect s!"none is unused: {reprStr rows}" (rows.all fun (_, _, unused) => !unused)
  expectEq "inlined" (nat (← stdoutJson out) ["functions", "inlined"]) (some 0)
  IO.FS.removeDirAll dir

/-! ## Analyzers -/

/-- A snippet in a file of this name, and each function's name and complexity in line order. -/
structure Case where
  name : String
  path : String
  source : String
  expected : List (String × Nat)

def functionsIn (path source : String) : Array Function :=
  match Language.fromExtension ((path.splitOn ".").getLast!) with
  | some l => Complexity.functions l path source.toUTF8
  | none => #[]

def complexityCases : List Case := [
  { name := "straight-line Rust function", path := "a.rs", source := "fn f() -> u8 {\n    1\n}\n"
    expected := [("f", 1)] },
  -- 1 base, `if` 1, `else if` 1, `while` 1, `for` 1, `&&` 1, `||` 1.
  { name := "Rust decisions", path := "a.rs", source := "fn f(a: bool, b: bool, n: u32) {
    if a {
    } else if b && n > 0 {
    }
    while n > 0 {}
    for _ in 0..n {}
    let _ = a || b;
}
"
    expected := [("f", 7)] },
  -- 1 base plus (4 arms - 1) = 4.
  { name := "Rust match arms", path := "a.rs", source := "fn f(n: u8) -> u8 {
    match n {
        0 => 1,
        1 => 2,
        2 => 3,
        _ => 4,
    }
}
"
    expected := [("f", 4)] },
  { name := "nested Rust functions alone, closures not", path := "a.rs", source := "fn outer(n: u32) -> u32 {
    fn inner(m: u32) -> u32 {
        if m > 1 { 1 } else { 2 }
    }
    let f = |x: u32| if x > 0 { x } else { 0 };
    if n > 0 { inner(n) + f(n) } else { 0 }
}
"
    expected := [("outer", 3), ("inner", 2)] },
  { name := "Rust methods in impl blocks", path := "a.rs", source := "struct S;
impl S {
    fn a(&self) {}
    fn b(&self, x: bool) { if x {} }
}
"
    expected := [("a", 1), ("b", 2)] },
  -- 1 base, `if` 1, `elif` 1, `for` 1, `and` 1, `except` 1, ternary 1.
  { name := "Python decisions", path := "a.py", source := "def f(a, b, xs):
    if a:
        pass
    elif b and xs:
        pass
    for x in xs:
        pass
    try:
        pass
    except ValueError:
        pass
    return 1 if a else 2
"
    expected := [("f", 7)] },
  { name := "Python match cases", path := "a.py", source := "def f(n):
    match n:
        case 0:
            return 1
        case 1:
            return 2
        case _:
            return 3
"
    expected := [("f", 3)] },
  { name := "TypeScript functions, arrows and methods", path := "a.ts", source := "function f(a: boolean, b: boolean) {
    if (a && b) { return 1; }
    switch (a ? 1 : 2) {
        case 1: return 2;
        case 2: return 3;
        default: return 4;
    }
}
class C {
    m(x: number) { return x ?? 0; }
}
const g = (y: number) => y > 0 ? y : 0;
"
    expected := [("f", 6), ("m", 2), ("g", 2)] },
  { name := "JavaScript loops and catch", path := "a.js", source := "function f(xs) {
    for (const x of xs) {
        try { x(); } catch (e) { continue; }
    }
    while (false) {}
}
"
    expected := [("f", 4)] },
  -- Read as plain TypeScript the JSX would not parse; as TSX it is one function with a ternary.
  { name := "TSX", path := "a.tsx",
    source := "const C = (p: { ok: boolean }) => p.ok ? <b /> : null;\n"
    expected := [("C", 2)] },
  -- 1 base, `if` 1, `&&` 1, `for` 1, two valued `case`s 2, `?:` 1.
  { name := "C decisions", path := "a.c", source := "static int *f(int a, int b) {
    if (a && b) return 0;
    for (;;) {}
    switch (a) {
    case 1: return 0;
    case 2: return 0;
    default: return b ? 0 : 0;
    }
}
"
    expected := [("f", 7)] },
  { name := "Objective-C methods and functions", path := "a.m", source := "@implementation T
- (void)tap:(id)x at:(int)n {
    if (n > 0 && x) { [x go]; }
    @try { [x go]; } @catch (NSException *e) {}
}
+ (instancetype)shared { return nil; }
@end
static void g(void) { while (1) {} }
"
    expected := [("-tap:at:", 4), ("+shared", 1), ("g", 2)] },
  { name := "Lean through the dispatch", path := "a.lean",
    source := "def f (n : Nat) : Nat := if n = 0 then 1 else n\n"
    expected := [("f", 2)] },
  { name := "no grammar, no functions", path := "a.kt", source := "fun f() {}\n", expected := [] },
  -- Learned from diffing the binaries.
  { name := "Objective-C methods after instance variables and after @implementation"
    path := "a.m", source := "@implementation A {
    int _x;
}
- (void)a { if (_x) {} }
@end
@implementation B
- (void)b:(int)n { }
@end
"
    expected := [("-a", 2), ("-b:", 1)] },
  -- tree-sitter parses a `#if` condition as an expression, so its `||` counts; a `do`'s closing
  -- `while` is part of the `do`.
  { name := "C #if condition operators and do-while", path := "a.c", source := "static int f(int a) {
#if defined(A) || defined(B)
    return a;
#else
    return 0;
#endif
}
int g(int x) { do { x--; } while (x); return x; }
"
    expected := [("f", 2), ("g", 2)] },
  { name := "React Native's selector macro takes its last word", path := "a.m",
    source := "@implementation M

RCT_EXPORT_MODULE(Tools);

RCT_EXPORT_METHOD(run:(NSString *)path
                  rejecter:(RCTPromiseRejectBlock)reject)
{
  if (path) {}
}

@end
"
    expected := [("reject", 2)] }
]

/-- A snippet and each function's name, first line and last line. -/
structure SpanCase where
  name : String
  path : String
  source : String
  expected : List (String × Nat × Nat)

def spanCases : List SpanCase := [
  -- In a raw string a backslash is text, so `\{{` is a backslash and a literal brace, not code.
  { name := "Python raw f-string", path := "a.py", source := "def f(name):
    return rf'^\\s*{re.escape(name)} \\{{isa = x;'

def g(a):
    if a:
        return 1
"
    expected := [("f", 1, 2), ("g", 4, 6)] },
  -- Only a backslash right before a line break joins lines; this one is in a comment.
  { name := "Python backslash in a comment", path := "a.py", source := "def f(self):
    # \"\\/\" escaped
    x = (1,
         2)
    g()
"
    expected := [("f", 1, 5)] }
]

/-! ## Lean -/

def leanFound (source : String) : List (String × Nat) :=
  (LeanLang.functions source.toUTF8).toList.map fun f => (f.name, f.complexity)

def leanSymbols (source : String) : List (String × Bool) :=
  (LeanLang.functions source.toUTF8).toList.map fun f =>
    match f.symbol with
    | some s => (s.name, s.private_)
    | none => ("<none>", false)

def whereSource : String := "namespace Cov
def total (xs : List Nat) : Nat := go xs 0
where
  go : List Nat → Nat → Nat
    | [], acc => acc
    | x :: rest, acc => go rest (acc + x)
  @[inline] twice (n : Nat) : Nat := if n > 0 then n * 2 else 0
end Cov
"

def instanceSource : String := "namespace N
instance : ToString P := ⟨fun p => if p.a then \"y\" else \"n\"⟩
instance named : Inhabited P := ⟨⟨0⟩⟩
instance (priority := low) [ToJson α] : ToJson (Array α) where
  toJson xs := if xs.isEmpty then .null else .arr (xs.map toJson)
end N
"

def leanCases : List (String × String × List (String × Nat)) := [
  ("straight-line definition", "def f (n : Nat) : Nat := n + 1\n", [("f", 1)]),
  -- 1 base, `if` 1, `else if` 1, `&&` 1, `for` 1, `||` 1, `while` 1, `catch` 1, `<|>` 1.
  ("decisions", "def f (a b : Bool) (n : Nat) : IO Nat := do
  if a then
    pure 1
  else if b && n > 0 then
    pure 2
  for _ in [0:n] do
    if a || b then pure () else pure ()
  while false do pure ()
  try pure () catch _ => pure ()
  let x := none <|> some 1
  pure 0
", [("f", 10)]),
  ("match arms", "def f (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 2
  | _ => 3
", [("f", 3)]),
  ("an or-pattern is one arm", "def f (n : Nat) : Nat :=
  match n with
  | 0 | 1 => 1
  | 2 | 3
  | 4 => 2
  | _ => 3

def g : Nat → Nat
  | 0 | 1 => 1
  | _ => 2

def h (xs : List Nat) : List Nat :=
  xs.map fun
    | 0 | 1 => 1
    | _ => 2

def i (a b : Nat) : Nat :=
  match a, b with
  | 0, 0 | 1, 1 => 1
  | _, _ => 2
", [("f", 3), ("g", 2), ("h", 2), ("i", 2)]),
  -- A fallback has no `=>`, so what follows it must not read as more of its pattern.
  ("a fallback, then arms", "def f (a b : Option Nat) : IO Nat := do
  let some x := a | pure 0
  let some y := b | pure 1
  match x with
  | 0 => pure 2
  | 1 | 2 => pure y
  | _ => pure 3
", [("f", 5)]),
  ("pattern-matching definitions and lambdas", "def f : Nat → Nat
  | 0 => 1
  | 1 => 2
  | _ => 3

def g (xs : List (Option Nat)) : List Nat :=
  xs.map fun
    | some x => x
    | none => 0
", [("f", 3), ("g", 2)]),
  ("a do let with a fallback", "def f (o : Option Nat) : IO Nat := do
  let some x := o | return 0
  return x
", [("f", 2)]),
  -- The `if` inside the interpolation is code, but the whole string is one token, so it is not
  -- counted: interpolations rarely branch.
  ("keywords in comments and strings", "/-- if this were code, `match` and `for` -/
def f (s : String) : String :=
  -- if not
  /- nested /- if -/ for -/
  s ++ \"if || && for\" ++ s!\"{if true then \"a\" else \"b\"} for\" ++ r#\"if\"#
", [("f", 1)]),
  ("where helpers", whereSource, [("total", 1), ("total.go", 2), ("total.twice", 2)]),
  ("structure instance where", "def config : Config where
  a := if b then 1 else 2
  c := 3
", [("config", 2)]),
  ("proofs, types and syntax", "theorem t : 1 = 1 := by
  if h : True then rfl else rfl
example : 2 = 2 := rfl
structure P where
  a : Nat
  deriving Repr
inductive T | a | b
macro \"x\" : term => `(1)
def real (n : Nat) : Nat := if n = 0 then 1 else n
", [("real", 2)]),
  ("termination proofs", "def f (n : Nat) : Nat := if n = 0 then 0 else f (n - 1)
termination_by n
decreasing_by
  all_goals (if h : n = 0 then omega else omega)
", [("f", 2)]),
  ("mutual blocks", "mutual
  private partial def a (n : Nat) : Nat := if n = 0 then 0 else b (n - 1)
  private partial def b (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | k + 1 => a k
end
def c := 1
", [("a", 2), ("b", 2), ("c", 1)]),
  ("instances", instanceSource,
    [("instance ToString P", 2), ("named", 1), ("instance ToJson (Array α)", 2)]),
  ("primes, bangs and guillemets", "def f' (x' : Nat) : Nat := x' + 'a'.toNat
def get! (xs : Array Nat) : Nat := xs[0]!
def «weird name» := 1
", [("f'", 1), ("get!", 1), ("«weird name»", 1)])
]

def leanSymbolsAndSpans : IO Unit := do
  expectEq "where symbols" (leanSymbols whereSource)
    [("Cov.total", false), ("Cov.total.go", false), ("Cov.total.twice", false)]
  expectEq "namespace symbols" (leanSymbols "namespace A.B
private def p := 1
section S
def q := 2
end S
def _root_.r := 3
@[simp] protected def A.s := 4
end A.B
def t := 5
") [("A.B.p", true), ("A.B.q", false), ("r", false), ("A.B.A.s", false), ("t", false)]
  expectEq "instance symbols" (leanSymbols instanceSource)
    [("N.instToStringP", false), ("N.named", false), ("N.instToJsonArray", false)]
  let spans := (LeanLang.functions "/-- doc -/
@[inline]
def f : String := \"a
b\"

def g := 1
".toUTF8).toList.map fun f => (f.startLine, f.endLine)
  expectEq "spans cover attributes and multiline strings" spans [(2, 4), (6, 6)]
  -- What the compiler may inline: by attribute, `abbrev`, or a body of one application of names.
  let inline := (LeanLang.functions "def a : Reader UInt8 := ByteReader.readUInt8
def b (n : Nat) := g n 1
def c (n : Nat) := n + 1
@[inline] def d (n : Nat) := n + 1
@[specialize, simp] def e (n : Nat) := n + 1
abbrev f (n : Nat) := n + 1
def g (n : Nat) : Id Nat := do return n
def h : Nat → Nat
  | n => n
def i (n : Nat) : Nat := j n
where
  @[inline] j (n : Nat) : Nat := n * 2
".toUTF8).toList.map fun f => (f.name, (f.symbol.map (·.inline)).getD false)
  expectEq "inline" inline [("a", true), ("b", true), ("c", false), ("d", true), ("e", true),
    ("f", true), ("g", false), ("h", false), ("i", true), ("i.j", true)]

def leanLineKinds : IO Unit := do
  -- A quote-matching classifier leaves the last string open after the first line, and takes the
  -- comment below for string text.
  let source := "def f (k : Option String) := s!\"marked {(k.map fun k => s!\"\\\"{k}\\\"\").getD \"none\"})\"
-- a comment
/- a block
   comment -/

def g := \"two
  lines\" -- trailing
"
  expectEq "nested interpolation" (LeanLang.lineKinds source.toUTF8)
    (some #[.code, .comment, .comment, .comment, .blank, .code, .code])
  expectEq "empty" (LeanLang.lineKinds ByteArray.empty) (some #[])
  expectEq "no final newline" (LeanLang.lineKinds "def x := 1".toUTF8) (some #[.code])

def leanMangling : IO Unit := do
  -- Names from the C that Lean 4.35 emits.
  let cases := [("My_ns.my_fun", "My__ns_my__fun"), ("My_ns.«weird name»", "My__ns_weird_x20name"),
    ("My_ns._under", "My__ns___under"), ("Std.Range.forIn'", "Std_Range_forIn_x27"),
    ("α.β", "00_u03b1_00_u03b2"), ("ℕat", "00_u2115at"), ("Foo.«a.b»", "Foo_a_x2eb"),
    ("x2._y3", "x2___y3")]
  for (name, c) in cases do
    expectEq s!"mangle {name}" (LeanLang.mangle name) c
  expectEq "mangle qualified" (LeanLang.mangle (LeanLang.qualified #["N"] "Foo.«a.b»"))
    "N_Foo_a_x2eb"

def supportedLanguages : IO Unit := do
  expect "Lean is supported" (Complexity.supports .lean "a.lean")
  expect "Rust is supported" (Complexity.supports .rust "a.rs")
  expect "Kotlin is not" (!Complexity.supports .kotlin "a.kt")

/-! ## Swift

Swift goes through the compiler's parser as a separate program, so its cases run the way a user
does: the built `clocrap` on a file in a fixture directory.
-/

/-- Each function clocrap reports for a Swift file: name, first line, last line and complexity. -/
def swiftFunctions (dir : System.FilePath) (args : Array String := #[]) :
    IO (List (String × Nat × Nat × Nat)) := do
  let out ← clocrap dir (#["--json"] ++ args)
  let rows := rowsAt (← stdoutJson out) ["functions", "functions"]
  let found := rows.toList.map fun r =>
    ((str r ["name"]).getD "?", (nat r ["line"]).getD 0, (nat r ["end_line"]).getD 0,
      (nat r ["complexity"]).getD 0)
  return found.mergeSort fun a b => a.2.1 ≤ b.2.1

/-- A snippet, and each function's name, first line, last line and complexity. -/
def swiftCases : List (String × String × List (String × Nat × Nat × Nat)) := [
  -- 1 base, `if` 1, `guard` 1, `&&` 1, `for` 1, switch with 3 entries 2.
  ("decisions", "func f(a: Bool, b: Bool, xs: [Int], n: Int) -> Int {
    if a && b { return 1 }
    guard n > 0 else { return 0 }
    for _ in xs {}
    switch n {
    case 1: return 1
    case 2: return 2
    default: return 3
    }
}
", [("f", 1, 10, 7)]),
  -- 1 base, `?:` 1, `??` 1, `||` 1, the `if` inside the interpolation 1.
  ("expressions", "func f(a: Bool, b: Int?) -> String {
    let x = a ? 1 : 2
    let y = b ?? x
    return \"\\(a || y > 0) \\(if a { 1 } else { 2 })\"
}
", [("f", 1, 5, 5)]),
  -- `repeat … while` is one, each `catch` is one, and `else if` is an `if`.
  ("loops and catches", "func f(a: Bool) {
    repeat {} while a
    while a {}
    do { try g() } catch is E {} catch {}
    if a {} else if !a {}
}
", [("f", 1, 6, 7)]),
  ("every `if case` counts", "func f(x: Int) {
    if case 1 = x {}
}
", [("f", 1, 3, 2)]),
  ("computed properties, accessors and subscripts", "final class C {
    var a: Int { flag ? 1 : 2 }
    var b: Int {
        get { if flag { return 1 }; return 2 }
        set { flag = newValue > 0 && flag }
    }
    var d = 0 {
        didSet { if d > 0 {} }
    }
    subscript(i: Int) -> Int { i > 0 ? 1 : 2 }
    deinit { if flag {} }
}
", [("a", 2, 2, 2), ("b.get", 4, 4, 2), ("b.set", 5, 5, 2), ("d.didSet", 8, 8, 2),
    ("subscript", 10, 10, 2), ("deinit", 11, 11, 2)]),
  ("a declaration starts at its attributes and modifiers", "struct S {
    @available(iOS 17, *)
    @MainActor
    public static func f() {}

    @inlinable public init() {}
}
", [("f", 2, 4, 1), ("init", 6, 6, 1)]),
  ("declarations with no body are not functions", "protocol P {
    init()
    func f()
    var v: Int { get set }
    subscript(i: Int) -> Int { get }
}
", []),
  ("a nested function is scored on its own, a closure is not", "func f(xs: [Int]) {
    func g() { if true {} }
    xs.forEach { x in if x > 0 {} }
}
", [("f", 1, 4, 2), ("g", 2, 2, 2)]),
  ("both branches of a `#if` count, its condition does not", "#if DEBUG && os(iOS)
func a() {}
#elseif os(macOS) || os(Linux)
func b() {}
#else
func c() {
    #if DEBUG
    if true {}
    #else
    while true {}
    #endif
}
#endif
", [("a", 2, 2, 1), ("b", 4, 4, 1), ("c", 6, 12, 3)]),
  ("operators and keywords as names", "func && (a: Bool, b: Bool) -> Bool { false }
func <=> (a: Int, b: Int) -> Bool { false }
func g(for x: Int, if y: Int, while z: Int) { h(for: x).if.while() }
", [("&&", 1, 1, 1), ("<=>", 2, 2, 1), ("g", 3, 3, 1)]) ]

def swiftReadsChangedFunctionsOnly : IO Unit := do
  let dir ← fixture
  write (dir / "a.swift") "func f() {}\nfunc g() {}\n"
  git dir #["init", "-q"]
  git dir #["add", "."]
  git dir #["commit", "-qm", "start"]
  write (dir / "a.swift") "func f() {}\nfunc g() { if true {} }\n"
  let out ← clocrap dir #["--json", "--diff", "HEAD"]
  let rows := rowsAt (← stdoutJson out) ["functions", "functions"]
  expectEq "functions" (rows.toList.map (str · ["name"])) [some "g"]

def swiftWithoutAToolchainIsSaid : IO Unit := do
  let dir ← fixture
  write (dir / "a.swift") "func f() {}\n"
  let out ← IO.Process.output {
    cmd := (← binary).toString, args := #["--json"], cwd := dir,
    env := #[("PATH", some "/nonexistent")] }
  expect s!"said so: {out.stderr}" (contains out.stderr "no Swift toolchain")
  expectEq "functions" (rowsAt (← stdoutJson out) ["functions", "functions"]).size 0

/-! ## Running -/

def tests : List (String × IO Unit) :=
  [ ("total lines agree with wc", totalLinesAgreeWithWc),
    ("per-language totals and table", perLanguageTotalsAndTable),
    ("files without an extension by their #! line", filesWithoutAnExtensionByShebang),
    ("C, HTML, CSS and JSON Lines", cHtmlCssAndJsonLines),
    ("gitignored files are not counted", gitignoredFilesAreNotCounted),
    ("CRAP score matches the hand-computed value", crapScoreMatchesTheHandComputedValue),
    ("threshold gate exits 1 only above it", thresholdGateExitsOneOnlyAboveIt),
    ("without coverage: complexity only, never gates", withoutCoverageComplexityOnlyAndNeverGates),
    ("--diff counts added lines and untracked files", diffCountsAddedLinesAndUntrackedFiles),
    ("--diff against an unknown ref is an error", diffAgainstAnUnknownRefIsAnError),
    ("counts the files git lists", countsTheFilesGitLists),
    ("--diff keeps functions with a changed line", diffKeepsChangedFunctions),
    ("outside git the directories are walked", outsideGitTheDirectoriesAreWalked),
    ("the table shows the worst, JSON every function", tableShowsTheWorstAndJsonEveryFunction),
    ("files the report omits count as untested", filesTheReportOmitsCountAsUntested),
    ("removed options are refused", removedOptionsAreRefused),
    ("Lean coverage comes from its C", leanCoverageComesFromItsC),
    ("Lean specialised copies belong to the callee", leanSpecialisedCopiesBelongToTheCallee),
    ("Lean inlined declarations are shown apart", leanInlinedDeclarationsAreShownApart),
    ("Lean declarations nothing calls are told apart", leanSilentDeclarations),
    ("Lean without its compiled modules stays never run", leanSilentWithoutCompiledModules),
    ("Lean symbols and spans", leanSymbolsAndSpans),
    ("Lean line kinds", leanLineKinds),
    ("Lean mangling", leanMangling),
    ("supported languages", supportedLanguages),
    ("Swift --diff keeps functions with a changed line", swiftReadsChangedFunctionsOnly),
    ("Swift without a toolchain is said", swiftWithoutAToolchainIsSaid) ] ++
  swiftCases.map (fun (name, source, expected) => (s!"Swift {name}", do
    let dir ← fixture
    write (dir / "a.swift") source
    expectEq "functions" (← swiftFunctions dir) expected)) ++
  complexityCases.map (fun c => (c.name, do
    let got := (functionsIn c.path c.source).toList.map fun f => (f.name, f.complexity)
    expectEq "functions" got c.expected)) ++
  spanCases.map (fun c => (c.name, do
    let got := (functionsIn c.path c.source).toList.map fun f => (f.name, f.startLine, f.endLine)
    expectEq "spans" got c.expected)) ++
  leanCases.map (fun (name, source, expected) => (s!"Lean {name}", do
    expectEq "functions" (leanFound source) expected))

def main : IO UInt32 := do
  let mut failed := 0
  for (name, test) in tests do
    try
      test
      IO.println s!"ok {name}"
    catch e =>
      failed := failed + 1
      IO.println s!"FAIL {name}: {e}"
  IO.println s!"{tests.length - failed} passed, {failed} failed"
  return if failed == 0 then 0 else 1
