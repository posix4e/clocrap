import Clocrap.Crap
import Clocrap.Diff
import Clocrap.Json
import Clocrap.Lcov
import Clocrap.Num
import Clocrap.Report
import Clocrap.Walk

/-!
# The `clocrap` command

See the README for usage.
-/

namespace Clocrap.Cli

def version : String := "0.1.0"

def usage : String := "Usage: clocrap [OPTIONS] [PATHS]..."

def help : String := s!"Count source lines by language, and score functions by CRAP

{usage}

Arguments:
  [PATHS]...  Files or directories to count. Defaults to the current directory

Options:
      --json            Print JSON instead of tables
      --by-file         Also print one row per file, in path order
      --walk            Count every recognised file under the paths by walking the directories,
                        instead of the files git lists (tracked files, plus untracked files git
                        does not ignore). A walk skips hidden files
      --diff <REF>      Count only the lines added or changed since this git ref
      --crap            Find every function and report its cyclomatic complexity. Implied by
                        --lcov, which also scores CRAP
      --lcov <FILE>     An lcov coverage file, as `cargo llvm-cov --lcov` writes. Repeat the flag
                        to merge several. Turns complexity into CRAP scores
      --threads <N>     Worker threads that read files. Zero picks four, the most that file opens
                        scale to on macOS [default: 0]
      --count-unlisted  Score functions in files the coverage report does not list (such as test
                        code) as untested. By default they are left out
      --threshold <N>   Exit with status 1 when a function's CRAP score is above this. Only applies
                        with --lcov [default: 30]
  -h, --help            Print help
  -V, --version         Print version
"

structure Options where
  paths : Array String := #[]
  json : Bool := false
  byFile : Bool := false
  walk : Bool := false
  diff : Option String := none
  crap : Bool := false
  lcov : Array String := #[]
  threads : Nat := 0
  countUnlisted : Bool := false
  threshold : Float := Crap.defaultThreshold

/-- What the command line asks for. -/
inductive Parsed where
  | run (o : Options)
  | help
  | version

def valueFlags : Array String := #["--diff", "--lcov", "--threads", "--threshold"]

def setValue (o : Options) (flag value : String) : Except String Options :=
  match flag with
  | "--diff" => .ok { o with diff := some value }
  | "--lcov" => .ok { o with lcov := o.lcov.push value }
  | "--threads" => match value.toNat? with
    | some n => .ok { o with threads := n }
    | none => .error s!"invalid value '{value}' for '--threads <N>': invalid digit found in string"
  | _ => match Num.parse? value with
    | some x => .ok { o with threshold := x }
    | none => .error s!"invalid value '{value}' for '--threshold <N>': invalid float literal"

def setSwitch (o : Options) (flag : String) : Option Options :=
  match flag with
  | "--json" => some { o with json := true }
  | "--by-file" => some { o with byFile := true }
  | "--walk" => some { o with walk := true }
  | "--crap" => some { o with crap := true }
  | "--count-unlisted" => some { o with countUnlisted := true }
  | _ => none

/-- Reads the arguments the way clap did: flags anywhere, `--flag value` or `--flag=value`, and
everything after `--` a path. -/
partial def parse (args : List String) : Except String Parsed := do
  let rec go (args : List String) (o : Options) (rest : Bool) : Except String Parsed :=
    match args with
    | [] => .ok (.run o)
    | a :: more =>
      if rest || a == "-" || !a.startsWith "-" then go more { o with paths := o.paths.push a } rest
      else if a == "--" then go more o true
      else if a == "-h" || a == "--help" then .ok .help
      else if a == "-V" || a == "--version" then .ok .version
      else
        let (flag, inline) := match splitOnce? a "=" with
          | some (f, v) => (f, some v)
          | none => (a, none)
        if valueFlags.contains flag then
          match inline, more with
          | some v, _ => do go more (← setValue o flag v) false
          | none, v :: more' => do go more' (← setValue o flag v) false
          | none, [] => .error s!"a value is required for '{flag} <{if flag == "--diff" then "REF" else if flag == "--lcov" then "FILE" else "N"}>' but none was supplied"
        else match inline, setSwitch o flag with
          | none, some o' => go more o' false
          | some _, some _ => .error s!"unexpected value for '{flag}'"
          | _, none => .error s!"unexpected argument '{a}' found"
  go args {} false

def runWith (o : Options) : IO UInt32 := do
  let cwd ← (do return (← IO.FS.realPath (← IO.currentDir)).toString)
  let roots := if o.paths.isEmpty then #["."] else o.paths
  let changed ← match o.diff with
    | some ref => some <$> Diff.changedSince roots ref
    | none => pure none
  let wantCrap := o.crap || !o.lcov.isEmpty
  let reports ← scan roots {
    listing := if o.walk then .walk else .vcs, changed, functions := wantCrap, threads := o.threads }
  let coverage ← if o.lcov.isEmpty then pure none else some <$> Coverage.read o.lcov
  let ranking ← if wantCrap then some <$> Crap.rank reports coverage o.countUnlisted else pure none
  let out ← if o.json then
      let mut document := Report.jsonCounts reports cwd o.byFile
      if let some r := ranking then document := document.push ("functions", Report.jsonFunctions r cwd o.threshold)
      pure ((Json.obj document).render ++ "\n")
    else
      let mut out := ""
      if o.byFile then out := Report.byFile reports cwd ++ "\n"
      out := out ++ Report.table reports
      if let some r := ranking then
        out := out ++ "\n" ++ Report.functions r cwd o.threshold o.countUnlisted
      pure out
  let stdout ← IO.getStdout
  stdout.putStr out
  stdout.flush
  -- The gate needs coverage: without it, CRAP is not defined.
  if let (some r, some _) := (ranking, coverage) then
    let over := Crap.overThreshold r.functions o.threshold
    if over > 0 then
      IO.eprintln s!"clocrap: {over} function(s) above the CRAP threshold of {Num.display o.threshold}"
      return 1
  return 0

def main (args : List String) : IO UInt32 := do
  match parse args with
  | .error message =>
    IO.eprintln s!"error: {message}\n\n{usage}\n\nFor more information, try '--help'."
    return 2
  | .ok .help =>
    IO.print help
    return 0
  | .ok .version =>
    IO.println s!"clocrap {version}"
    return 0
  | .ok (.run o) =>
    try runWith o
    catch e =>
      IO.eprintln s!"clocrap: {e}"
      return 2

end Clocrap.Cli
