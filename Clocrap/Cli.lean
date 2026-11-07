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
      --json            Print JSON instead of tables, with every file and function
      --diff <REF>      Count only the lines added or changed since this git ref
      --lcov <FILE>     An lcov coverage file, as `cargo llvm-cov --lcov` writes. Repeat the flag
                        to merge several. Turns complexity into CRAP scores
      --threshold <N>   Exit with status 1 when a function's CRAP score is above this. Only applies
                        with --lcov [default: 30]
  -h, --help            Print help
  -V, --version         Print version
"

structure Options where
  paths : Array String := #[]
  json : Bool := false
  diff : Option String := none
  lcov : Array String := #[]
  threshold : Float := Crap.defaultThreshold

/-- What the command line asks for. -/
inductive Parsed where
  | run (o : Options)
  | help
  | version

def valueFlags : Array String := #["--diff", "--lcov", "--threshold"]

def setValue (o : Options) (flag value : String) : Except String Options :=
  match flag with
  | "--diff" => .ok { o with diff := some value }
  | "--lcov" => .ok { o with lcov := o.lcov.push value }
  | _ => match Num.parse? value with
    | some x => .ok { o with threshold := x }
    | none => .error s!"invalid value '{value}' for '--threshold <N>': invalid float literal"

def setSwitch (o : Options) (flag : String) : Option Options :=
  match flag with
  | "--json" => some { o with json := true }
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
  let reports ← scan roots changed
  let coverage ← if o.lcov.isEmpty then pure none else some <$> Coverage.read o.lcov
  let ranking ← Crap.rank reports coverage
  let out := if o.json then
      let document := (Report.jsonCounts reports cwd).push
        ("functions", Report.jsonFunctions ranking cwd o.threshold)
      (Json.obj document).render ++ "\n"
    else
      Report.table reports ++ "\n" ++ Report.functions ranking cwd o.threshold
  let stdout ← IO.getStdout
  stdout.putStr out
  stdout.flush
  -- The gate needs coverage: without it, CRAP is not defined.
  if coverage.isSome then
    let over := Crap.overThreshold ranking.functions o.threshold
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
