import Clocrap.Str
/-!
# Ignore files

Trees outside git honour `.gitignore` the way ripgrep's `ignore` crate does with
`require_git(false)`, which the Rust clocrap used:

- Each directory may hold a `.ignore` and a `.gitignore`; a directory with `.git` also has
  `.git/info/exclude`; the user's global excludes file applies everywhere.
- Ignore files in the directories above a root apply too. A `.gitignore` above a directory that
  holds `.git` does not, since it belongs to another repository.
- For one entry the deepest directory whose files say anything decides: `.ignore` first, then
  `.gitignore`, then `info/exclude`; the global file last. Within one file the last matching line
  wins, so `!` can re-include what an earlier line ignored.
- Hidden entries (a name starting with `.`) are skipped unless a `!` line re-includes them.

A line is a glob: `*` and `?` stay within one path component, `[...]` is a class, `**` spans
components. A line with a `/` before its end is anchored to its file's directory; one without
matches at any depth. A trailing `/` matches directories only.
-/

namespace Clocrap.Gitignore

inductive Tok where
  | lit (c : Char)
  | any
  | star
  /-- `**/` at the start or after a `/`: zero or more whole components. -/
  | globDir
  /-- `/**` at the end: everything below. -/
  | globRest
  | cls (negated : Bool) (items : Array (Char × Char))
  deriving Inhabited, Repr

/-- Compiles one glob into tokens. -/
partial def compile (glob : String) : Array Tok := Id.run do
  let cs := glob.toList.toArray
  let mut out := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '\\' && i + 1 < cs.size then
      out := out.push (.lit cs[i+1]!)
      i := i + 2
    else if c == '*' then
      if i + 1 < cs.size && cs[i+1]! == '*' then
        let atStart := i == 0 || cs[i-1]! == '/'
        let atEnd := i + 2 == cs.size
        if atStart && i + 2 < cs.size && cs[i+2]! == '/' then
          out := out.push .globDir
          i := i + 3
        else if atStart && atEnd && i > 0 then
          -- `a/**`: drop the `/` already pushed.
          out := out.pop.push .globRest
          i := i + 2
        else if atStart && atEnd then
          out := out.push .globDir |>.push .star
          i := i + 2
        else
          out := out.push .star
          i := i + 2
      else
        out := out.push .star
        i := i + 1
    else if c == '?' then
      out := out.push .any
      i := i + 1
    else if c == '[' then
      -- A class runs to the next `]` that is not its first character.
      let mut j := i + 1
      let negated := j < cs.size && (cs[j]! == '!' || cs[j]! == '^')
      if negated then j := j + 1
      let first := j
      while j < cs.size && (cs[j]! != ']' || j == first) do j := j + 1
      if j ≥ cs.size then
        out := out.push (.lit '[')
        i := i + 1
      else
        let body := cs.extract first j
        let mut items := #[]
        let mut k := 0
        while k < body.size do
          if k + 2 < body.size && body[k+1]! == '-' then
            items := items.push (body[k]!, body[k+2]!)
            k := k + 3
          else
            items := items.push (body[k]!, body[k]!)
            k := k + 1
        out := out.push (.cls negated items)
        i := j + 1
    else
      out := out.push (.lit c)
      i := i + 1
  return out

/-- Whether `toks` from `ti` matches `path` from `pi`. -/
partial def matchFrom (toks : Array Tok) (path : Array Char) (ti pi : Nat) : Bool :=
  if ti ≥ toks.size then pi ≥ path.size
  else match toks[ti]! with
    | .lit c => pi < path.size && path[pi]! == c && matchFrom toks path (ti + 1) (pi + 1)
    | .any => pi < path.size && path[pi]! != '/' && matchFrom toks path (ti + 1) (pi + 1)
    | .cls negated items =>
      pi < path.size && path[pi]! != '/' &&
        (let c := path[pi]!
         let inside := items.any fun (lo, hi) => lo ≤ c && c ≤ hi
         inside != negated) &&
        matchFrom toks path (ti + 1) (pi + 1)
    | .star =>
      -- Any run of characters within one component.
      let rec star (k : Nat) : Bool :=
        matchFrom toks path (ti + 1) k || (k < path.size && path[k]! != '/' && star (k + 1))
      star pi
    | .globDir =>
      -- Zero or more whole components: try here, then after each later `/`.
      let rec dirs (k : Nat) : Bool :=
        matchFrom toks path (ti + 1) k ||
          (match (path.extract k path.size).findIdx? (· == '/') with
           | some d => dirs (k + d + 1)
           | none => false)
      dirs pi
    | .globRest => pi < path.size && path[pi]! == '/' && pi + 1 < path.size

/-- Whether the glob matches the whole of `path`. -/
def globMatches (toks : Array Tok) (path : String) : Bool :=
  matchFrom toks path.toList.toArray 0 0

structure Pattern where
  toks : Array Tok
  whitelist : Bool
  onlyDir : Bool
  deriving Inhabited

/-- The patterns of one ignore file, matched against paths relative to `root`. -/
structure Matcher where
  root : String
  patterns : Array Pattern
  deriving Inhabited

/-- Trailing spaces end a pattern unless a backslash escapes the last one. -/
def trimTrailing (line : String) : String := Id.run do
  let cs := line.toList.toArray
  let mut stop := cs.size
  while stop > 0 && cs[stop - 1]! == ' ' && !(stop ≥ 2 && cs[stop - 2]! == '\\') do
    stop := stop - 1
  return String.ofList (cs.extract 0 stop).toList

/-- Parses an ignore file's text. -/
def parse (root text : String) : Matcher := Id.run do
  let mut patterns := #[]
  for raw in text.splitOn "\n" do
    let line := trimTrailing (if raw.endsWith "\r" then raw.dropRight 1 else raw)
    if line.isEmpty || line.startsWith "#" then continue
    let mut glob := line
    let mut whitelist := false
    if glob.startsWith "!" then
      whitelist := true
      glob := glob.dropS 1
    else if glob.startsWith "\\!" || glob.startsWith "\\#" then
      glob := glob.dropS 1
    let mut onlyDir := false
    if glob.endsWith "/" && glob.length > 1 then
      onlyDir := true
      glob := glob.dropRight 1
    if glob.isEmpty then continue
    -- A `/` anywhere but the end anchors the pattern; otherwise it matches at any depth.
    let anchored := glob.contains '/'
    if glob.startsWith "/" then glob := glob.dropS 1
    if !anchored && !glob.startsWith "**/" then glob := "**/" ++ glob
    patterns := patterns.push ⟨compile glob, whitelist, onlyDir⟩
  return ⟨root, patterns⟩

/-- What the file says about `path`, an absolute path under its root: `some true` to ignore,
`some false` to re-include, `none` when no line matches. The last matching line wins. -/
def Matcher.matched (m : Matcher) (path : String) (isDir : Bool) : Option Bool := Id.run do
  let prefix_ := if m.root.endsWith "/" then m.root else m.root ++ "/"
  if !path.startsWith prefix_ then return none
  let rel := path.dropS prefix_.length
  let mut found := none
  for p in m.patterns do
    if p.onlyDir && !isDir then continue
    if globMatches p.toks rel then found := some !p.whitelist
  return found

/-- Reads an ignore file, or `none` when there is none. -/
def load (root : String) (file : System.FilePath) : IO (Option Matcher) := do
  try
    if !(← file.pathExists) || (← file.isDir) then return none
    let text ← IO.FS.readFile file
    return some (parse root text)
  catch _ => return none

/-- The ignore files of one directory. -/
structure Level where
  dir : String
  custom : Option Matcher
  gitignore : Option Matcher
  exclude : Option Matcher
  hasGit : Bool
  deriving Inhabited

def Level.read (dir : String) : IO Level := do
  let d : System.FilePath := dir
  let hasGit ← (d / ".git").pathExists
  return {
    dir
    custom := ← load dir (d / ".ignore")
    gitignore := ← load dir (d / ".gitignore")
    exclude := ← if hasGit then load dir (d / ".git" / "info" / "exclude") else pure none
    hasGit }

/-- The global excludes file: git's `core.excludesFile`, or `$XDG_CONFIG_HOME/git/ignore`, or
`~/.config/git/ignore`. Its patterns match relative to the current directory. -/
def global (cwd : String) : IO (Option Matcher) := do
  let configured ← try
      let out ← IO.Process.output { cmd := "git", args := #["config", "--path", "--get", "core.excludesFile"] }
      pure (if out.exitCode == 0 then some out.stdout.trimS else none)
    catch _ => pure none
  let path ← match configured with
    | some p => pure (some p)
    | none =>
      match ← IO.getEnv "XDG_CONFIG_HOME" with
      | some x => pure (some s!"{x}/git/ignore")
      | none => pure ((← IO.getEnv "HOME").map (· ++ "/.config/git/ignore"))
  match path with
  | some p => load cwd p
  | none => return none

/-- The decision for an entry under `levels` (deepest last): `some true` ignored, `some false`
re-included, `none` when no file says anything. -/
def decide (levels : Array Level) (globalM : Option Matcher) (path : String) (isDir : Bool) :
    Option Bool := Id.run do
  let mut custom : Option Bool := none
  let mut ignore : Option Bool := none
  let mut exclude : Option Bool := none
  let mut sawGit := false
  for level in levels.reverse do
    if custom.isNone then custom := level.custom.bind (·.matched path isDir)
    if !sawGit then
      if ignore.isNone then ignore := level.gitignore.bind (·.matched path isDir)
      if exclude.isNone then exclude := level.exclude.bind (·.matched path isDir)
    sawGit := sawGit || level.hasGit
  let g := globalM.bind (·.matched path isDir)
  return custom <|> ignore <|> exclude <|> g

end Clocrap.Gitignore
