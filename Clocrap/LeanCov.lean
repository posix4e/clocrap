import Clocrap.Bytes
import Clocrap.Function
import Clocrap.Lcov
import Clocrap.LeanLang
import Clocrap.LeanRefs

/-!
# Coverage for Lean

Read from the C that Lean compiles to. Lake writes one C file per module,
`.lake/build/ir/<Module>.c`, and Lean's C has no line directives back to the `.lean` source. Built
with LLVM source coverage (see the README), an lcov report covers those C files instead. Each C
function carries its declaration's mangled name, so the C functions are matched to the declarations
clocrap found:

- `lp_<package>_<name>` or `l_<name>` is the declaration `<name>` itself; `<name>___lam__0`,
  `<name>___redArg`, `<name>_spec__0` and the like are parts of it, so they belong to it too. Of
  several declarations whose name fits, the longest wins, so `total_go` belongs to `total.go`, not
  `total`.
- `<callee>___at___00<caller>_spec__0` is a copy of a generic callee specialised for `<caller>`: the
  callee's source compiled for the caller's types, so it belongs to the callee, and the copy may sit
  in another module's C. A chain `<a>___at___00<b>___at___00<c>…` is `<a>` specialised for `<b>`'s
  copy for `<c>`: it belongs to the first of them that is a declaration clocrap found, and to the
  caller when none of the callees is (a loop of the standard library specialised for it).
- A private declaration's name starts `__private_<Module>_0__`, and so do the compiler's private
  helpers for a public one. `main` is `_lean_main`.
- `___boxed` wrappers, `match` splitters and module initialisers are left out: wrappers and
  initialisers are glue, boxing wrappers rarely run, and a splitter is compiled for proofs (the
  `split` tactic) and never called, so each would read as untested code.

A declaration's coverage is the share of the instrumented C lines of the functions it owns that
ran. A declaration that owns none has no compiled code of its own (it was inlined, is a type, or
runs only at compile time), and has no coverage. With the report's call counts (`FNDA:`), two more
cases are told apart:

- A generic declaration whose own body was never called but whose specialised copies were: only
  the copies count, since the generic body is a template the compiled program does not use.

A declaration none of whose C was ever called takes more to read, since it may have run inside its
callers' C, where it cannot be told apart. So the C is searched for the places that use it:

- Any other function's C mentions it, whether a direct call, a closure, a `___boxed` wrapper or a
  closed term in `_init_…`: the call site exists and its count is 0, so it really never ran.
- No C mentions it, and something that ran reaches it through the declarations (see
  `Clocrap.LeanRefs`): its body was inlined. It is `inlined`, with no coverage, rather than untested.
- No C mentions it, and nothing that ran reaches it: it is `unused`, scored as never run and marked,
  as it is dead code, or runs only at compile time.

A declaration's own parts do not count as using it, and neither does a copy of something else
specialised for it. Without the C or the compiled modules to read, a declaration the compiler may
inline (see `Symbol.inline`) with no copies is taken to be `inlined`.
-/

namespace Clocrap.LeanCov

def ir : String := "/.lake/build/ir/"

/-- The report's C file for this Lean file, and the module's path (`A/B` for `A.B`). The C file is
`<root>/.lake/build/ir/<module>.c` where the Lean file is under `<root>` and ends in
`<module>.lean`; the longest module wins. -/
def cFileFor (coverage : Coverage) (leanFile : String) : Option (String × String) := Id.run do
  let mut best : Option (String × String) := none
  for path in coverage.fileList do
    let some (root, rest) := splitOnce? path ir | continue
    let some module := stripSuffix? rest ".c" | continue
    let fits := leanFile.startsWith root &&
      ((stripSuffix? leanFile ".lean").bind (stripSuffix? · module)).any (·.endsWith "/")
    if fits && best.all (fun (_, m) => module.length > m.length) then best := some (path, module)
  return best

/-- llvm-cov writes a static function as `File.c:name`. -/
def localName (name : String) : String :=
  match rsplitOnce? name ":" with
  | some (_, local_) => local_
  | none => name

/-- Whether a C name is a `match` splitter or one of its parts: a component `match_<n>.splitter`,
mangled `_match__<n>_splitter`. -/
def isSplitter (name : String) : Bool :=
  (name.splitOn "_match__").drop 1 |>.any fun rest =>
    let digits := rest.toList.takeWhile Char.isDigit |>.length
    digits > 0 && (rest.drop digits).toString.startsWith "_splitter"

/-- The value in `keys` of the declaration that the C name `candidate` is, or is a part of. A part
adds a component: `_` and a name (`_go`, `_spec__0`), or a component that itself starts with `_`
(`___lam__0`). A key followed by `__x` is another declaration whose last component goes on with an
underscore, as `Foo.bar_x` is `Foo_bar__x`. Of several keys that fit, the longest wins. -/
def lookup {α} (keys : Std.HashMap String α) (candidate : String) : Option α := Id.run do
  let cs := candidate.toList.toArray
  let mut p := cs.size
  while p > 0 do
    let fits := p == cs.size ||
      (cs[p]! == '_' && (cs[p + 1]? != some '_' || cs[p + 2]? == some '_'))
    if fits then
      if let some v := keys.get? (String.ofList (cs.extract 0 p).toList) then return some v
    p := p - 1
  return none

/-- `lookup`, and for a name with a module's private prefix, which the compiler also gives its
private helpers for a public declaration (such as a `match` splitter), the name after it. -/
def find {α} (keys : Std.HashMap String α) (candidate : String) : Option α :=
  (lookup keys candidate).orElse fun _ => do
    let rest ← stripPrefix? candidate "__private_"
    let (_, after) ← splitOnce? rest "_0__"
    lookup keys after

/-- The C name without its package prefix, or `none` for a function no declaration owns. -/
def unprefixed (name : String) (prefixes : Array String) : Option String :=
  if name.endsWith "___boxed" || isSplitter name || name.startsWith "initialize_" ||
      name.startsWith "_init_" then none
  else if name == "_lean_main" then some "main"
  else prefixes.findSome? (stripPrefix? name ·)

/-- A C name split at each `___at___`: the callee first, then each caller it was specialised for. -/
def chain (name : String) : Array String :=
  match name.splitOn "___at___" with
  | first :: rest => #[first] ++ rest.toArray.map fun s => (stripPrefix? s "00").getD s
  | [] => #[name]

/-- A chain's last part cut after its last `_spec__<n>`, as the stem and the numbers in order:
`c_spec__0_spec__2___redArg` is `c` and `["0", "2"]`. -/
def specs (last : String) : String × List String := Id.run do
  let some (before, after) := rsplitOnce? last "_spec__" | return (last, [])
  let digits := String.ofList (after.toList.takeWhile Char.isDigit)
  if digits.isEmpty then return (last, [])
  let mut stem := before
  let mut numbers := [digits]
  for _ in [0:before.length] do
    let some (b, a) := rsplitOnce? stem "_spec__" | break
    if a.isEmpty || !a.all Char.isDigit then break
    stem := b
    numbers := a :: numbers
  return (stem, numbers)

/-- Which copy of the callee `parts[k]` the C function with this `chain` is part of, named by the
callers after it. The last caller numbers its copies `_spec__<n>`, and each callee inside the copy
adds one more number, so the last `k` numbers are the inner callees', not this copy's. `___redArg`,
`___lam__0` and the like after them are parts of the copy. -/
def copyOf (parts : Array String) (k : Nat) : String :=
  let (stem, numbers) := specs parts.back!
  let mine := numbers.take (numbers.length - k)
  let last := stem ++ String.join (mine.map ("_spec__" ++ ·))
  "___at___".intercalate ((parts.extract (k + 1) (parts.size - 1)).toList ++ [last])

/-- What the coverage data says about one Lean declaration with compiled code. -/
inductive Measure where
  /-- The share of its C lines that ran. -/
  | ratio (r : Float)
  /-- Inlined into its callers, and its own C never ran: its coverage cannot be told. -/
  | inlined
  /-- Never ran, and nothing that ran reaches it. -/
  | unused
  deriving Inhabited, BEq, Repr

/-- Where a declaration whose C was never called stands. -/
inductive Silent where
  /-- Some other C mentions it, so its count of 0 is real. -/
  | hasCallSite
  | inlined
  | unused
  deriving Inhabited, BEq

/-- The instrumented C lines of some functions, how many of them ran, and the calls to them. -/
structure Tally where
  lines : Nat := 0
  ran : Nat := 0
  calls : Nat := 0
  deriving Inhabited

def Tally.add (t : Tally) (lines ran calls : Nat) : Tally :=
  { lines := t.lines + lines, ran := t.ran + ran, calls := t.calls + calls }

def Tally.plus (a b : Tally) : Tally := a.add b.lines b.ran b.calls

def Tally.ratio (t : Tally) : Float := if t.lines == 0 then 0.0 else t.ran.toFloat / t.lines.toFloat

/-- A declaration's own C functions, and the copies of it specialised for its callers, by
`copyOf`. -/
structure Owned where
  own : Option Tally := none
  copies : Std.HashMap String Tally := {}
  deriving Inhabited

/-- Whether a call to any of the declaration's C was ever counted. -/
def Owned.neverCalled (o : Owned) : Bool :=
  (o.own.all (·.calls == 0)) && o.copies.fold (init := true) fun none _ t => none && t.calls == 0

/-- The measure of a declaration from what it owns: `none` when it owns no C. `counted` is whether
the report counts calls for its module's C. With counts, a copy that was never called is left out
when another was: each copy is the same source, and an unused one shows only that its caller did
not run. `silent` says where a declaration that was never called stands, when that could be read. -/
def Owned.measure (o : Owned) (counted inline : Bool) (silent : Option Silent) : Option Measure :=
  if o.own.isNone && o.copies.isEmpty then none
  else
    let own := o.own.getD {}
    let copies := o.copies.fold (init := ({} : Tally)) fun acc _ t => acc.plus t
    let called := o.copies.fold (init := ({} : Tally)) fun acc _ t =>
      if t.calls > 0 then acc.plus t else acc
    if counted && own.calls == 0 && called.calls > 0 then some (.ratio called.ratio)
    else if counted && o.neverCalled && silent == some .inlined then some .inlined
    else if counted && o.neverCalled && silent == some .unused then some .unused
    else if counted && own.calls == 0 && silent.isNone && inline && o.copies.isEmpty then
      some .inlined
    else if counted && called.calls > 0 then some (.ratio (own.plus called).ratio)
    else some (.ratio (own.plus copies).ratio)

/-- A module's path as it appears in C names: `A/B` is `A_B`. -/
def mangledModule (module : String) : String :=
  "_".intercalate ((module.splitOn "/").map LeanLang.mangle)

/-- A C function's name with the wrapping that makes it another function of the same code removed:
`_init_` for a closed term, `___boxed` for a wrapper. -/
def unwrapped (name : String) : String :=
  let name := (stripPrefix? name "_init_").getD name
  (stripSuffix? name "___boxed").getD name

/-- The declarations a C function is part of: its own, the callee it is a copy of, and the callers
that copy is for. `decl` finds the declaration of a name without its package prefix. -/
def declsOf {α} (name : String) (prefixes : Array String) (decl : String → Option α) : Array α :=
  match prefixes.findSome? (stripPrefix? (unwrapped name) ·) with
  | none => #[]
  | some rest => (chain rest).filterMap decl

/-- Whether the line at `i` declares something rather than being part of a function's body. Bodies
are indented or start with a label, a brace or a local variable. -/
def declaration (source : ByteArray) (i : Nat) : Bool :=
  hasAt source i "LEAN_EXPORT".toUTF8 || hasAt source i "static ".toUTF8 ||
    hasAt source i "extern ".toUTF8

/-- The declarations with a name in `targets` that this C file's code mentions, added to `found`.
`starts` is the file's functions by first line. Lines that declare a function are skipped, but a
`static const` line can hold a closure over one, and belongs to the name it declares. A function's
own parts are not mentions: `owners` says what a name is part of. Module initialisers assign every
constant, and say nothing of who uses it. -/
def mentions (source : ByteArray) (starts : Array (Nat × String))
    (targets : Std.HashMap String (Nat × Nat)) (owners : String → Array (Nat × Nat))
    (found : Std.HashSet (Nat × Nat)) : Std.HashSet (Nat × Nat) := Id.run do
  let mut found := found
  let mut i := 0
  let mut line := 1
  let mut next := 0
  let mut current : Option String := none
  let isId (b : UInt8) : Bool :=
    (b >= 97 && b <= 122) || (b >= 65 && b <= 90) || (b >= 48 && b <= 57) || b == 95
  while i < source.size do
    -- At the start of a line.
    while next < starts.size && starts[next]!.1 < line do next := next + 1
    let starting := next < starts.size && starts[next]!.1 == line
    if starting then
      let name := localName starts[next]!.2
      current := if name.startsWith "initialize_" then none else some name
    let closed := hasAt source i "static const ".toUTF8
    let read := !starting && (closed || !declaration source i)
    let mut owner := if closed then none else current
    while i < source.size && source[i]! != 10 do
      let b := source[i]!
      if read && b == 108 && !isId source[i - 1]! &&
          (source[i + 1]! == 95 || (source[i + 1]! == 112 && source[i + 2]! == 95)) then
        let mut j := i
        while j < source.size && isId source[j]! do j := j + 1
        let word := String.fromUTF8! (source.extract i j)
        i := j
        match owner, closed with
        | none, true => owner := some word
        | none, false => pure ()
        | some name, _ =>
          if let some target := targets.get? (unwrapped word) then
            if !found.contains target && !(owners name).contains target then
              found := found.insert target
      else i := i + 1
    i := i + 1
    line := line + 1
  return found

/-- Where each declaration that was never called stands, by file and function. One is left out when
what would settle it cannot be read. -/
def silentDeclarations (owned : Array (Array Owned)) (cNames : Std.HashMap String (Nat × Nat))
    (sources : Array (String × Array (Nat × String) × Array String))
    (projects : Std.HashMap String (Array String)) (ran : Array String)
    (everywhere : Std.HashMap String (Nat × Nat)) :
    IO (Std.HashMap (Nat × Nat) Silent) := do
  let targets := cNames.filter fun _ (i, index) => owned[i]![index]!.neverCalled
  if targets.isEmpty then return {}
  let mut sites : Std.HashSet (Nat × Nat) := {}
  for (path, starts, prefixes) in sources do
    let source ← try IO.FS.readBinFile path catch _ => return {}
    sites := mentions source starts targets (declsOf · prefixes (find everywhere)) sites
  let mut settled : Std.HashMap (Nat × Nat) Silent := {}
  for declaration in sites do settled := settled.insert declaration .hasCallSite
  -- What is left needs the source's references. Each C file came from a module of its project.
  let mut compiled : Array (String × Array String) := #[]
  for (root, modules) in projects do
    let oleans ← modules.filterM fun m =>
      System.FilePath.pathExists s!"{root}/.lake/build/lib/lean/{m}.olean"
    if !oleans.isEmpty then
      compiled := compiled.push (root, oleans.map (s!".lake/build/lib/lean/{·}.olean"))
  if compiled.isEmpty then return settled
  let some uses ← LeanRefs.read compiled | return settled
  let nodes := uses.fold (init := ({} : Std.HashMap String String)) fun acc k _ => acc.insert k k
  let roots := ran.filterMap (find nodes)
  let live := LeanRefs.reached uses (roots.push "main")
  for (key, declaration) in everywhere do
    let (i, index) := declaration
    if settled.contains declaration || !owned[i]![index]!.neverCalled then continue
    if !nodes.contains key then continue
    settled := settled.insert declaration (if live.contains key then .inlined else .unused)
  return settled

/-- Coverage for the functions of each Lean file in `files`, given as its path and functions, in
the same order. A file's entry is `none` when the report has no C file for its module; within it,
a function's is `none` when it has no compiled code. Every C file of the report is read, since a
declaration's specialised copies may be in other modules' C. -/
def measures (coverage : Coverage) (files : Array (String × Array Function)) :
    IO (Array (Option (Array (Option Measure)))) := do
  -- Each Lean file's C file, and its declarations' C names: on their own for the file's own
  -- functions, and in one map for the copies, which may be anywhere.
  let mut byC : Std.HashMap String Nat := {}
  let mut cFiles : Array (Option String) := #[]
  let mut keys : Array (Std.HashMap String Nat) := #[]
  let mut everywhere : Std.HashMap String (Nat × Nat) := {}
  for h : i in [0:files.size] do
    let (path, functions) := files[i]
    let leanFile ← Coverage.canonicalOrSame path
    let mut mine : Std.HashMap String Nat := {}
    let mut cFile : Option String := none
    if let some (c, module) := cFileFor coverage leanFile then
      if (coverage.functionsOf c).isSome then
        cFile := some c
        byC := byC.insert c i
        let module := mangledModule module
        for h : index in [0:functions.size] do
          let some symbol := functions[index].symbol | continue
          let name := LeanLang.mangle symbol.name
          -- On a tie the last, as Rust's `max_by_key`.
          let key := if symbol.private_ then s!"__private_{module}_0__{name}" else name
          mine := mine.insert key index
          everywhere := everywhere.insert key (i, index)
    cFiles := cFiles.push cFile
    keys := keys.push mine
  let mut owned : Array (Array Owned) := files.map fun (_, fs) => Array.replicate fs.size {}
  -- Which declaration each C function belongs to, and what is needed to read each C file later.
  let mut cNames : Std.HashMap String (Nat × Nat) := {}
  let mut executed : Array String := #[]
  let mut sources : Array (String × Array (Nat × String) × Array String) := #[]
  let mut projects : Std.HashMap String (Array String) := {}
  for path in coverage.fileList do
    let some (_, rest) := splitOnce? path ir | continue
    let some module := stripSuffix? rest ".c" | continue
    let some cFunctions := coverage.functionsOf path | continue
    let here := byC.get? path
    let calls := (coverage.callsOf path).getD {}
    if let some (root, rest) := splitOnce? path ir then
      if let some file := stripSuffix? rest ".c" then
        projects := projects.insert root ((projects.getD root #[]).push file)
    let module := mangledModule module
    let starts := cFunctions.toArray
    let initializer := starts.findSome? fun (_, name) => do
      let rest ← stripPrefix? (localName name) "initialize_"
      let rest ← stripSuffix? rest module
      stripSuffix? rest "_"
    let prefixes := match initializer with
      | some package => #[s!"lp_{package}_", "l_"]
      | none => #["l_"]
    sources := sources.push (path, starts, prefixes)
    for h : n in [0:starts.size] do
      let (start, raw) := starts[n]
      let stop := match starts[n + 1]? with
        | some (next, _) => next - 1
        | none => 2 ^ 64
      let some name := unprefixed (localName raw) prefixes | continue
      let parts := chain name
      let (lines, ran) := coverage.hits path start stop
      let called := calls.getD raw 0
      if called > 0 then executed := executed ++ chain name
      -- A specialised copy belongs to its innermost callee that is a declaration: one of this
      -- module's first, else any module's.
      let callee := (parts.extract 0 (parts.size - 1)).zipIdx.findSome? fun (part, k) =>
        ((here.bind fun i => (find keys[i]! part).map (i, ·)).orElse fun _ =>
          find everywhere part).map (·, k)
      if let some ((i, index), k) := callee then
        let copy := copyOf parts k
        cNames := cNames.insert (localName raw) (i, index)
        owned := owned.modify i (·.modify index fun o =>
          { o with copies := o.copies.insert copy ((o.copies.getD copy {}).add lines ran called) })
      else
        let some i := here | continue
        let some index := find keys[i]! parts.back! | continue
        cNames := cNames.insert (localName raw) (i, index)
        owned := owned.modify i (·.modify index fun o =>
          { o with own := some ((o.own.getD {}).add lines ran called) })
  let silent ← silentDeclarations owned cNames sources projects executed everywhere
  return (files.zipIdx.zip (cFiles.zip owned)).map fun (((_, functions), i), (cFile, mine)) => do
    let cFile ← cFile
    let counted := (coverage.callsOf cFile).isSome
    return (functions.zipIdx.zip mine).map fun ((f, index), o) =>
      o.measure counted ((f.symbol.map (·.inline)).getD false) (silent.get? (i, index))

end Clocrap.LeanCov
