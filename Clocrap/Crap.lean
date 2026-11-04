import Clocrap.Bytes
import Clocrap.Function
import Clocrap.Lcov
import Clocrap.LeanCov
import Clocrap.Walk

/-!
# CRAP

The CRAP score of each function (Change Risk Anti-Patterns):

```text
CRAP(m) = comp(m)^2 * (1 - cov(m))^3 + comp(m)
```

`comp` is the function's cyclomatic complexity and `cov` is the share of its lines that the tests
ran, from 0 to 1. A function with complexity 1 and full coverage scores 1; a complex function with
no tests scores comp² + comp.
-/

namespace Clocrap.Crap

/-- The usual CRAP limit. A function above it is a risk. -/
def defaultThreshold : Float := 30.0

/-- The CRAP score for a function of the given complexity and coverage. The coverage is clamped to
0 through 1. -/
def score (complexity : Nat) (coverage : Float) : Float :=
  let comp := complexity.toFloat
  let clamped := if coverage < 0.0 then 0.0 else if coverage > 1.0 then 1.0 else coverage
  let uncovered := 1.0 - clamped
  comp * comp * (uncovered * uncovered * uncovered) + comp

/-- One function with its measures. -/
structure Scored where
  path : String
  function : Function
  /-- Share of the function's instrumented lines that ran. `none` when no coverage data was
  given. -/
  coverage : Option Float
  /-- The CRAP score. `none` when no coverage data was given, because the score needs coverage. -/
  crap : Option Float
  /-- Whether the coverage data has a record for the file. When it does not, `coverage` is 0: the
  file is counted as untested. -/
  missingFromReport : Bool
  deriving Inhabited

/-- The functions of a scan, worst first, and how many were left out. -/
structure Ranking where
  functions : Array Scored
  /-- Functions in files the coverage report does not list, left out because the caller did not
  ask to count them. -/
  leftOut : Nat
  /-- Lean functions in files the report covers that have no compiled code of their own (inlined,
  a type, or compile-time only), so no coverage. -/
  noCode : Nat
  /-- Lean functions the compiler inlines into their callers whose own C never ran, so their
  coverage cannot be told. -/
  inlined : Nat

/-- What the coverage data says about one function. -/
inductive Found where
  | ratio (r : Float)
  /-- The report has no record of the function's file. -/
  | unlisted
  /-- The report covers the file, but the function compiled to no code. -/
  | noCode
  /-- Lean only: the function ran, if at all, inlined into its callers. -/
  | inlined

/-- Worst first: by CRAP score when both have one, else by complexity; then by path and line. -/
def order (a b : Scored) : Ordering :=
  let byRisk : Ordering := match a.crap, b.crap with
    | some x, some y => if y < x then .lt else if x < y then .gt else .eq
    | _, _ => compare b.function.complexity a.function.complexity
  let byPath : Ordering :=
    if pathLt a.path b.path then .lt else if pathLt b.path a.path then .gt else .eq
  byRisk.then byPath
    |>.then (compare a.function.startLine b.function.startLine)

/-- Every function in `reports`, worst first. With coverage the order is by CRAP score; without
it, by complexity, and the scores are `none`.

A file the coverage report does not list is usually one it leaves out on purpose, such as test
code. Its functions are left out unless `countUnlisted` is set, in which case they count as 0%
covered. -/
def rank (reports : Array FileReport) (coverage : Option Coverage) (countUnlisted : Bool) :
    IO Ranking := do
  let mut scored := #[]
  let mut leftOut := 0
  let mut noCode := 0
  let mut inlined := 0
  -- Lean's coverage is of the C it compiles to, matched by name across every module's C.
  let leanReports := reports.filter (·.language == .lean)
  let leanMeasures ← match coverage with
    | some data => LeanCov.measures data (leanReports.map fun r => (r.path, r.functions))
    | none => pure #[]
  let mut nextLean := 0
  for report in reports do
    let lean := if report.language == .lean then leanMeasures[nextLean]? else none
    if report.language == .lean then nextLean := nextLean + 1
    let key ← match coverage with
      | some data => data.resolve report.path
      | none => pure report.path
    for h : index in [0:report.functions.size] do
      let function := report.functions[index]
      let mut cov : Option Float := none
      let mut missing := false
      if let some data := coverage then
        let found := match lean with
          | some (some perFunction) => match perFunction[index]! with
            | some (.ratio r) => Found.ratio r
            | some .inlined => .inlined
            | none => .noCode
          | some none => .unlisted
          | none => match data.ratio key function.startLine function.endLine with
            | some r => .ratio r
            | none => .unlisted
        match found with
        | .ratio r => cov := some r
        | .unlisted =>
          if countUnlisted then
            cov := some 0.0
            missing := true
          else
            leftOut := leftOut + 1
            continue
        | .noCode =>
          noCode := noCode + 1
          continue
        | .inlined =>
          inlined := inlined + 1
          continue
      scored := scored.push {
        path := report.path, function, coverage := cov,
        crap := cov.map (score function.complexity ·), missingFromReport := missing }
  let sorted := scored.toList.mergeSort (fun a b => order a b != .gt) |>.toArray
  return { functions := sorted, leftOut, noCode, inlined }

/-- How many functions score above `threshold`. -/
def overThreshold (scored : Array Scored) (threshold : Float) : Nat :=
  scored.foldl (init := 0) fun n s => if s.crap.any (· > threshold) then n + 1 else n

end Clocrap.Crap
