import Clocrap.Crap
import Clocrap.Json
import Clocrap.Num
import Clocrap.Walk

/-!
# Reports

Turns scan results into the tables and JSON that the command prints.
-/

namespace Clocrap.Report

/-- Line totals for one language. -/
structure LanguageTotal where
  files : Nat := 0
  counts : LineCounts := {}
  deriving Inhabited

def LanguageTotal.add (t : LanguageTotal) (counts : LineCounts) : LanguageTotal :=
  { files := t.files + 1, counts := t.counts.add counts }

/-- Groups file reports by language, in `Language.all` order. Languages with no files are left
out. -/
def byLanguage (reports : Array FileReport) : Array (Language × LanguageTotal) :=
  Language.all.filterMap fun language =>
    let total := reports.foldl (init := ({} : LanguageTotal)) fun t r =>
      if r.language == language then t.add r.counts else t
    if total.files == 0 then none else some (language, total)

/-- The sum of every report. -/
def grandTotal (reports : Array FileReport) : LanguageTotal :=
  reports.foldl (init := {}) fun t r => t.add r.counts

/-- The path shown to the user: relative to `cwd` when the file is under it. -/
def displayPath (path cwd : String) : String :=
  if path == cwd then ""
  else if cwd == "/" then (stripPrefix? path "/").getD path
  else (stripPrefix? path (cwd ++ "/")).getD path

/-- Column widths count bytes, as Rust's `len()`, while padding counts characters, as its
`format!` does. -/
def width (s : String) : Nat := s.utf8ByteSize

def padRight (s : String) (w : Nat) : String := s ++ String.ofList (List.replicate (w - s.length) ' ')
def padLeft (s : String) (w : Nat) : String := String.ofList (List.replicate (w - s.length) ' ') ++ s

def cellsFor (t : LanguageTotal) : Array String :=
  #[toString t.files, toString t.counts.blank, toString t.counts.comment, toString t.counts.code]

/-- The per-language table, largest code count first, with a total row. -/
def table (reports : Array FileReport) : String := Id.run do
  let rows := (byLanguage reports).toList.mergeSort (fun a b =>
    a.2.counts.code > b.2.counts.code ||
      (a.2.counts.code == b.2.counts.code && a.1.name ≤ b.1.name)) |>.toArray
  let sum := cellsFor (grandTotal reports)
  let cells := rows.map (cellsFor ·.2)
  let header := #["files", "blank", "comment", "code"]
  let nameWidth := (rows.map (width ·.1.name) ++ #["Language".length, "SUM:".length]).foldl max 0
  let numberWidth := ((cells.flatMap id) ++ sum ++ header).foldl (fun m c => max m (width c)) 0
  let rule := String.ofList (List.replicate (nameWidth + 4 * (numberWidth + 2)) '-')
  let line (name : String) (row : Array String) : String :=
    padRight name nameWidth ++ String.join (row.toList.map fun c => "  " ++ padLeft c numberWidth) ++ "\n"
  let mut out := line "Language" header ++ rule ++ "\n"
  for ((language, _), row) in rows.zip cells do out := out ++ line language.name row
  return out ++ rule ++ "\n" ++ line "SUM:" sum

def countsJson (c : LineCounts) : Array (String × Json) :=
  #[("blank", .nat c.blank), ("comment", .nat c.comment), ("code", .nat c.code)]

/-- The JSON document for a scan: per-language totals, the grand total and the per-file rows. -/
def jsonCounts (reports : Array FileReport) (cwd : String) : Array (String × Json) :=
  let languages := (byLanguage reports).map fun (language, total) =>
    Json.obj (#[("language", .str language.name), ("files", .nat total.files)] ++ countsJson total.counts)
  let total := grandTotal reports
  #[("languages", Json.arr languages),
    ("total", .obj (#[("files", .nat total.files)] ++ countsJson total.counts)),
    ("files", .arr (reports.map fun r =>
      .obj (#[("path", .str (displayPath r.path cwd)), ("language", .str r.language.name)] ++
        countsJson r.counts)))]

/-- The cells of one row of the functions table. -/
def functionCells (s : Crap.Scored) (cwd : String) (hasCoverage : Bool) (threshold : Float) :
    Array String :=
  let location := s!"{displayPath s.path cwd}:{s.function.startLine}"
  let complexity := toString s.function.complexity
  if !hasCoverage then #[complexity, s.function.name, location]
  else
    let over := if s.crap.any (· > threshold) then " OVER" else ""
    #[(s.crap.map (Num.fixed · 1)).getD "-", complexity,
      (s.coverage.map fun r => Num.fixed (r * 100.0) 0 ++ "%").getD "-", s.function.name,
      location ++ over ++ (if s.unused then " UNUSED" else "")]

/-- Functions the table shows when none is over the threshold. -/
def shownFunctions : Nat := 20

/-- The lines under the functions table: what the table cut, the gate's count, and what was left
out or counted as untested. -/
def functionNotes (ranking : Crap.Ranking) (threshold : Float) (hidden : Nat) : String := Id.run do
  let scored := ranking.functions
  let cut := if hidden > 0 then s!"\n{hidden} more functions; --json lists them all\n" else ""
  if scored[0]!.crap.isNone then
    return cut ++ "\nno coverage data, so CRAP is not computed: complexity only (pass --lcov)\n"
  let over := Crap.overThreshold scored threshold
  let mut out := cut ++ s!"\n{over} of {scored.size} functions above the CRAP threshold of {Num.display threshold}\n"
  if ranking.noCode > 0 then
    out := out ++ s!"{ranking.noCode} Lean functions compiled to no code of their own (inlined, a type, or compile-time only), so have no coverage and were left out\n"
  if ranking.inlined > 0 then
    out := out ++ s!"{ranking.inlined} Lean functions were inlined into their callers and their own C never ran, so their coverage cannot be told and they were left out\n"
  let unused : Nat := scored.foldl (fun n s => if s.unused then n + 1 else n) 0
  if unused > 0 then
    out := out ++ s!"{unused} Lean functions never ran and nothing that ran reaches them: dead code, or run only at compile time\n"
  let unlisted : Nat := scored.foldl (fun n s => if s.missingFromReport then n + 1 else n) 0
  if unlisted > 0 then
    out := out ++ s!"{unlisted} functions in files the coverage report does not list count as 0% covered\n"
  return out

/-- The worst functions, and every one above `threshold`. With coverage the table shows the CRAP
score and flags each function above `threshold`. Without coverage it shows complexity only. -/
def functions (ranking : Crap.Ranking) (cwd : String) (threshold : Float) : String := Id.run do
  let scored := ranking.functions
  if scored.isEmpty then return "no functions found\n"
  let hasCoverage := scored[0]!.crap.isSome
  let header := if hasCoverage then #["CRAP", "complexity", "coverage", "function", "location"]
    else #["complexity", "function", "location"]
  -- Worst first, so what is over the threshold comes before what is cut.
  let shown := scored.extract 0 (max shownFunctions (Crap.overThreshold scored threshold))
  let rows := shown.map (functionCells · cwd hasCoverage threshold)
  let widths := (Array.range header.size).map fun column =>
    rows.foldl (fun m row => max m (width row[column]!)) (width header[column]!)
  -- The function name is left-aligned, and so is the location, which ends the row. Every other
  -- column is right-aligned.
  let nameColumn := if hasCoverage then 3 else 1
  let last := header.size - 1
  let line (cells : Array String) : String :=
    let padded := (cells.zipIdx).map fun (cell, column) =>
      if column == last || column == nameColumn then padRight cell widths[column]!
      else padLeft cell widths[column]!
    trimEnd ("  ".intercalate padded.toList) ++ "\n"
  let mut out := line header
  for row in rows do out := out ++ line row
  return out ++ functionNotes ranking threshold (scored.size - shown.size)

/-- The CRAP section of the JSON document. -/
def jsonFunctions (ranking : Crap.Ranking) (cwd : String) (threshold : Float) : Json :=
  let functions := ranking.functions.map fun s => Json.obj #[
    ("path", .str (displayPath s.path cwd)), ("name", .str s.function.name),
    ("line", .nat s.function.startLine), ("end_line", .nat s.function.endLine),
    ("complexity", .nat s.function.complexity), ("coverage", .option .float s.coverage),
    ("crap", .option .float s.crap), ("missing_from_report", .bool s.missingFromReport),
    ("unused", .bool s.unused)]
  .obj #[("threshold", .float threshold),
    ("over_threshold", .nat (Crap.overThreshold ranking.functions threshold)),
    ("no_code", .nat ranking.noCode), ("inlined", .nat ranking.inlined),
    ("functions", .arr functions)]

end Clocrap.Report
