//! Turns scan results into the table, per-file listing and JSON that the
//! command prints.

use std::collections::BTreeMap;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use serde_json::{Value, json};

use crate::count::LineCounts;
use crate::crap::{Ranking, Scored};
use crate::lang::Language;
use crate::walk::FileReport;

/// Line totals for one language.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct LanguageTotal {
    pub files: u64,
    pub counts: LineCounts,
}

/// Groups file reports by language. Languages with no files are left out.
#[must_use]
pub fn by_language(reports: &[FileReport]) -> BTreeMap<Language, LanguageTotal> {
    let mut totals: BTreeMap<Language, LanguageTotal> = BTreeMap::new();
    for report in reports {
        let total = totals.entry(report.language).or_default();
        total.files += 1;
        total.counts.add(&report.counts);
    }
    totals
}

/// The sum of every report.
#[must_use]
pub fn grand_total(reports: &[FileReport]) -> LanguageTotal {
    let mut total = LanguageTotal::default();
    for report in reports {
        total.files += 1;
        total.counts.add(&report.counts);
    }
    total
}

/// The path shown to the user: relative to `cwd` when the file is under it.
#[must_use]
pub fn display_path(path: &Path, cwd: &Path) -> PathBuf {
    path.strip_prefix(cwd).unwrap_or(path).to_path_buf()
}

/// Writes the per-language table, largest code count first, with a total row.
///
/// # Errors
///
/// Returns any error from writing to `out`.
pub fn write_table(out: &mut impl Write, reports: &[FileReport]) -> io::Result<()> {
    let mut rows: Vec<(&str, LanguageTotal)> = by_language(reports)
        .into_iter()
        .map(|(language, total)| (language.name(), total))
        .collect();
    rows.sort_by(|a, b| b.1.counts.code.cmp(&a.1.counts.code).then(a.0.cmp(b.0)));

    let sum = cells_for(&grand_total(reports));
    let cells: Vec<[String; 4]> = rows.iter().map(|(_, total)| cells_for(total)).collect();
    let name_width = rows
        .iter()
        .map(|(name, _)| name.len())
        .chain(["Language".len(), "SUM:".len()])
        .max()
        .unwrap_or(0);
    let number_width = cells
        .iter()
        .flatten()
        .chain(sum.iter())
        .map(String::len)
        .chain(
            ["files", "blank", "comment", "code"]
                .iter()
                .map(|h| h.len()),
        )
        .max()
        .unwrap_or(0);

    let header = ["files", "blank", "comment", "code"];
    let rule = "-".repeat(name_width + 4 * (number_width + 2));
    writeln!(
        out,
        "{:<name_width$}  {:>number_width$}  {:>number_width$}  {:>number_width$}  {:>number_width$}",
        "Language", header[0], header[1], header[2], header[3],
    )?;
    writeln!(out, "{rule}")?;
    for ((name, _), row) in rows.iter().zip(&cells) {
        writeln!(
            out,
            "{name:<name_width$}  {:>number_width$}  {:>number_width$}  {:>number_width$}  {:>number_width$}",
            row[0], row[1], row[2], row[3],
        )?;
    }
    writeln!(out, "{rule}")?;
    writeln!(
        out,
        "{:<name_width$}  {:>number_width$}  {:>number_width$}  {:>number_width$}  {:>number_width$}",
        "SUM:", sum[0], sum[1], sum[2], sum[3],
    )?;
    Ok(())
}

fn cells_for(total: &LanguageTotal) -> [String; 4] {
    [
        total.files.to_string(),
        total.counts.blank.to_string(),
        total.counts.comment.to_string(),
        total.counts.code.to_string(),
    ]
}

/// Writes one row per file, in path order.
///
/// # Errors
///
/// Returns any error from writing to `out`.
pub fn write_by_file(out: &mut impl Write, reports: &[FileReport], cwd: &Path) -> io::Result<()> {
    let rows: Vec<[String; 5]> = reports
        .iter()
        .map(|report| {
            [
                display_path(&report.path, cwd).display().to_string(),
                report.language.name().to_string(),
                report.counts.blank.to_string(),
                report.counts.comment.to_string(),
                report.counts.code.to_string(),
            ]
        })
        .collect();
    let path_width = rows
        .iter()
        .map(|r| r[0].len())
        .max()
        .unwrap_or(0)
        .max("File".len());
    let lang_width = rows
        .iter()
        .map(|r| r[1].len())
        .max()
        .unwrap_or(0)
        .max("Language".len());
    writeln!(
        out,
        "{:<path_width$}  {:<lang_width$}  {:>7}  {:>7}  {:>7}",
        "File", "Language", "blank", "comment", "code",
    )?;
    for row in &rows {
        writeln!(
            out,
            "{:<path_width$}  {:<lang_width$}  {:>7}  {:>7}  {:>7}",
            row[0], row[1], row[2], row[3], row[4],
        )?;
    }
    Ok(())
}

/// The JSON document for a scan: per-language totals, the grand total, and
/// with `by_file` the per-file rows.
#[must_use]
pub fn json_counts(reports: &[FileReport], cwd: &Path, by_file: bool) -> Value {
    let languages: Vec<Value> = by_language(reports)
        .into_iter()
        .map(|(language, total)| {
            json!({
                "language": language.name(),
                "files": total.files,
                "blank": total.counts.blank,
                "comment": total.counts.comment,
                "code": total.counts.code,
            })
        })
        .collect();
    let total = grand_total(reports);
    let mut document = json!({
        "languages": languages,
        "total": {
            "files": total.files,
            "blank": total.counts.blank,
            "comment": total.counts.comment,
            "code": total.counts.code,
        },
    });
    if by_file {
        let files: Vec<Value> = reports
            .iter()
            .map(|report| {
                json!({
                    "path": display_path(&report.path, cwd).display().to_string(),
                    "language": report.language.name(),
                    "blank": report.counts.blank,
                    "comment": report.counts.comment,
                    "code": report.counts.code,
                })
            })
            .collect();
        document["files"] = Value::Array(files);
    }
    document
}

/// Writes the functions, worst first. With coverage the table shows the CRAP
/// score and flags each function above `threshold`. Without coverage it shows
/// complexity only.
///
/// # Errors
///
/// Returns any error from writing to `out`.
pub fn write_functions(
    out: &mut impl Write,
    ranking: &Ranking,
    cwd: &Path,
    threshold: f64,
    count_unlisted: bool,
) -> io::Result<()> {
    let scored = &ranking.functions;
    if scored.is_empty() {
        return writeln!(out, "no functions found");
    }
    let has_coverage = scored[0].crap.is_some();
    let header: &[&str] = if has_coverage {
        &["CRAP", "complexity", "coverage", "function", "location"]
    } else {
        &["complexity", "function", "location"]
    };
    let rows: Vec<Vec<String>> = scored
        .iter()
        .map(|s| function_cells(s, cwd, has_coverage, threshold))
        .collect();

    let widths: Vec<usize> = (0..header.len())
        .map(|column| {
            rows.iter()
                .map(|row| row[column].len())
                .chain(std::iter::once(header[column].len()))
                .max()
                .unwrap_or(0)
        })
        .collect();
    // The function name is left-aligned, and so is the location, which ends
    // the row. Every other column is right-aligned.
    let name_column = if has_coverage { 3 } else { 1 };
    let last = header.len() - 1;
    let line = |cells: &[&str]| -> String {
        let padded: Vec<String> = cells
            .iter()
            .enumerate()
            .map(|(column, cell)| {
                let width = widths[column];
                if column == last || column == name_column {
                    format!("{cell:<width$}")
                } else {
                    format!("{cell:>width$}")
                }
            })
            .collect();
        padded.join("  ").trim_end().to_string()
    };
    writeln!(out, "{}", line(header))?;
    for row in &rows {
        let cells: Vec<&str> = row.iter().map(String::as_str).collect();
        writeln!(out, "{}", line(&cells))?;
    }
    write_function_notes(out, ranking, threshold, count_unlisted)
}

/// The cells of one row of the functions table.
fn function_cells(s: &Scored, cwd: &Path, has_coverage: bool, threshold: f64) -> Vec<String> {
    let location = format!(
        "{}:{}",
        display_path(&s.path, cwd).display(),
        s.function.start_line
    );
    let complexity = s.function.complexity.to_string();
    if !has_coverage {
        return vec![complexity, s.function.name.clone(), location];
    }
    let over = if s.crap.is_some_and(|crap| crap > threshold) {
        " OVER"
    } else {
        ""
    };
    vec![
        s.crap.map_or("-".to_string(), |crap| format!("{crap:.1}")),
        complexity,
        s.coverage
            .map_or("-".to_string(), |ratio| format!("{:.0}%", ratio * 100.0)),
        s.function.name.clone(),
        format!("{location}{over}"),
    ]
}

/// The lines under the functions table: the gate's count, and what was left
/// out or counted as untested.
fn write_function_notes(
    out: &mut impl Write,
    ranking: &Ranking,
    threshold: f64,
    count_unlisted: bool,
) -> io::Result<()> {
    let scored = &ranking.functions;
    if scored[0].crap.is_none() {
        return writeln!(
            out,
            "\nno coverage data, so CRAP is not computed: complexity only (pass --lcov)"
        );
    }
    let over = crate::crap::over_threshold(scored, threshold);
    writeln!(
        out,
        "\n{over} of {} functions above the CRAP threshold of {threshold}",
        scored.len()
    )?;
    if ranking.left_out > 0 {
        writeln!(
            out,
            "{} functions in files the coverage report does not list were left out; --count-unlisted scores them as untested",
            ranking.left_out
        )?;
    }
    let unlisted = scored.iter().filter(|s| s.missing_from_report).count();
    if count_unlisted && unlisted > 0 {
        writeln!(
            out,
            "{unlisted} functions in files the coverage report does not list count as 0% covered"
        )?;
    }
    Ok(())
}

/// The CRAP section of the JSON document.
#[must_use]
pub fn json_functions(ranking: &Ranking, cwd: &Path, threshold: f64) -> Value {
    let scored = &ranking.functions;
    let functions: Vec<Value> = scored
        .iter()
        .map(|s| {
            json!({
                "path": display_path(&s.path, cwd).display().to_string(),
                "name": s.function.name,
                "line": s.function.start_line,
                "end_line": s.function.end_line,
                "complexity": s.function.complexity,
                "coverage": s.coverage,
                "crap": s.crap,
                "missing_from_report": s.missing_from_report,
            })
        })
        .collect();
    json!({
        "threshold": threshold,
        "over_threshold": crate::crap::over_threshold(scored, threshold),
        "left_out": ranking.left_out,
        "functions": functions,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn report(language: Language, blank: u64, comment: u64, code: u64) -> FileReport {
        FileReport {
            path: PathBuf::from(format!("/r/{}-{code}.x", language.name())),
            language,
            counts: LineCounts {
                blank,
                comment,
                code,
            },
            functions: Vec::new(),
        }
    }

    #[test]
    fn totals_add_up_across_languages() {
        let reports = [
            report(Language::Rust, 1, 2, 10),
            report(Language::Rust, 0, 0, 5),
            report(Language::Python, 3, 1, 7),
        ];
        let total = grand_total(&reports);
        assert_eq!(total.files, 3);
        assert_eq!(
            total.counts,
            LineCounts {
                blank: 4,
                comment: 3,
                code: 22,
            }
        );
        let rust = by_language(&reports)[&Language::Rust];
        assert_eq!(rust.files, 2);
        assert_eq!(rust.counts.code, 15);
    }

    #[test]
    fn table_lists_largest_code_count_first_and_ends_with_sum() {
        let reports = [
            report(Language::Python, 0, 0, 7),
            report(Language::Rust, 0, 0, 10),
        ];
        let mut out = Vec::new();
        write_table(&mut out, &reports).unwrap();
        let text = String::from_utf8(out).unwrap();
        let rows: Vec<&str> = text.lines().collect();
        assert!(rows[2].starts_with("Rust"));
        assert!(rows[3].starts_with("Python"));
        assert!(rows.last().unwrap().starts_with("SUM:"));
        assert!(rows.last().unwrap().ends_with("17"));
    }

    #[test]
    fn json_has_totals_and_optional_files() {
        let reports = [report(Language::Toml, 1, 0, 4)];
        let cwd = Path::new("/r");
        let brief = json_counts(&reports, cwd, false);
        assert_eq!(brief["total"]["code"], 4);
        assert!(brief.get("files").is_none());
        let full = json_counts(&reports, cwd, true);
        assert_eq!(full["files"][0]["path"], "TOML-4.x");
        assert_eq!(full["files"][0]["language"], "TOML");
    }
}
