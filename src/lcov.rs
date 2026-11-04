//! Line coverage from lcov files: the format `cargo llvm-cov --lcov` and most
//! other coverage tools write. The `SF:`, `DA:` and `FN:` records are read:
//! `FN:` names each function's first line, which Lean's coverage needs (see
//! `leancov`).

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};

/// Hit counts per line, for every source file in one or more lcov reports.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Coverage {
    /// Keyed by the file's path as the report gives it, canonicalised when the
    /// file exists. Each value maps a 1-based line to its hit count.
    files: HashMap<PathBuf, BTreeMap<u64, u64>>,
    /// Each file's functions: first line to name.
    functions: HashMap<PathBuf, BTreeMap<u64, String>>,
}

impl Coverage {
    /// Reads and merges several lcov files. Hit counts for the same line add up.
    ///
    /// # Errors
    ///
    /// Returns an error if a file cannot be read.
    pub fn read(paths: &[PathBuf]) -> Result<Coverage, String> {
        let mut coverage = Coverage::default();
        for path in paths {
            let text = std::fs::read_to_string(path)
                .map_err(|err| format!("cannot read lcov file {}: {err}", path.display()))?;
            coverage.merge(&Coverage::parse(&text));
        }
        Ok(coverage)
    }

    /// Parses the text of one lcov report.
    #[must_use]
    pub fn parse(text: &str) -> Coverage {
        let mut coverage = Coverage::default();
        let mut current: Option<PathBuf> = None;
        for line in text.lines() {
            if let Some(path) = line.strip_prefix("SF:") {
                current = Some(canonical_or_same(Path::new(path)));
            } else if let Some(record) = line.strip_prefix("DA:") {
                if let (Some(file), Some((number, hits))) = (&current, parse_da(record)) {
                    let lines = coverage.files.entry(file.clone()).or_default();
                    let total = lines.entry(number).or_insert(0);
                    *total = total.saturating_add(hits);
                }
            } else if let Some(record) = line.strip_prefix("FN:") {
                if let (Some(file), Some((number, name))) = (&current, parse_fn(record)) {
                    coverage
                        .functions
                        .entry(file.clone())
                        .or_default()
                        .insert(number, name.to_string());
                }
            } else if line == "end_of_record" {
                current = None;
            }
        }
        coverage
    }

    /// Adds another report's hit counts to this one.
    pub fn merge(&mut self, other: &Coverage) {
        for (path, lines) in &other.files {
            let mine = self.files.entry(path.clone()).or_default();
            for (&number, &hits) in lines {
                let total = mine.entry(number).or_insert(0);
                *total = total.saturating_add(hits);
            }
        }
        for (path, functions) in &other.functions {
            let mine = self.functions.entry(path.clone()).or_default();
            for (&number, name) in functions {
                mine.entry(number).or_insert_with(|| name.clone());
            }
        }
    }

    /// Every file the report has line records for.
    pub fn files(&self) -> impl Iterator<Item = &Path> {
        self.files.keys().map(PathBuf::as_path)
    }

    /// The functions the report names in `path`, by first line.
    #[must_use]
    pub fn functions_of(&self, path: &Path) -> Option<&BTreeMap<u64, String>> {
        self.functions.get(path)
    }

    /// The instrumented lines in `start..=end`, and how many of them ran.
    #[must_use]
    pub fn hits(&self, path: &Path, start: u64, end: u64) -> (u32, u32) {
        let (mut total, mut covered) = (0_u32, 0_u32);
        if let Some(lines) = self.lines_of(path) {
            for (_, &hits) in lines.range(start..=end) {
                total = total.saturating_add(1);
                if hits > 0 {
                    covered = covered.saturating_add(1);
                }
            }
        }
        (total, covered)
    }

    /// Whether the report has any record for `path`.
    #[must_use]
    pub fn has_file(&self, path: &Path) -> bool {
        self.lines_of(path).is_some()
    }

    /// The fraction of instrumented lines in `start..=end` that ran, between 0
    /// and 1. A range with no instrumented lines counts as 0, since nothing
    /// shows that it ran. Returns `None` if the report has no record for the
    /// file at all.
    #[must_use]
    pub fn ratio(&self, path: &Path, start: u64, end: u64) -> Option<f64> {
        self.lines_of(path)?;
        let (total, covered) = self.hits(path, start, end);
        if total == 0 {
            return Some(0.0);
        }
        Some(f64::from(covered) / f64::from(total))
    }

    fn lines_of(&self, path: &Path) -> Option<&BTreeMap<u64, u64>> {
        self.files
            .get(path)
            .or_else(|| self.files.get(&canonical_or_same(path)))
    }
}

/// `DA:<line>,<hits>[,<checksum>]`.
fn parse_da(record: &str) -> Option<(u64, u64)> {
    let mut fields = record.split(',');
    let number = fields.next()?.trim().parse().ok()?;
    let hits = fields.next()?.trim().parse().ok()?;
    Some((number, hits))
}

/// `FN:<line>,<name>`, or `FN:<line>,<end line>,<name>` as newer lcov writes.
fn parse_fn(record: &str) -> Option<(u64, &str)> {
    let (number, rest) = record.split_once(',')?;
    let number = number.trim().parse().ok()?;
    let name = match rest.split_once(',') {
        Some((end, name)) if end.trim().parse::<u64>().is_ok() => name,
        _ => rest,
    };
    Some((number, name.trim()))
}

fn canonical_or_same(path: &Path) -> PathBuf {
    std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

#[cfg(test)]
mod tests {
    use super::*;

    const REPORT: &str = "\
TN:
SF:/no/such/clocrap/src/lib.rs
FN:1,f
FNDA:1,f
DA:1,1
DA:2,0
DA:3,4
DA:4,0,abc123
LF:4
LH:2
end_of_record
SF:/no/such/clocrap/src/other.rs
DA:1,0
end_of_record
";

    #[test]
    fn ratio_is_the_share_of_instrumented_lines_that_ran() {
        let coverage = Coverage::parse(REPORT);
        let path = Path::new("/no/such/clocrap/src/lib.rs");
        assert_eq!(coverage.ratio(path, 1, 4), Some(0.5));
        assert_eq!(coverage.ratio(path, 1, 1), Some(1.0));
        assert_eq!(coverage.ratio(path, 2, 2), Some(0.0));
    }

    #[test]
    fn range_with_no_instrumented_lines_is_zero_not_missing() {
        let coverage = Coverage::parse(REPORT);
        let path = Path::new("/no/such/clocrap/src/lib.rs");
        assert_eq!(coverage.ratio(path, 100, 200), Some(0.0));
    }

    #[test]
    fn file_absent_from_the_report_is_none() {
        let coverage = Coverage::parse(REPORT);
        assert_eq!(
            coverage.ratio(Path::new("/no/such/clocrap/x.rs"), 1, 9),
            None
        );
        assert!(!coverage.has_file(Path::new("/no/such/clocrap/x.rs")));
        assert!(coverage.has_file(Path::new("/no/such/clocrap/src/other.rs")));
    }

    #[test]
    fn merging_adds_hit_counts_line_by_line() {
        let mut first = Coverage::parse("SF:/x/a.rs\nDA:1,1\nDA:2,0\nend_of_record\n");
        let second = Coverage::parse("SF:/x/a.rs\nDA:1,0\nDA:2,3\nend_of_record\n");
        first.merge(&second);
        assert_eq!(first.ratio(Path::new("/x/a.rs"), 1, 2), Some(1.0));
        let only_first = Coverage::parse("SF:/x/b.rs\nDA:1,0\nend_of_record\n");
        first.merge(&only_first);
        assert_eq!(first.ratio(Path::new("/x/b.rs"), 1, 1), Some(0.0));
    }

    #[test]
    fn function_records_name_first_lines() {
        let coverage =
            Coverage::parse("SF:/x/a.c\nFN:3,f\nFN:9,12,g\nFN:20,a.c:h\nDA:3,1\nend_of_record\n");
        let functions = coverage.functions_of(Path::new("/x/a.c")).unwrap();
        let named: Vec<(u64, &str)> = functions.iter().map(|(&n, s)| (n, s.as_str())).collect();
        assert_eq!(named, [(3, "f"), (9, "g"), (20, "a.c:h")]);
    }

    #[test]
    fn records_outside_a_file_are_ignored() {
        let coverage = Coverage::parse("DA:1,5\nend_of_record\n");
        assert_eq!(coverage, Coverage::default());
    }
}
