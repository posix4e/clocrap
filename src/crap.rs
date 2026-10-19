//! The CRAP score of each function (Change Risk Anti-Patterns):
//!
//! ```text
//! CRAP(m) = comp(m)^2 * (1 - cov(m))^3 + comp(m)
//! ```
//!
//! `comp` is the function's cyclomatic complexity and `cov` is the share of its
//! lines that the tests ran, from 0 to 1. A function with complexity 1 and full
//! coverage scores 1; a complex function with no tests scores comp² + comp.

use std::path::PathBuf;

use crate::complexity::Function;
use crate::lcov::Coverage;
use crate::walk::FileReport;

/// The usual CRAP limit. A function above it is a risk.
pub const DEFAULT_THRESHOLD: f64 = 30.0;

/// The CRAP score for a function of the given complexity and coverage. The
/// coverage is clamped to 0 through 1.
#[must_use]
pub fn score(complexity: u32, coverage: f64) -> f64 {
    let comp = f64::from(complexity);
    let uncovered = 1.0 - coverage.clamp(0.0, 1.0);
    comp * comp * uncovered.powi(3) + comp
}

/// One function with its measures.
#[derive(Debug, Clone, PartialEq)]
pub struct Scored {
    pub path: PathBuf,
    pub function: Function,
    /// Share of the function's instrumented lines that ran. `None` when no
    /// coverage data was given.
    pub coverage: Option<f64>,
    /// The CRAP score. `None` when no coverage data was given, because the
    /// score needs coverage.
    pub crap: Option<f64>,
    /// Whether the coverage data has a record for the file. When it does not,
    /// `coverage` is 0: the file is counted as untested.
    pub missing_from_report: bool,
}

/// The functions of a scan, worst first, and how many were left out.
#[derive(Debug, Clone, PartialEq)]
pub struct Ranking {
    pub functions: Vec<Scored>,
    /// Functions in files the coverage report does not list, left out because
    /// the caller did not ask to count them.
    pub left_out: usize,
}

/// Every function in `reports`, worst first. With coverage the order is by
/// CRAP score; without it, by complexity, and the scores are `None`.
///
/// A file the coverage report does not list is usually one it leaves out on
/// purpose, such as test code. Its functions are left out unless
/// `count_unlisted` is set, in which case they count as 0% covered.
#[must_use]
pub fn rank(reports: &[FileReport], coverage: Option<&Coverage>, count_unlisted: bool) -> Ranking {
    let mut scored = Vec::new();
    let mut left_out = 0;
    for report in reports {
        for function in &report.functions {
            let (cov, missing_from_report) = match coverage {
                None => (None, false),
                Some(data) => {
                    match data.ratio(&report.path, function.start_line, function.end_line) {
                        Some(ratio) => (Some(ratio), false),
                        None if count_unlisted => (Some(0.0), true),
                        None => {
                            left_out += 1;
                            continue;
                        }
                    }
                }
            };
            scored.push(Scored {
                path: report.path.clone(),
                function: function.clone(),
                coverage: cov,
                crap: cov.map(|ratio| score(function.complexity, ratio)),
                missing_from_report,
            });
        }
    }
    scored.sort_by(|a, b| {
        let by_risk = match (a.crap, b.crap) {
            (Some(x), Some(y)) => y.total_cmp(&x),
            _ => b.function.complexity.cmp(&a.function.complexity),
        };
        by_risk
            .then_with(|| a.path.cmp(&b.path))
            .then_with(|| a.function.start_line.cmp(&b.function.start_line))
    });
    Ranking {
        functions: scored,
        left_out,
    }
}

/// How many functions score above `threshold`.
#[must_use]
pub fn over_threshold(scored: &[Scored], threshold: f64) -> usize {
    scored
        .iter()
        .filter(|s| s.crap.is_some_and(|crap| crap > threshold))
        .count()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Hand-computed: each row is comp, cov, and the CRAP value worked out
    /// from the formula by hand.
    #[test]
    fn score_matches_hand_computed_values() {
        // Full coverage: the square term vanishes, leaving complexity.
        assert_eq!(score(1, 1.0), 1.0);
        assert_eq!(score(7, 1.0), 7.0);
        // No coverage: comp^2 + comp.
        assert_eq!(score(1, 0.0), 2.0);
        assert_eq!(score(10, 0.0), 110.0);
        // Half covered: comp^2 * 0.125 + comp.
        assert_eq!(score(10, 0.5), 22.5);
        assert_eq!(score(4, 0.5), 4.0 * 4.0 * 0.125 + 4.0);
        // 80% covered: 0.2^3 = 0.008. 5^2 * 0.008 + 5 = 5.2.
        assert!((score(5, 0.8) - 5.2).abs() < 1e-12);
        // 90% covered on comp 6: 36 * 0.001 + 6 = 6.036.
        assert!((score(6, 0.9) - 6.036).abs() < 1e-12);
    }

    #[test]
    fn coverage_outside_zero_to_one_is_clamped() {
        assert_eq!(score(3, 1.5), score(3, 1.0));
        assert_eq!(score(3, -0.5), score(3, 0.0));
    }

    #[test]
    fn the_threshold_gate_is_strictly_above() {
        // comp 5 with no tests scores 30 exactly: not above a threshold of 30.
        assert_eq!(score(5, 0.0), 30.0);
        let scored = vec![row(5, Some(0.0))];
        assert_eq!(over_threshold(&scored, DEFAULT_THRESHOLD), 0);
        assert_eq!(over_threshold(&[row(6, Some(0.0))], DEFAULT_THRESHOLD), 1);
    }

    #[test]
    fn rank_orders_worst_first_and_skips_crap_without_coverage() {
        let report = FileReport {
            path: PathBuf::from("/r/a.rs"),
            language: crate::lang::Language::Rust,
            counts: crate::count::LineCounts::default(),
            functions: vec![
                Function {
                    name: "tested".into(),
                    start_line: 1,
                    end_line: 3,
                    complexity: 9,
                },
                Function {
                    name: "untested".into(),
                    start_line: 5,
                    end_line: 9,
                    complexity: 3,
                },
            ],
        };
        let mut coverage =
            Coverage::parse("SF:/r/a.rs\nDA:1,1\nDA:2,1\nDA:3,1\nDA:5,0\nDA:6,0\nend_of_record\n");
        let reports = [report];

        let scored = rank(&reports, Some(&coverage), false).functions;
        assert_eq!(scored[0].function.name, "untested");
        assert_eq!(scored[0].crap, Some(score(3, 0.0)));
        assert_eq!(scored[1].function.name, "tested");
        assert_eq!(scored[1].coverage, Some(1.0));
        assert_eq!(scored[1].crap, Some(9.0));

        let by_complexity = rank(&reports, None, false).functions;
        assert_eq!(by_complexity[0].function.name, "tested");
        assert!(
            by_complexity
                .iter()
                .all(|s| s.crap.is_none() && s.coverage.is_none())
        );

        // A file the report does not mention is left out by default...
        coverage = Coverage::parse("SF:/r/other.rs\nDA:1,1\nend_of_record\n");
        let left_out = rank(&reports, Some(&coverage), false);
        assert_eq!(left_out.functions, Vec::new());
        assert_eq!(left_out.left_out, 2);
        // ...and counts as untested when asked.
        let unknown = rank(&reports, Some(&coverage), true).functions;
        assert!(
            unknown
                .iter()
                .all(|s| s.missing_from_report && s.coverage == Some(0.0))
        );
    }

    fn row(complexity: u32, coverage: Option<f64>) -> Scored {
        Scored {
            path: PathBuf::from("x.rs"),
            function: Function {
                name: "f".into(),
                start_line: 1,
                end_line: 2,
                complexity,
            },
            coverage,
            crap: coverage.map(|c| score(complexity, c)),
            missing_from_report: false,
        }
    }
}
