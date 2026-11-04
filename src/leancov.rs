//! Coverage for Lean, read from the C that Lean compiles to.
//!
//! Lake writes one C file per module, `.lake/build/ir/<Module>.c`, and Lean's
//! C has no line directives back to the `.lean` source. Built with LLVM source
//! coverage (see the README), an lcov report covers those C files instead. Each
//! C function carries its declaration's mangled name, so the C functions are
//! matched to the declarations clocrap found:
//!
//! - `lp_<package>_<name>` or `l_<name>` is the declaration `<name>` itself;
//!   `<name>___lam__0`, `<name>___redArg`, `<name>_spec__0` and the like are
//!   parts of it, so they belong to it too. Of several declarations whose name
//!   fits, the longest wins, so `total_go` belongs to `total.go`, not `total`.
//! - `<callee>___at___00<name>_spec__0` is a copy of a callee specialised for
//!   `<name>`, run on `<name>`'s behalf: it belongs to `<name>`.
//! - A private declaration's name starts `__private_<Module>_0__`, and so do
//!   the compiler's private helpers for a public one. `main` is `_lean_main`.
//! - `___boxed` wrappers, `match` splitters and module initialisers are left
//!   out: wrappers and initialisers are glue, boxing wrappers rarely run, and a
//!   splitter is compiled for proofs (the `split` tactic) and never called, so
//!   each would read as untested code.
//!
//! A declaration's coverage is the share of the instrumented C lines of the
//! functions it owns that ran. A declaration that owns none has no compiled
//! code of its own (it was inlined, is a type, or runs only at compile time),
//! and has no coverage.

use std::path::Path;

use crate::complexity::Function;
use crate::lcov::Coverage;
use crate::lean::mangle;

const IR: &str = "/.lake/build/ir/";

/// Coverage for each of `functions`, the functions of the Lean file at
/// `lean_file`, in the same order: `None` for one with no compiled code. The
/// result is `None` when the report has no C file for this module.
#[must_use]
pub fn file_coverage(
    coverage: &Coverage,
    lean_file: &Path,
    functions: &[Function],
) -> Option<Vec<Option<f64>>> {
    let lean_file = std::fs::canonicalize(lean_file).unwrap_or_else(|_| lean_file.to_path_buf());
    let (c_file, module) = c_file_for(coverage, &lean_file)?;
    let c_functions = coverage.functions_of(&c_file)?;
    let module = module.split('/').map(mangle).collect::<Vec<_>>().join("_");

    let initializer = c_functions
        .values()
        .map(|name| local_name(name))
        .find_map(|name| {
            name.strip_prefix("initialize_")?
                .strip_suffix(&module)?
                .strip_suffix('_')
        });
    let mut prefixes = vec!["l_".to_string()];
    if let Some(package) = initializer {
        prefixes.insert(0, format!("lp_{package}_"));
    }

    let keys: Vec<(usize, String)> = functions
        .iter()
        .enumerate()
        .filter_map(|(index, f)| {
            let symbol = f.symbol.as_ref()?;
            let name = mangle(&symbol.name);
            Some((
                index,
                if symbol.private {
                    format!("__private_{module}_0__{name}")
                } else {
                    name
                },
            ))
        })
        .collect();

    let starts: Vec<(u64, &str)> = c_functions
        .iter()
        .map(|(&line, name)| (line, local_name(name)))
        .collect();
    let mut tallies: Vec<Option<(u32, u32)>> = vec![None; functions.len()];
    for (n, &(start, name)) in starts.iter().enumerate() {
        let end = starts.get(n + 1).map_or(u64::MAX, |&(next, _)| next - 1);
        let Some(owner) = owner(name, &prefixes, &keys) else {
            continue;
        };
        let (total, covered) = coverage.hits(&c_file, start, end);
        let tally = tallies[owner].get_or_insert((0, 0));
        tally.0 = tally.0.saturating_add(total);
        tally.1 = tally.1.saturating_add(covered);
    }
    Some(
        tallies
            .into_iter()
            .map(|tally| {
                tally.map(|(total, covered)| {
                    if total == 0 {
                        0.0
                    } else {
                        f64::from(covered) / f64::from(total)
                    }
                })
            })
            .collect(),
    )
}

/// The report's C file for this Lean file, and the module's path (`A/B` for
/// `A.B`). The C file is `<root>/.lake/build/ir/<module>.c` where the Lean
/// file is under `<root>` and ends in `<module>.lean`; the longest module wins.
fn c_file_for(coverage: &Coverage, lean_file: &Path) -> Option<(std::path::PathBuf, String)> {
    let lean = lean_file.to_str()?;
    let mut best: Option<(std::path::PathBuf, String)> = None;
    for path in coverage.files() {
        let Some(text) = path.to_str() else { continue };
        let Some((root, rest)) = text.split_once(IR) else {
            continue;
        };
        let Some(module) = rest.strip_suffix(".c") else {
            continue;
        };
        let fits = lean.starts_with(root)
            && lean
                .strip_suffix(".lean")
                .and_then(|stem| stem.strip_suffix(module))
                .is_some_and(|before| before.ends_with('/'));
        if fits && best.as_ref().is_none_or(|(_, m)| module.len() > m.len()) {
            best = Some((path.to_path_buf(), module.to_string()));
        }
    }
    best
}

/// llvm-cov writes a static function as `File.c:name`.
fn local_name(name: &str) -> &str {
    name.rsplit_once(':').map_or(name, |(_, local)| local)
}

/// The declaration that owns the C function `name`, as an index into the
/// file's functions.
fn owner(name: &str, prefixes: &[String], keys: &[(usize, String)]) -> Option<usize> {
    if name.ends_with("___boxed")
        || is_splitter(name)
        || name.starts_with("initialize_")
        || name.starts_with("_init_")
    {
        return None;
    }
    let stripped = if name == "_lean_main" {
        "main"
    } else {
        prefixes
            .iter()
            .find_map(|p| name.strip_prefix(p.as_str()))?
    };
    let mut candidates: Vec<&str> = match stripped.rfind("___at___") {
        Some(at) => {
            let target = &stripped[at + "___at___".len()..];
            vec![target.strip_prefix("00").unwrap_or(target), &stripped[..at]]
        }
        None => vec![stripped],
    };
    // The compiler's private helpers for a public declaration, such as a
    // `match` splitter, carry the module's private prefix.
    let public: Vec<&str> = candidates
        .iter()
        .filter_map(|c| {
            c.strip_prefix("__private_")?
                .split_once("_0__")
                .map(|(_, rest)| rest)
        })
        .collect();
    candidates.extend(public);
    candidates.into_iter().find_map(|candidate| {
        keys.iter()
            .filter(|(_, key)| part_of(candidate, key))
            .max_by_key(|(_, key)| key.len())
            .map(|&(index, _)| index)
    })
}

/// Whether a C name is a `match` splitter or one of its parts: a component
/// `match_<n>.splitter`, mangled `_match__<n>_splitter`.
fn is_splitter(name: &str) -> bool {
    name.match_indices("_match__").any(|(at, m)| {
        let rest = &name[at + m.len()..];
        let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
        digits > 0 && rest[digits..].starts_with("_splitter")
    })
}

/// Whether the C name `candidate` is the declaration `key` or one of its
/// parts. A part adds a component: `_` and a name (`_go`, `_spec__0`), or a
/// component that itself starts with `_` (`___lam__0`). `key` followed by
/// `__x` is another declaration whose last component goes on with an
/// underscore, as `Foo.bar_x` is `Foo_bar__x`.
fn part_of(candidate: &str, key: &str) -> bool {
    let Some(rest) = candidate.strip_prefix(key) else {
        return false;
    };
    rest.is_empty()
        || rest.starts_with("___")
        || (rest.starts_with('_') && !rest[1..].starts_with('_'))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::complexity::Symbol;

    fn function(name: &str, private: bool) -> Function {
        Function {
            name: name.to_string(),
            start_line: 1,
            end_line: 1,
            complexity: 1,
            symbol: Some(Symbol {
                name: name.to_string(),
                private,
            }),
        }
    }

    /// C function names as Lean 4.35 emits them for `Cov/Basic.lean` in a
    /// package named `covtest`, with made-up line hits.
    const REPORT: &str = "\
SF:/no/such/pkg/.lake/build/ir/Cov/Basic.c
FN:10,lp_covtest_Cov_classify
FN:20,lp_covtest_Cov_classify___boxed
FN:30,lp_covtest_Cov_unused
FN:40,lp_covtest_List_foldl___at___00__private_Cov_Basic_0__Cov_helper_spec__0
FN:50,lp_covtest___private_Cov_Basic_0__Cov_helper
FN:60,lp_covtest_Cov_total_go
FN:70,lp_covtest_Cov_total
FN:80,lp_covtest_Cov_total___lam__0
FN:90,lp_covtest_Cov_total__extra
FN:95,lp_covtest___private_Cov_Basic_0__Cov_classify_match__1
FN:98,lp_covtest___private_Cov_Basic_0__Cov_classify_match__1_splitter
FN:99,lp_covtest___private_Cov_Basic_0__Cov_classify_match__1_splitter___redArg
FN:100,initialize_covtest_Cov_Basic
DA:10,1
DA:11,0
DA:20,0
DA:30,0
DA:40,3
DA:50,3
DA:51,0
DA:60,1
DA:70,1
DA:80,0
DA:90,0
DA:95,1
DA:96,1
DA:98,0
DA:99,0
DA:100,1
end_of_record
";

    #[test]
    fn c_functions_are_matched_to_their_declarations() {
        let coverage = Coverage::parse(REPORT);
        let functions = [
            function("Cov.classify", false),
            function("Cov.unused", false),
            function("Cov.helper", true),
            function("Cov.total", false),
            function("Cov.total.go", false),
            function("Cov.inlined", false),
        ];
        let found = file_coverage(
            &coverage,
            Path::new("/no/such/pkg/Cov/Basic.lean"),
            &functions,
        )
        .unwrap();
        assert_eq!(
            found,
            [
                // 10 ran, 11 did not; the boxed wrapper at 20 is left out; its
                // private matcher's two lines at 95 ran, and its splitter at 98,
                // which only proofs use, is left out.
                Some(0.75),
                Some(0.0),
                // its own lines 50 and 51, and the foldl specialised for it at 40.
                Some(2.0 / 3.0),
                // 70 and its lambda at 80; not `total_go`, and not `total__extra`,
                // which is another declaration (`Cov.total_extra`).
                Some(0.5),
                Some(1.0),
                None,
            ]
        );
    }

    #[test]
    fn a_module_with_no_c_file_in_the_report_is_none() {
        let coverage = Coverage::parse(REPORT);
        assert_eq!(
            file_coverage(
                &coverage,
                Path::new("/no/such/pkg/Cov/Other.lean"),
                &[function("Cov.classify", false)],
            ),
            None
        );
        // The module path must match whole components.
        assert_eq!(
            file_coverage(
                &coverage,
                Path::new("/no/such/pkg/XCov/Basic.lean"),
                &[function("Cov.classify", false)],
            ),
            None
        );
    }

    #[test]
    fn main_and_static_functions() {
        let coverage = Coverage::parse(
            "SF:/p/.lake/build/ir/Main.c\nFN:1,_lean_main\nFN:5,Main.c:lp_x_main___lam__0\nFN:9,initialize_x_Main\nDA:1,1\nDA:5,0\nend_of_record\n",
        );
        let found = file_coverage(
            &coverage,
            Path::new("/p/Main.lean"),
            &[function("main", false)],
        )
        .unwrap();
        assert_eq!(found, [Some(0.5)]);
    }
}
