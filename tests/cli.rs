//! End-to-end tests of the `clocrap` binary, on small fixture trees.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const LIB_RS: &str = "\
//! Crate docs.

/// A function.
pub fn f(x: u32) -> u32 {
    // comment
    if x > 1 {
        return 1;
    }
    if x > 2 {
        return 2;
    }
    0
}
";

/// A fresh directory for one test.
fn fixture(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("clocrap-cli-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn write(path: &Path, contents: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, contents).unwrap();
}

fn clocrap(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_clocrap"))
        .current_dir(dir)
        .args(args)
        .output()
        .unwrap()
}

fn stdout_json(output: &Output) -> serde_json::Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|err| {
        panic!(
            "not JSON ({err}): {}\nstderr: {}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

/// The number `wc -l` reports for a file.
fn wc_lines(path: &Path) -> u64 {
    let output = Command::new("wc")
        .arg("-l")
        .stdin(fs::File::open(path).unwrap())
        .output()
        .unwrap();
    String::from_utf8_lossy(&output.stdout)
        .trim()
        .parse()
        .unwrap()
}

#[test]
fn total_lines_agree_with_wc_for_newline_terminated_files() {
    let dir = fixture("wc");
    write(&dir.join("src/lib.rs"), LIB_RS);
    write(&dir.join("README.md"), "# Title\n\nSome prose.\n");
    write(
        &dir.join("tool/run.py"),
        "\"\"\"Doc.\n\nmore\n\"\"\"\n# note\nprint(1)\n",
    );
    write(&dir.join("Cargo.toml"), "[package]\n# c\nname = \"x\"\n");
    write(&dir.join("web/app.ts"), "// top\nconst a = 1; /* c */\n\n");

    let files = [
        "src/lib.rs",
        "README.md",
        "tool/run.py",
        "Cargo.toml",
        "web/app.ts",
    ];
    let expected: u64 = files.iter().map(|f| wc_lines(&dir.join(f))).sum();

    let output = clocrap(&dir, &["--json", "--by-file"]);
    assert!(output.status.success(), "{output:?}");
    let json = stdout_json(&output);
    let total = &json["total"];
    let counted = total["blank"].as_u64().unwrap()
        + total["comment"].as_u64().unwrap()
        + total["code"].as_u64().unwrap();
    assert_eq!(counted, expected);
    assert_eq!(total["files"], 5);
    assert_eq!(json["files"].as_array().unwrap().len(), 5);
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn per_language_totals_and_table() {
    let dir = fixture("table");
    write(&dir.join("src/lib.rs"), LIB_RS);
    let output = clocrap(&dir, &["--json"]);
    let json = stdout_json(&output);
    let rust = &json["languages"][0];
    assert_eq!(rust["language"], "Rust");
    assert_eq!(rust["files"], 1);
    assert_eq!(rust["blank"], 1);
    assert_eq!(rust["comment"], 3);
    assert_eq!(rust["code"], 9);

    let table = clocrap(&dir, &[]);
    let text = String::from_utf8(table.stdout).unwrap();
    assert!(text.lines().any(|line| line.starts_with("Rust")), "{text}");
    assert!(text.contains("SUM:"), "{text}");
    fs::remove_dir_all(&dir).unwrap();
}

fn language<'a>(json: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    json["languages"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["language"] == name)
        .unwrap_or_else(|| panic!("no {name} row in {json}"))
}

#[test]
fn files_without_an_extension_are_counted_by_their_shebang() {
    let dir = fixture("shebang");
    write(
        &dir.join("bin/tool"),
        "#!/usr/bin/env python3\n# a comment\nprint(1)\n",
    );
    write(&dir.join("bin/run"), "#!/bin/sh\necho hi\n");
    write(&dir.join("bin/data"), "plain text\n");
    write(&dir.join("LICENSE"), "MIT\n");
    let json = stdout_json(&clocrap(&dir, &["--json"]));
    assert_eq!(json["total"]["files"], 2);
    let python = language(&json, "Python");
    assert_eq!(
        (
            python["files"].as_u64(),
            python["comment"].as_u64(),
            python["code"].as_u64()
        ),
        (Some(1), Some(2), Some(1))
    );
    let shell = language(&json, "Shell");
    assert_eq!(
        (shell["comment"].as_u64(), shell["code"].as_u64()),
        (Some(1), Some(1))
    );
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn c_html_css_and_json_lines_are_counted() {
    let dir = fixture("more-languages");
    write(
        &dir.join("probe.c"),
        "/* block\n comment */\nint main(void) { return '/'; } // tail\n",
    );
    write(
        &dir.join("page.html"),
        "<!-- note -->\n<p>\"quoted\" text</p>\n<!--\nmulti\n-->\n",
    );
    write(
        &dir.join("site.css"),
        "/* theme */\nbody { content: \"/*\"; }\n",
    );
    write(&dir.join("events.jsonl"), "{\"a\":1}\n{\"b\":2}\n");
    let json = stdout_json(&clocrap(&dir, &["--json"]));
    let counts = |name: &str| {
        let row = language(&json, name);
        (
            row["comment"].as_u64().unwrap(),
            row["code"].as_u64().unwrap(),
        )
    };
    assert_eq!(counts("C"), (2, 1));
    assert_eq!(counts("HTML"), (4, 1));
    assert_eq!(counts("CSS"), (1, 1));
    assert_eq!(counts("JSON"), (0, 2));
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn gitignored_files_are_not_counted() {
    let dir = fixture("ignore");
    write(&dir.join(".gitignore"), "generated/\n");
    write(&dir.join("keep.rs"), "fn k() {}\n");
    write(&dir.join("generated/skip.rs"), "fn s() {}\n");
    let json = stdout_json(&clocrap(&dir, &["--json"]));
    assert_eq!(json["total"]["files"], 1);
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn crap_score_of_the_fixture_function_matches_the_hand_computed_value() {
    let dir = fixture("crap");
    let source = dir.join("src/lib.rs");
    write(&source, LIB_RS);
    // Complexity 3 (base 1, two ifs). Lines 6, 7, 9, 10 are instrumented and
    // two of them ran, so coverage is 0.5.
    // CRAP = 3^2 * 0.5^3 + 3 = 9 / 8 + 3 = 4.125.
    let lcov = dir.join("lcov.info");
    let canonical = fs::canonicalize(&source).unwrap();
    write(
        &lcov,
        &format!(
            "SF:{}\nDA:6,1\nDA:7,1\nDA:9,0\nDA:10,0\nend_of_record\n",
            canonical.display()
        ),
    );

    let json = stdout_json(&clocrap(
        &dir,
        &["--json", "--lcov", lcov.to_str().unwrap()],
    ));
    let functions = &json["functions"];
    assert_eq!(functions["functions"][0]["name"], "f");
    assert_eq!(functions["functions"][0]["complexity"], 3);
    assert_eq!(functions["functions"][0]["coverage"], 0.5);
    assert_eq!(functions["functions"][0]["crap"], 4.125);
    assert_eq!(functions["over_threshold"], 0);
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn threshold_gate_exits_one_only_when_a_function_is_above_it() {
    let dir = fixture("gate");
    let source = dir.join("src/lib.rs");
    write(&source, LIB_RS);
    let lcov = dir.join("lcov.info");
    let canonical = fs::canonicalize(&source).unwrap();
    write(
        &lcov,
        &format!(
            "SF:{}\nDA:6,1\nDA:7,1\nDA:9,0\nDA:10,0\nend_of_record\n",
            canonical.display()
        ),
    );
    let lcov = lcov.to_str().unwrap();

    // Default threshold 30: 4.125 passes.
    let pass = clocrap(&dir, &["--lcov", lcov]);
    assert_eq!(pass.status.code(), Some(0), "{pass:?}");
    // 4.2 is above 4.125: still passes.
    let pass = clocrap(&dir, &["--lcov", lcov, "--threshold", "4.2"]);
    assert_eq!(pass.status.code(), Some(0));
    // 4 is below 4.125: fails with status 1.
    let fail = clocrap(&dir, &["--lcov", lcov, "--threshold", "4"]);
    assert_eq!(fail.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&fail.stdout).contains("OVER"));
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn without_coverage_the_report_is_complexity_only_and_never_gates() {
    let dir = fixture("complexity");
    write(&dir.join("src/lib.rs"), LIB_RS);
    let output = clocrap(&dir, &["--crap", "--threshold", "1"]);
    assert_eq!(output.status.code(), Some(0));
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("complexity only"), "{text}");
    assert!(text.lines().any(
        |line| line.split_whitespace().any(|word| word == "f") && line.contains("src/lib.rs:4")
    ));
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn diff_counts_only_added_lines_and_all_of_untracked_files() {
    let dir = fixture("diff");
    write(&dir.join("src/lib.rs"), LIB_RS);
    git(&dir, &["init", "-q"]);
    git(&dir, &["add", "."]);
    git(&dir, &["commit", "-q", "-m", "init"]);

    // One new code line in a tracked file, and a new untracked file of two lines.
    write(&dir.join("src/lib.rs"), &format!("{LIB_RS}fn g() {{}}\n"));
    write(&dir.join("new.rs"), "fn n() {}\n\n");

    let json = stdout_json(&clocrap(&dir, &["--diff", "HEAD", "--json", "--by-file"]));
    assert_eq!(json["total"]["files"], 2);
    assert_eq!(json["total"]["code"], 2);
    assert_eq!(json["total"]["blank"], 1);
    assert_eq!(json["total"]["comment"], 0);
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn diff_against_an_unknown_ref_is_an_error() {
    let dir = fixture("badref");
    write(&dir.join("a.rs"), "fn a() {}\n");
    git(&dir, &["init", "-q"]);
    let output = clocrap(&dir, &["--diff", "no-such-ref"]);
    assert_eq!(output.status.code(), Some(2));
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn counts_the_files_git_lists_unless_told_to_walk() {
    let dir = fixture("vcs-default");
    git(&dir, &["init", "-q"]);
    write(&dir.join(".gitignore"), "ignored.rs\n");
    write(&dir.join("tracked.rs"), "fn t() {}\n");
    write(&dir.join(".github/ci.yml"), "name: ci\n");
    write(&dir.join("untracked.rs"), "fn u() {}\n");
    write(&dir.join("ignored.rs"), "fn i() {}\n");
    git(&dir, &["add", "tracked.rs", ".github/ci.yml"]);

    // Tracked, hidden but tracked, and untracked but not ignored.
    let by_git = stdout_json(&clocrap(&dir, &["--json"]));
    assert_eq!(by_git["total"]["files"], 3);
    // A walk skips the hidden directory.
    let walked = stdout_json(&clocrap(&dir, &["--json", "--walk"]));
    assert_eq!(walked["total"]["files"], 2);
    fs::remove_dir_all(&dir).unwrap();
}

fn git(dir: &Path, args: &[&str]) {
    let status = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args([
            "-c",
            "user.name=clocrap",
            "-c",
            "user.email=clocrap@example.invalid",
        ])
        .args(args)
        .status()
        .unwrap();
    assert!(status.success(), "git {args:?} failed");
}

#[test]
fn diff_with_crap_keeps_only_functions_that_contain_a_changed_line() {
    let dir = fixture("diff-crap");
    write(&dir.join("src/lib.rs"), LIB_RS);
    git(&dir, &["init", "-q"]);
    git(&dir, &["add", "."]);
    git(&dir, &["commit", "-q", "-m", "init"]);

    // A new function after `f`; `f` itself is untouched.
    write(
        &dir.join("src/lib.rs"),
        &format!("{LIB_RS}\npub fn g(y: u32) -> u32 {{\n    if y > 0 {{ y }} else {{ 0 }}\n}}\n"),
    );
    let json = stdout_json(&clocrap(&dir, &["--diff", "HEAD", "--crap", "--json"]));
    let names: Vec<&str> = json["functions"]["functions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|f| f["name"].as_str().unwrap())
        .collect();
    assert_eq!(names, ["g"]);
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn lean_functions_take_their_coverage_from_the_c_they_compile_to() {
    let dir = fixture("lean");
    write(
        &dir.join("pkg/Cov/Basic.lean"),
        "\
namespace Cov
/-- Tested. -/
def classify (n : Nat) : String :=
  if n == 0 then \"zero\" else if n % 2 == 0 then \"even\" else \"odd\"
def unused (n : Nat) : Nat := match n with
  | 0 => 1
  | k + 1 => k * 2
@[inline] def inlined (n : Nat) : Nat := n
theorem t : 1 = 1 := rfl
end Cov
",
    );
    // The C file must exist, so its path canonicalises like the Lean file's.
    let c_file = dir.join("pkg/.lake/build/ir/Cov/Basic.c");
    write(&c_file, "");
    let c_file = fs::canonicalize(&c_file).unwrap();
    write(
        &dir.join("lcov.info"),
        &format!(
            "SF:{}\nFN:10,lp_pkg_Cov_classify\nFN:20,lp_pkg_Cov_classify___boxed\nFN:30,lp_pkg_Cov_unused\nFN:40,initialize_pkg_Cov_Basic\nDA:10,1\nDA:11,1\nDA:12,0\nDA:20,0\nDA:30,0\nDA:40,1\nend_of_record\n",
            c_file.display()
        ),
    );
    let output = clocrap(&dir, &["--json", "--lcov", "lcov.info", "pkg"]);
    let json = stdout_json(&output);
    assert_eq!(language(&json, "Lean")["code"], 9);
    assert_eq!(language(&json, "Lean")["comment"], 1);
    let crap = &json["functions"];
    let rows: Vec<(String, u64, String)> = crap["functions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|f| {
            (
                f["name"].as_str().unwrap().to_string(),
                f["complexity"].as_u64().unwrap(),
                format!("{:.3}", f["coverage"].as_f64().unwrap()),
            )
        })
        .collect();
    // unused: complexity 2, untested, CRAP 6; classify: complexity 3, two of
    // its three C lines ran.
    assert_eq!(
        rows,
        [
            ("unused".to_string(), 2, "0.000".to_string()),
            ("classify".to_string(), 3, "0.667".to_string()),
        ]
    );
    assert_eq!(crap["no_code"], 1);
    fs::remove_dir_all(&dir).unwrap();
}
