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
