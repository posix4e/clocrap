//! `--diff <ref>`: the lines added or changed against a git ref, read from
//! `git diff -U0`. Lines are only added or changed when the diff says so, so a
//! line that was merely moved or re-indented counts as changed.

use std::collections::{BTreeSet, HashMap};
use std::ops::RangeInclusive;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Which lines of one file a diff touched.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FileChange {
    /// A file untracked by git. Every line is new.
    Everything,
    /// 1-based inclusive ranges of added or changed lines in the new file.
    Lines(Vec<RangeInclusive<u64>>),
}

impl FileChange {
    /// Whether the given 1-based line is in this change.
    #[must_use]
    pub fn contains(&self, line: u64) -> bool {
        match self {
            FileChange::Everything => true,
            FileChange::Lines(ranges) => ranges.iter().any(|range| range.contains(&line)),
        }
    }
}

/// The changed lines of every file that a diff touched, keyed by absolute path.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ChangedLines {
    files: HashMap<PathBuf, FileChange>,
}

impl ChangedLines {
    /// The change to `path`, if the diff touched it.
    #[must_use]
    pub fn get(&self, path: &Path) -> Option<&FileChange> {
        self.files.get(path)
    }
}

/// The changed lines between `git_ref` and the working tree, for every git
/// repository that holds one of `roots`. Untracked files that git does not
/// ignore count as all new.
///
/// # Errors
///
/// Returns an error if a root is not inside a git repository, or if git
/// rejects `git_ref`.
pub fn changed_since(roots: &[PathBuf], git_ref: &str) -> Result<ChangedLines, String> {
    let mut tops = BTreeSet::new();
    for root in roots {
        let dir = if root.is_dir() {
            root.as_path()
        } else {
            root.parent().unwrap_or(root.as_path())
        };
        tops.insert(toplevel(dir)?);
    }

    let mut files = HashMap::new();
    for top in tops {
        let diff = git(
            &top,
            &[
                "-c",
                "core.quotepath=off",
                "diff",
                "--no-color",
                "--no-ext-diff",
                "--src-prefix=a/",
                "--dst-prefix=b/",
                "-U0",
                git_ref,
                "--",
            ],
        )?;
        files.extend(parse_diff(&top, &diff));

        let untracked = git(&top, &["ls-files", "--others", "--exclude-standard", "-z"])?;
        for name in untracked.split('\0').filter(|name| !name.is_empty()) {
            files.insert(top.join(name), FileChange::Everything);
        }
    }
    Ok(ChangedLines { files })
}

fn toplevel(dir: &Path) -> Result<PathBuf, String> {
    let out = git(dir, &["rev-parse", "--show-toplevel"])?;
    let top = PathBuf::from(out.trim_end());
    std::fs::canonicalize(&top).map_err(|err| format!("{}: {err}", top.display()))
}

fn git(dir: &Path, args: &[&str]) -> Result<String, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .map_err(|err| format!("cannot run git: {err}"))?;
    if !output.status.success() {
        return Err(format!(
            "git {} failed in {}: {}",
            args.first().copied().unwrap_or(""),
            dir.display(),
            String::from_utf8_lossy(&output.stderr).trim_end()
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

/// Reads a `git diff -U0` text. Hunk bodies are skipped by their line counts,
/// not by their first character, so an added line that starts with `++ ` is
/// not taken for a file header.
fn parse_diff(top: &Path, text: &str) -> HashMap<PathBuf, FileChange> {
    let mut out = HashMap::new();
    let mut current: Option<(PathBuf, Vec<RangeInclusive<u64>>)> = None;
    // Removed and added lines still to come in the current hunk.
    let mut body: Option<(u64, u64)> = None;

    for line in text.lines() {
        if let Some((removed, added)) = body {
            match line.as_bytes().first() {
                Some(b'-') => body = Some((removed.saturating_sub(1), added)),
                Some(b'+') => body = Some((removed, added.saturating_sub(1))),
                _ => {}
            }
            if body == Some((0, 0)) {
                body = None;
            }
            continue;
        }

        if line.starts_with("diff --git ") {
            finish(&mut current, &mut out);
        } else if let Some(rest) = line.strip_prefix("+++ ") {
            finish(&mut current, &mut out);
            current = rest
                .trim_end_matches('\t')
                .strip_prefix("b/")
                .map(|path| (top.join(path), Vec::new()));
        } else if line.starts_with("@@ ")
            && let Some(hunk) = parse_hunk(line)
        {
            body = Some((hunk.removed, hunk.new_count));
            if hunk.new_count > 0
                && let Some((_, ranges)) = current.as_mut()
            {
                ranges.push(hunk.new_start..=hunk.new_start + hunk.new_count - 1);
            }
        }
    }
    finish(&mut current, &mut out);
    out
}

fn finish(
    current: &mut Option<(PathBuf, Vec<RangeInclusive<u64>>)>,
    out: &mut HashMap<PathBuf, FileChange>,
) {
    if let Some((path, ranges)) = current.take() {
        out.insert(path, FileChange::Lines(ranges));
    }
}

/// The counts a `@@ -a,b +c,d @@` header announces.
#[derive(Debug, PartialEq, Eq)]
struct Hunk {
    /// Lines the hunk removes from the old file.
    removed: u64,
    new_start: u64,
    /// Lines the hunk adds to the new file.
    new_count: u64,
}

fn parse_hunk(line: &str) -> Option<Hunk> {
    let mut parts = line.split_whitespace().skip(1);
    let (_, removed) = parse_range(parts.next()?.strip_prefix('-')?)?;
    let (new_start, new_count) = parse_range(parts.next()?.strip_prefix('+')?)?;
    Some(Hunk {
        removed,
        new_start,
        new_count,
    })
}

/// `start,count`, where a missing count means one line.
fn parse_range(text: &str) -> Option<(u64, u64)> {
    match text.split_once(',') {
        Some((start, count)) => Some((start.parse().ok()?, count.parse().ok()?)),
        None => Some((text.parse().ok()?, 1)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hunk_header_counts() {
        assert_eq!(
            parse_hunk("@@ -2 +2,2 @@ fn f()"),
            Some(Hunk {
                removed: 1,
                new_start: 2,
                new_count: 2,
            })
        );
        assert_eq!(
            parse_hunk("@@ -10,0 +12 @@"),
            Some(Hunk {
                removed: 0,
                new_start: 12,
                new_count: 1,
            })
        );
        assert_eq!(parse_hunk("@@ garbage @@"), None);
    }

    #[test]
    fn added_and_changed_lines_are_ranges_in_the_new_file() {
        let diff = "\
diff --git a/src/a.rs b/src/a.rs
index 111..222 100644
--- a/src/a.rs
+++ b/src/a.rs
@@ -2 +2,2 @@
-old
+new
+++ inside
@@ -10,0 +12 @@
+added
";
        let changes = parse_diff(Path::new("/repo"), diff);
        assert_eq!(
            changes.get(Path::new("/repo/src/a.rs")),
            Some(&FileChange::Lines(vec![2..=3, 12..=12]))
        );
    }

    #[test]
    fn deleted_files_have_no_new_lines() {
        let diff = "\
diff --git a/gone.rs b/gone.rs
deleted file mode 100644
--- a/gone.rs
+++ /dev/null
@@ -1,2 +0,0 @@
-x
-y
";
        assert!(parse_diff(Path::new("/repo"), diff).is_empty());
    }

    #[test]
    fn everything_contains_every_line() {
        assert!(FileChange::Everything.contains(1_000_000));
        let lines = FileChange::Lines(vec![3..=5, 9..=9]);
        assert!(lines.contains(3) && lines.contains(5) && lines.contains(9));
        assert!(!lines.contains(2) && !lines.contains(6) && !lines.contains(8));
    }
}
