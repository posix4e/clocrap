//! The files git would commit: tracked files, plus untracked files that git
//! does not ignore. This is the default list of files to count.

use std::ffi::OsStr;
use std::io::ErrorKind;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The files git lists under `root`, as paths under `root`: every tracked file
/// and every untracked file that `.gitignore` and the other standard ignore
/// files do not exclude. Hidden files are included when git lists them. A
/// tracked file that has been deleted from the working tree is left out, and
/// so is anything that is not a plain file, such as a symlink or a submodule.
///
/// `root` may be a directory or a single file. Returns `Ok(None)` when `root`
/// is not inside a git repository, or when git is not installed, so the caller
/// can fall back to walking the directory.
///
/// # Errors
///
/// Returns an error if git runs and fails for any other reason, so that a
/// repository git refuses to read is not silently counted as a plain tree.
pub fn files_under(root: &Path) -> Result<Option<Vec<PathBuf>>, String> {
    let (dir, only) = if root.is_dir() {
        (root, None)
    } else {
        match (root.parent(), root.file_name()) {
            (Some(parent), Some(name)) => (parent, Some(name)),
            _ => return Ok(None),
        }
    };

    let mut command = Command::new("git");
    command.arg("-C").arg(dir).args([
        "ls-files",
        "-z",
        "--cached",
        "--others",
        "--exclude-standard",
    ]);
    if let Some(name) = only {
        command.arg("--").arg(literal_pathspec(name));
    }
    let output = match command.output() {
        Ok(output) => output,
        Err(err) if err.kind() == ErrorKind::NotFound => return Ok(None),
        Err(err) => return Err(format!("cannot run git: {err}")),
    };
    if !output.status.success() {
        let message = String::from_utf8_lossy(&output.stderr);
        if message.contains("not a git repository") {
            return Ok(None);
        }
        return Err(format!(
            "git ls-files failed in {}: {}",
            dir.display(),
            message.trim()
        ));
    }

    let files = output
        .stdout
        .split(|&byte| byte == 0)
        .filter(|name| !name.is_empty())
        .map(|name| dir.join(String::from_utf8_lossy(name).as_ref()))
        .filter(|path| std::fs::symlink_metadata(path).is_ok_and(|metadata| metadata.is_file()))
        .collect();
    Ok(Some(files))
}

/// A pathspec that matches the named file and nothing else, whatever
/// characters its name holds.
fn literal_pathspec(name: &OsStr) -> String {
    format!(":(literal){}", name.to_string_lossy())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn git(dir: &Path, args: &[&str]) {
        let status = Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .status()
            .unwrap();
        assert!(status.success(), "git {args:?} failed");
    }

    fn write(path: &Path, contents: &str) {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    /// A fresh directory, a git repository when `repo` is set.
    fn fixture(name: &str, repo: bool) -> PathBuf {
        let dir = fs::canonicalize(std::env::temp_dir())
            .unwrap()
            .join(format!("clocrap-vcs-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        if repo {
            git(&dir, &["init", "-q"]);
        }
        dir
    }

    fn names(root: &Path, files: &[PathBuf]) -> Vec<String> {
        let mut names: Vec<String> = files
            .iter()
            .map(|path| path.strip_prefix(root).unwrap().display().to_string())
            .collect();
        names.sort();
        names
    }

    #[test]
    fn lists_tracked_and_untracked_files_but_not_ignored_ones() {
        let dir = fixture("lists", true);
        write(&dir.join(".gitignore"), "ignored.rs\ngenerated/\n");
        write(&dir.join("tracked.rs"), "fn t() {}\n");
        write(&dir.join(".hidden_tracked.rs"), "fn h() {}\n");
        write(&dir.join("untracked.rs"), "fn u() {}\n");
        write(&dir.join("ignored.rs"), "fn i() {}\n");
        write(&dir.join("generated/skip.rs"), "fn s() {}\n");
        git(
            &dir,
            &["add", ".gitignore", "tracked.rs", ".hidden_tracked.rs"],
        );

        let files = files_under(&dir).unwrap().unwrap();
        assert_eq!(
            names(&dir, &files),
            [
                ".gitignore",
                ".hidden_tracked.rs",
                "tracked.rs",
                "untracked.rs"
            ]
        );
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_tracked_file_deleted_from_the_working_tree_is_left_out() {
        let dir = fixture("deleted", true);
        write(&dir.join("gone.rs"), "fn g() {}\n");
        write(&dir.join("kept.rs"), "fn k() {}\n");
        git(&dir, &["add", "gone.rs", "kept.rs"]);
        fs::remove_file(dir.join("gone.rs")).unwrap();

        let files = files_under(&dir).unwrap().unwrap();
        assert_eq!(names(&dir, &files), ["kept.rs"]);
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_subdirectory_lists_only_its_own_files() {
        let dir = fixture("subdir", true);
        write(&dir.join("top.rs"), "fn t() {}\n");
        write(&dir.join("sub/inner.rs"), "fn i() {}\n");
        git(&dir, &["add", "."]);

        let sub = dir.join("sub");
        let files = files_under(&sub).unwrap().unwrap();
        assert_eq!(names(&sub, &files), ["inner.rs"]);
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_single_file_root_lists_just_that_file() {
        let dir = fixture("file-root", true);
        write(&dir.join("a.rs"), "fn a() {}\n");
        write(&dir.join("b.rs"), "fn b() {}\n");
        git(&dir, &["add", "."]);

        let files = files_under(&dir.join("a.rs")).unwrap().unwrap();
        assert_eq!(names(&dir, &files), ["a.rs"]);
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_directory_outside_any_repository_is_none() {
        let dir = fixture("no-repo", false);
        write(&dir.join("a.rs"), "fn a() {}\n");
        assert_eq!(files_under(&dir), Ok(None));
        fs::remove_dir_all(&dir).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn a_symlink_is_not_a_file() {
        let dir = fixture("symlink", true);
        write(&dir.join("real.rs"), "fn r() {}\n");
        std::os::unix::fs::symlink(dir.join("real.rs"), dir.join("link.rs")).unwrap();
        git(&dir, &["add", "."]);

        let files = files_under(&dir).unwrap().unwrap();
        assert_eq!(names(&dir, &files), ["real.rs"]);
        fs::remove_dir_all(&dir).unwrap();
    }
}
