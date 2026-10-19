//! Parallel directory walk. Each file is read, classified and counted on the
//! worker thread that found it, so the walk and the counting share one pass.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use ignore::WalkBuilder;

use crate::complexity::{Analyzer, Function};
use crate::count::{LineCounts, for_each_line};
use crate::diff::ChangedLines;
use crate::lang::Language;

/// Bytes read when looking for a NUL, the usual sign of a binary file.
const BINARY_PROBE: usize = 8000;

/// The counts for one source file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileReport {
    /// The path as the walk found it, under one of the roots.
    pub path: PathBuf,
    pub language: Language,
    pub counts: LineCounts,
    /// The functions in the file, when the scan asked for them. In diff mode,
    /// only the functions that contain a changed line.
    pub functions: Vec<Function>,
}

/// What a scan should count.
#[derive(Debug, Clone, Default)]
pub struct ScanOptions {
    /// When set, only the lines in here are counted, and a file with none of
    /// them is left out.
    pub changed: Option<Arc<ChangedLines>>,
    /// Whether to parse source files and find their functions.
    pub functions: bool,
    /// Worker threads that read and count files. Zero picks `DEFAULT_THREADS`.
    pub threads: usize,
}

/// Workers used when the caller does not say. File opens contend in the kernel
/// past about four threads on macOS, so more workers make the walk slower, not
/// faster (see the README).
pub const DEFAULT_THREADS: usize = 4;

/// Files handed to a worker at a time. Large enough that the shared counter is
/// not contended, small enough that the workers finish close together.
const CHUNK: usize = 64;

/// Walks every root and counts every recognised source file under it.
///
/// Hidden files and directories are skipped, and `.gitignore` files are
/// honoured even outside a git repository. The result is sorted by path, so
/// the output does not depend on thread scheduling.
///
/// The directory walk runs on one thread: it is cheap, and the parallel walker
/// of the `ignore` crate spends more time in the kernel on contended file
/// system calls than it saves. The files are then read and counted by
/// `options.threads` workers.
///
/// # Errors
///
/// Returns an error if a root does not exist or cannot be read.
pub fn scan(roots: &[PathBuf], options: &ScanOptions) -> Result<Vec<FileReport>, String> {
    let canonical = roots
        .iter()
        .map(|root| fs::canonicalize(root).map_err(|err| format!("{}: {err}", root.display())))
        .collect::<Result<Vec<_>, _>>()?;
    let Some((first, rest)) = canonical.split_first() else {
        return Ok(Vec::new());
    };

    let mut builder = WalkBuilder::new(first);
    for root in rest {
        builder.add(root);
    }
    builder.require_git(false);
    let mut paths = Vec::new();
    for entry in builder.build() {
        match entry {
            Ok(entry) => {
                if entry.file_type().is_some_and(|kind| kind.is_file()) && recognised(entry.path())
                {
                    paths.push(entry.into_path());
                }
            }
            Err(err) => eprintln!("clocrap: {err}"),
        }
    }

    let threads = match options.threads {
        0 => DEFAULT_THREADS,
        n => n,
    };
    let next = AtomicUsize::new(0);
    let mut reports = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                scope.spawn(|| {
                    // One analyzer per worker: its parsers are reused across files.
                    let mut analyzer = Analyzer::default();
                    let mut found = Vec::new();
                    loop {
                        let start = next.fetch_add(CHUNK, Ordering::Relaxed);
                        if start >= paths.len() {
                            break;
                        }
                        let end = (start + CHUNK).min(paths.len());
                        for path in &paths[start..end] {
                            if let Some(report) = scan_file(path, options, &mut analyzer) {
                                found.push(report);
                            }
                        }
                    }
                    found
                })
            })
            .collect();
        workers
            .into_iter()
            .flat_map(|worker| {
                worker
                    .join()
                    .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
            })
            .collect::<Vec<FileReport>>()
    });
    reports.sort_by(|a, b| a.path.cmp(&b.path));
    Ok(reports)
}

/// Whether the path has an extension clocrap knows.
fn recognised(path: &Path) -> bool {
    path.extension()
        .and_then(|extension| extension.to_str())
        .and_then(Language::from_extension)
        .is_some()
}

/// Counts one file, or returns `None` if it is not a recognised text file or,
/// in diff mode, has no changed lines.
fn scan_file(path: &Path, options: &ScanOptions, analyzer: &mut Analyzer) -> Option<FileReport> {
    let language = path
        .extension()
        .and_then(|extension| extension.to_str())
        .and_then(Language::from_extension)?;
    let change = match &options.changed {
        Some(changed) => Some(changed.get(path)?),
        None => None,
    };
    let source = match fs::read(path) {
        Ok(source) => source,
        Err(err) => {
            eprintln!("clocrap: {}: {err}", path.display());
            return None;
        }
    };
    if source[..source.len().min(BINARY_PROBE)].contains(&0) {
        return None;
    }

    let syntax = language.syntax();
    let mut counts = LineCounts::default();
    for_each_line(&source, &syntax, |number, kind| {
        if change.is_none_or(|change| change.contains(number)) {
            counts.record(kind);
        }
    });
    if change.is_some() && counts.total() == 0 {
        return None;
    }

    let mut functions = Vec::new();
    if options.functions {
        functions = analyzer.functions(language, path, &source);
        if let Some(change) = change {
            functions.retain(|f| (f.start_line..=f.end_line).any(|line| change.contains(line)));
        }
    }
    Some(FileReport {
        path: path.to_path_buf(),
        language,
        counts,
        functions,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn write(path: &Path, contents: &str) {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        let mut file = fs::File::create(path).unwrap();
        file.write_all(contents.as_bytes()).unwrap();
    }

    #[test]
    fn skips_hidden_files_unknown_extensions_and_binaries() {
        let dir = tempfile_dir("walk-skip");
        write(&dir.join("a.rs"), "fn a() {}\n");
        write(&dir.join("notes.xyz"), "text\n");
        write(&dir.join(".hidden.rs"), "fn h() {}\n");
        fs::write(dir.join("b.rs"), b"fn b() {}\0\n").unwrap();

        let reports = scan(std::slice::from_ref(&dir), &ScanOptions::default()).unwrap();
        let names: Vec<String> = reports
            .iter()
            .map(|r| r.path.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        assert_eq!(names, ["a.rs"]);
    }

    #[test]
    fn honours_gitignore_without_a_git_repository() {
        let dir = tempfile_dir("walk-ignore");
        write(&dir.join(".gitignore"), "generated/\n");
        write(&dir.join("keep.rs"), "fn k() {}\n");
        write(&dir.join("generated/skip.rs"), "fn s() {}\n");

        let reports = scan(std::slice::from_ref(&dir), &ScanOptions::default()).unwrap();
        assert_eq!(reports.len(), 1);
        assert!(reports[0].path.ends_with("keep.rs"));
    }

    #[test]
    fn missing_root_is_an_error() {
        let err = scan(
            &[PathBuf::from("/no/such/clocrap/root")],
            &ScanOptions::default(),
        );
        assert!(err.is_err());
    }

    /// A fresh directory under the system temp dir, unique per test name and process.
    fn tempfile_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("clocrap-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }
}
