//! The `clocrap` command. See the README for usage.

use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::Arc;

use clap::Parser;
use clocrap::crap::{self, DEFAULT_THRESHOLD};
use clocrap::diff;
use clocrap::lcov::Coverage;
use clocrap::report;
use clocrap::walk::{self, ScanOptions};

/// Count source lines by language, and score functions by CRAP.
// Each flag is a switch on the command line, so the bools are the design.
#[allow(clippy::struct_excessive_bools)]
#[derive(Debug, Parser)]
#[command(name = "clocrap", version, about)]
struct Cli {
    /// Files or directories to count. Defaults to the current directory.
    paths: Vec<PathBuf>,
    /// Print JSON instead of tables.
    #[arg(long)]
    json: bool,
    /// Also print one row per file, in path order.
    #[arg(long)]
    by_file: bool,
    /// Count only the lines added or changed since this git ref.
    #[arg(long, value_name = "REF")]
    diff: Option<String>,
    /// Find every function and report its cyclomatic complexity. Implied by
    /// --lcov, which also scores CRAP.
    #[arg(long)]
    crap: bool,
    /// An lcov coverage file, as `cargo llvm-cov --lcov` writes. Repeat the
    /// flag to merge several. Turns complexity into CRAP scores.
    #[arg(long, value_name = "FILE")]
    lcov: Vec<PathBuf>,
    /// Worker threads that read files. Zero picks four, the most that file
    /// opens scale to on macOS.
    #[arg(long, value_name = "N", default_value_t = 0)]
    threads: usize,
    /// Score functions in files the coverage report does not list (such as
    /// test code) as untested. By default they are left out.
    #[arg(long)]
    count_unlisted: bool,
    /// Exit with status 1 when a function's CRAP score is above this. Only
    /// applies with --lcov.
    #[arg(long, value_name = "N", default_value_t = DEFAULT_THRESHOLD)]
    threshold: f64,
}

fn main() -> ExitCode {
    match run(&Cli::parse()) {
        Ok(code) => code,
        Err(message) => {
            eprintln!("clocrap: {message}");
            ExitCode::from(2)
        }
    }
}

fn run(cli: &Cli) -> Result<ExitCode, String> {
    let cwd = std::env::current_dir()
        .and_then(std::fs::canonicalize)
        .map_err(|err| err.to_string())?;
    let roots = if cli.paths.is_empty() {
        vec![PathBuf::from(".")]
    } else {
        cli.paths.clone()
    };
    let changed = match &cli.diff {
        Some(git_ref) => Some(Arc::new(diff::changed_since(&roots, git_ref)?)),
        None => None,
    };
    let want_crap = cli.crap || !cli.lcov.is_empty();
    let reports = walk::scan(
        &roots,
        &ScanOptions {
            changed,
            functions: want_crap,
            threads: cli.threads,
        },
    )?;

    let coverage = if cli.lcov.is_empty() {
        None
    } else {
        Some(Coverage::read(&cli.lcov)?)
    };
    let ranking = want_crap.then(|| crap::rank(&reports, coverage.as_ref(), cli.count_unlisted));

    let mut out = io::BufWriter::new(io::stdout().lock());
    if cli.json {
        let mut document = report::json_counts(&reports, &cwd, cli.by_file);
        if let Some(ranking) = &ranking {
            document["functions"] = report::json_functions(ranking, &cwd, cli.threshold);
        }
        serde_json::to_writer_pretty(&mut out, &document).map_err(|err| err.to_string())?;
        writeln!(out).map_err(|err| err.to_string())?;
    } else {
        if cli.by_file {
            report::write_by_file(&mut out, &reports, &cwd).map_err(|err| err.to_string())?;
            writeln!(out).map_err(|err| err.to_string())?;
        }
        report::write_table(&mut out, &reports).map_err(|err| err.to_string())?;
        if let Some(ranking) = &ranking {
            writeln!(out).map_err(|err| err.to_string())?;
            report::write_functions(&mut out, ranking, &cwd, cli.threshold, cli.count_unlisted)
                .map_err(|err| err.to_string())?;
        }
    }
    out.flush().map_err(|err| err.to_string())?;

    // The gate needs coverage: without it, CRAP is not defined.
    if let Some(ranking) = &ranking
        && coverage.is_some()
    {
        let over = crap::over_threshold(&ranking.functions, cli.threshold);
        if over > 0 {
            eprintln!(
                "clocrap: {over} function(s) above the CRAP threshold of {}",
                cli.threshold
            );
            return Ok(ExitCode::from(1));
        }
    }
    Ok(ExitCode::SUCCESS)
}
