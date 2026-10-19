# clocrap

One static binary that counts source lines by language, like `cloc`, and scores
every function by its CRAP value, so a repository's worst code is listed first.
It walks a tree in parallel, respects `.gitignore`, and can count only the lines
a change added.

```text
$ cargo llvm-cov --locked -p rescue-core --lcov --output-path lcov.info
$ clocrap --crap --lcov lcov.info crates/rescue-core
Language    files    blank  comment     code
--------------------------------------------
Rust           23      376      548     4388
TOML            1        4        2       23
--------------------------------------------
SUM:           24      380      550     4411

CRAP  complexity  coverage  function             location
30.0           5        0%  name                 crates/rescue-core/src/paths.rs:45
13.0          13       98%  parse_extended       crates/rescue-core/src/keys.rs:462
12.0          12      100%  parse_path           crates/rescue-core/src/paths.rs:370

0 of 93 functions above the CRAP threshold of 30
142 functions in files the coverage report does not list were left out; --count-unlisted scores them as untested
```

## Install

From a checkout:

```bash
cargo install --locked --path .
```

From GitHub, once the repository is public:

```bash
cargo install --locked --git https://github.com/winnowwallet/clocrap
```

The toolchain is pinned in `rust-toolchain.toml`. `cargo install` uses it.

## Counting lines

```bash
clocrap                      # the current directory, as a table
clocrap src tests            # several roots
clocrap --by-file            # a row per file as well
clocrap --json               # machine-readable, for scripts
clocrap --diff origin/main   # only the lines added or changed against a ref
```

Counts are by language, detected from the file extension:

| Language   | Extensions                                 | Comments                            |
|------------|--------------------------------------------|-------------------------------------|
| Rust       | `rs`                                       | `//`, nested `/* */`                |
| TOML       | `toml`                                     | `#`                                 |
| JSON       | `json`                                     | none                                |
| Markdown   | `md`, `markdown`                           | none, so every non-blank line is code |
| Python     | `py`                                       | `#`                                 |
| Swift      | `swift`                                    | `//`, nested `/* */`                |
| TypeScript | `ts`, `tsx`, `mts`, `cts`                  | `//`, `/* */`                       |
| JavaScript | `js`, `jsx`, `mjs`, `cjs`                  | `//`, `/* */`                       |
| Kotlin     | `kt`, `kts`                                | `//`, nested `/* */`                |
| Shell      | `sh`, `bash`, `zsh`                        | `#`                                 |
| YAML       | `yml`, `yaml`                              | `#`                                 |

A line is **blank** if it holds only whitespace, **comment** if it holds only
comment text, and **code** otherwise. A comment marker inside a string is code.
Doc comments (`///`, `//!`) are comments. Python docstrings are code, since
they are string literals.

The total of lines matches `wc -l` for files that end in a newline. A final
line without a newline counts as one more line than `wc -l` reports.

Hidden files and directories are skipped, and `.gitignore` is honoured even
outside a git repository. Files with an unknown extension, and files with a NUL
byte in their first 8 KB, are not counted.

`--diff <REF>` runs `git diff -U0 <REF>` in each repository the roots belong
to. It counts only the added and changed lines in the working tree. A file with
no changed lines is left out. An untracked file that git does not ignore counts
in full. With `--crap`, only the functions that contain a changed line are
listed.

## CRAP

```text
CRAP(m) = comp(m)^2 * (1 - cov(m))^3 + comp(m)
```

`comp(m)` is the cyclomatic complexity of the function. `cov(m)` is the share of
the function's instrumented lines that the tests ran, from 0 to 1. A complex
function with no tests scores `comp^2 + comp`. A function with full coverage
scores its complexity.

Complexity is 1 plus one for each decision point in the function's body:

- Rust: `if` (including `else if` and `if let`), `while`, `for`, `loop`, each
  `match` arm beyond the first, `&&`, `||`.
- Python: `if`, `elif`, `for`, `while`, `except`, `and`, `or`, the conditional
  expression, each `case` beyond the first, comprehension `for` and `if`.
- TypeScript and JavaScript: `if`, `for`, `for-in` and `for-of`, `while`, `do`,
  each `case`, `catch`, the ternary operator, `&&`, `||`, `??`.
- Swift: `if`, `guard`, `for`, `while`, `repeat`, `catch`, each `switch` entry
  beyond the first, `&&`, `||`.

Closures and lambdas count toward the function they sit in. A nested function
is scored on its own. The `?` operator, `try` and `else` are not decision points.

Coverage is line coverage, not branch coverage: the instrumented lines of the
function's span (its first to its last line) that ran, divided by the
instrumented lines in that span. A function with no instrumented lines counts as
0% covered.

A file the lcov report does not list is usually one the report leaves out on
purpose, such as test code. Its functions are left out of the CRAP table, and
the report says how many. `--count-unlisted` scores them as 0% covered instead.

Without `--lcov` there is no coverage, so no CRAP score. The tool then lists
complexity only. `--crap` alone does this.

Get an lcov file from `cargo-llvm-cov`:

```bash
cargo llvm-cov --locked --lcov --output-path lcov.info
clocrap --crap --lcov lcov.info
```

Functions are found with tree-sitter, for Rust, Python, Swift, TypeScript, TSX
and JavaScript. Other languages have counts but no function list.

### The gate

With `--lcov`, a function whose CRAP score is above `--threshold` (default 30,
the usual CRAP limit) makes the command exit with status 1 after printing the
report. That is the gate for CI:

```bash
clocrap --lcov lcov.info --threshold 30
```

With `--diff <REF>` the functions reported are those that contain a changed
line, so the gate checks what a change touched.

## Exit status

| Status | Meaning                                                             |
|--------|---------------------------------------------------------------------|
| 0      | counted, and no function is above the threshold                      |
| 1      | a function's CRAP score is above `--threshold` (only with `--lcov`) |
| 2      | a usage, I/O or git error                                           |

## Speed

On an Apple M5 Max, counting 100,000 files (50,000 Rust and 50,000 Python, about
4.4 million lines) takes about 1.2 to 1.5 seconds, wall clock, with
`--threads 4`, the default.

The time goes to the kernel. Plain `cat` over the same files, run in parallel,
has the same curve: real time stops falling at four or so readers, while system
time keeps rising. File opens contend in macOS past that point. So the default
is four workers, and `--threads` changes it.

`scripts/bench.py [DIR]` times clocrap against `cloc` and `tokei` on one
directory when they are installed, and reports each tool's code total.

## Limits

- Strings are tracked per line. A string that interpolates another string, as
  in a Swift `\(...)`, can confuse the line classifier when the inner string
  holds a comment marker.
- Complexity is a count of decision nodes, not a full control-flow analysis.
- Coverage is line coverage. A branch that never runs on a line that did run is
  not seen.
- `--diff` takes its line numbers from `git diff`. A path that git quotes, which
  happens when it holds a control character, a double quote or a backslash, is
  skipped, so its changes are not counted.

## Development

```bash
cargo fmt --all --check
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo test --locked
cargo deny check
```

## License

MIT. See [LICENSE](LICENSE).
