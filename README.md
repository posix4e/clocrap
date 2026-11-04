# clocrap

One binary, written in Lean, that counts source lines by language, like `cloc`,
and scores every function by its CRAP value, so a repository's worst code is
listed first.
It counts the files git would commit (tracked files plus untracked files that
`.gitignore` does not exclude), reads them in parallel, and can count only the
lines a change added.

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

With [elan](https://github.com/leanprover/elan), from a checkout:

```bash
lake build clocrap
cp .lake/build/bin/clocrap ~/.local/bin/
```

The Lean version is pinned in `lean-toolchain`, and elan fetches it. clocrap
uses only Lean's own library: no C code, no tree-sitter, no other packages.

## Counting lines

```bash
clocrap                      # the current directory, as a table
clocrap src tests            # several roots
clocrap --by-file            # a row per file as well
clocrap --walk               # every file under the paths, tracked or not
clocrap --json               # machine-readable, for scripts
clocrap --diff origin/main   # only the lines added or changed against a ref
```

Counts are by language, detected from the file extension:

| Language   | Extensions                                 | Comments                            |
|------------|--------------------------------------------|-------------------------------------|
| Rust       | `rs`                                       | `//`, nested `/* */`                |
| TOML       | `toml`                                     | `#`                                 |
| JSON       | `json`, `jsonl`, `ndjson`                  | none                                |
| Markdown   | `md`, `markdown`                           | none, so every non-blank line is code |
| Python     | `py`                                       | `#`                                 |
| Swift      | `swift`                                    | `//`, nested `/* */`                |
| TypeScript | `ts`, `tsx`, `mts`, `cts`                  | `//`, `/* */`                       |
| JavaScript | `js`, `jsx`, `mjs`, `cjs`                  | `//`, `/* */`                       |
| Kotlin     | `kt`, `kts`                                | `//`, nested `/* */`                |
| Shell      | `sh`, `bash`, `zsh`                        | `#`                                 |
| YAML       | `yml`, `yaml`                              | `#`                                 |
| C          | `c`, `h`                                   | `//`, `/* */`                       |
| HTML       | `html`, `htm`                              | `<!-- -->`; text between tags is code |
| CSS        | `css`                                      | `/* */`                             |
| Lean       | `lean`                                     | `--`, nested `/- -/` (and `/--`, `/-!`) |
| Objective-C | `m`, `mm`                                 | `//`, `/* */`                       |

A file with no extension is read, and counted if its first line is a `#!`
naming Python (`python`, `python3`, `python3.12`), a POSIX shell (`sh`,
`bash`, `zsh`, `dash`, `ksh`) or Node, by path or through `env`. That covers
the extensionless scripts most repositories keep in `scripts/` or `bin/`.

A line is **blank** if it holds only whitespace, **comment** if it holds only
comment text, and **code** otherwise. A comment marker inside a string is code.
Doc comments (`///`, `//!`, and Lean's `/--` and `/-!`) are comments. Lean's
lines come from its own lexer, which reads interpolated strings such as
`s!"{f "x"}"`, where matching quotes would lose its place. Python docstrings are code, since
they are string literals. A whitespace-only line inside a multi-line string is
still blank. A `#!` line is a comment, as `#` makes it in every language that
uses one.

The total of lines matches `wc -l` for files that end in a newline. A final
line without a newline counts as one more line than `wc -l` reports.

### Which files

By default the files are the ones git lists for each path: every tracked file,
plus every untracked file that `.gitignore` and the other standard ignore files
do not exclude. That is what `git add -A` would commit, so build output and
other ignored files never count. Hidden files that git lists, such as
`.github/workflows/ci.yml`, are counted. A tracked file deleted from the
working tree, a symlink and a submodule are not. The count reads the working
tree, not the index. A file named explicitly that git ignores is skipped.

A path that is not inside a git repository, or a machine without git, falls
back to `--walk`.

`--walk` finds files by walking the directories instead. It skips hidden files
and directories and honours `.gitignore` even outside a git repository, so it
also counts tracked files that `.gitignore` excludes and misses hidden ones.

Either way, files with an unknown extension, files with no extension whose
first line names no supported language, and files with a NUL byte in their
first 8 KB, are not counted.

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
- C and Objective-C: `if`, `for`, `while`, `do`, each `case` with a value (not
  `default`), `@catch`, the ternary operator, `&&`, `||`.
- Lean: `if` (so each `else if`), `unless`, `for`, `while`, `repeat`, `catch`,
  `&&`, `||`, `∧`, `∨`, `<|>`, and each `|` alternative beyond the first of a
  `match`, a `fun` or a definition by pattern matching. A `do` block's
  `let some x := e | fallback` is one. A `termination_by` or `decreasing_by`
  clause is a proof and adds nothing.

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

Get an lcov file for Rust from `cargo-llvm-cov`:

```bash
cargo llvm-cov --locked --lcov --output-path lcov.info
clocrap --crap --lcov lcov.info
```

Functions are found for Rust, Python, Swift, TypeScript, TSX, JavaScript, C,
Objective-C (where a method is named by its selector, such as `-tap:at:`) and
Lean, each by its own analyzer in `Clocrap/`, which reads the file's tokens.
One tokenizer (`Clocrap/Lex.lean`) knows each family's comments, strings and
the code inside strings: template literals' `${…}`, Swift's `\(…)` and
Python's f-string `{…}` are code, so a decision inside one counts.

The analyzers give the answers tree-sitter's grammars give. clocrap used
tree-sitter until it was rewritten in Lean, and the rewrite was checked by
running both versions on fifteen repositories (Lean, Rust, Swift, TypeScript,
JavaScript and Python) and 330 C and Objective-C files, and comparing their
output byte for byte. Where tree-sitter has a quirk that changes a count, the
analyzer copies it: a Swift `if case 1 = x` does not count, a Rust match guard's
`if` does not count, and a Python comment after a function's last statement,
indented as far as its body, is part of the function.

Lean's functions come from its tokens too, since notation and macros make its
grammar open-ended: `def`, `abbrev`, `instance` and `opaque` declarations are
functions, and each helper in a `where` block is one of its own, named
`outer.helper`. Theorems, lemmas and examples are proofs the kernel checks and
never run, so they are not scored, and nor are structures, inductives, classes
and syntax. Other languages have counts but no function list.

### Where the analyzers and tree-sitter differ

Each of these is a file tree-sitter cannot parse, where its error recovery
loses or misplaces functions that the analyzers find:

- Swift: where tree-sitter's Swift grammar fails, as on a `for … where` clause
  that calls `await`, it drops the loop from the count, or the functions after
  the error.
- C++ (in `.h` and `.mm` files): neither reads it. tree-sitter's C and
  Objective-C grammars do not know classes, namespaces or templates, and nor
  does the analyzer, so the two lose different functions.
- Objective-C: a method outside `@implementation`, and a React Native
  `RCT_EXPORT_METHOD(…)` right after `RCT_EXPORT_MODULE()`, which tree-sitter
  starts on a later line.

### Lean coverage

Lean compiles to C, one file per module under `.lake/build/ir/`, with no line
directives back to the `.lean` source. clocrap reads an lcov report of that C
and gives each declaration the C functions that carry its mangled name: its
own, its lambdas, and its `where` helpers' when they are not scored on their
own. A copy of a generic function specialised for a caller
(`<callee>___at___00<caller>_spec__0`, often in the caller's module's C) is
the callee's code, so it goes to the callee; standard-library code
specialised for a caller goes to the caller. `___boxed` wrappers, module
initialisers and `match` splitters (compiled for proofs, never called) are
left out. A declaration's coverage is the share of those functions'
instrumented C lines that ran. A declaration with no C of its own (inlined
everywhere, a type, or run only at compile time) has no coverage, and the
report says how many were left out for that.

The report's call counts (`FNDA:`) settle two more cases. A generic
declaration whose own body was never called is measured by its specialised
copies that were. A declaration Lean may inline into its callers
(`@[inline]`, `@[macro_inline]`, `@[always_inline]`, `@[specialize]`, an
`abbrev`, or a body that is one application of names) whose own C was never
called ran, if at all, inside its callers' C: it is counted apart as inlined,
with no coverage, rather than as untested.

Lean's toolchain ships clang without LLVM's profile runtime, so the build uses
Apple's, through `scripts/lean-cov-cc`:

```bash
find . -path '*/.lake/build/ir/*' -name '*.c.o*' -delete   # Lake does not track LEAN_CC
LEAN_CC=/path/to/clocrap/scripts/lean-cov-cc lake build <test executables>
LLVM_PROFILE_FILE="$PWD/cov/%c%p.profraw" .lake/build/bin/<test>
xcrun llvm-profdata merge -o cov.profdata cov/*.profraw
xcrun llvm-cov export -format=lcov -instr-profile cov.profdata .lake/build/bin/<test> > lcov.info
clocrap --lcov lcov.info
```

`%c` is LLVM's continuous mode: counters go to the file as the program runs,
so a process that is killed, such as an app a test harness stops, keeps its
coverage. Export each test executable's profile on its own and concatenate
the lcov files (clocrap adds the hits up): two executables often hold
different functions under one name, such as each one's `main`.

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

On an Apple M5 Max, counting 100,000 files (50,000 Rust and 50,000 Python,
4.35 million lines) takes about 1.7 seconds, wall clock, with `--threads 4`,
the default. The Rust version took 1.2 seconds on the same tree.

The time goes to the kernel. Plain `cat` over the same files, run in parallel,
has the same curve: real time stops falling at four or so readers, while system
time keeps rising. File opens contend in macOS past that point. So the default
is four workers, and `--threads` changes it.

Against the other two tools, on the same 100,000-file tree (each file with
different content), best of three runs, `--threads 4` for clocrap:

| Tool      | Wall clock | Code lines |
|-----------|-----------:|-----------:|
| clocrap   |     1.66 s |  2,300,000 |
| tokei 15  |     1.29 s |  2,300,000 |
| cloc 2.10 |    18.3 s  |  2,250,000 |

`scripts/bench.py [DIR]` runs the comparison on any directory. cloc skips files
whose contents are identical to an earlier file, so a benchmark tree must have
distinct files, or cloc looks several times faster than it is.

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
lake build clocrap clocrap-test
.lake/build/bin/clocrap-test
```

The tests run the built `clocrap` on small fixture trees, the way a user would,
and check each analyzer on short sources. Lake does not rebuild `clocrap`
before running the tests, so build both.

## License

MIT. See [LICENSE](LICENSE).
