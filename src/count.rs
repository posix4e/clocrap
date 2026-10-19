//! Line classification. One pass over the bytes of a file decides, for every
//! line, whether it is blank, comment or code. Comment and string state carries
//! from line to line, so a `//` inside a string is code and a `/*` that opens
//! on one line stays open until its `*/`.

use crate::lang::{Language, StringSyntax, Syntax};

/// What one line holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LineKind {
    /// Only whitespace.
    Blank,
    /// Only comment text.
    Comment,
    /// Code, possibly with a trailing comment.
    Code,
}

/// Line totals for one file or a sum of files.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LineCounts {
    pub blank: u64,
    pub comment: u64,
    pub code: u64,
}

impl LineCounts {
    /// Every line, of any kind.
    #[must_use]
    pub fn total(&self) -> u64 {
        self.blank + self.comment + self.code
    }

    /// Adds one line of the given kind.
    pub fn record(&mut self, kind: LineKind) {
        match kind {
            LineKind::Blank => self.blank += 1,
            LineKind::Comment => self.comment += 1,
            LineKind::Code => self.code += 1,
        }
    }

    /// Adds another set of totals to this one.
    pub fn add(&mut self, other: &LineCounts) {
        self.blank += other.blank;
        self.comment += other.comment;
        self.code += other.code;
    }
}

/// Where the lexer is when a line begins.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Code,
    /// Inside a block comment, with the nesting depth (1 when not nested).
    Block(u32),
    /// Inside the string at this index in the syntax's `strings`.
    Str(usize),
}

/// Calls `visit` with the 1-based number and kind of every line in `source`.
///
/// A final line without a newline is a line, so the number of lines matches
/// `wc -l` for files that end in a newline and is one more for files that do
/// not. A file that is empty has no lines.
pub fn for_each_line(source: &[u8], syntax: &Syntax, mut visit: impl FnMut(u64, LineKind)) {
    let mut state = State::Code;
    let mut rest = source;
    let mut number = 0;
    while !rest.is_empty() {
        let (line, next) = match rest.iter().position(|&b| b == b'\n') {
            Some(end) => (&rest[..end], &rest[end + 1..]),
            None => (rest, &rest[rest.len()..]),
        };
        number += 1;
        visit(number, classify_line(line, syntax, &mut state));
        rest = next;
    }
}

/// Counts the lines of `source` by kind.
#[must_use]
pub fn count_lines(source: &[u8], language: Language) -> LineCounts {
    let syntax = language.syntax();
    let mut counts = LineCounts::default();
    for_each_line(source, &syntax, |_, kind| counts.record(kind));
    counts
}

fn classify_line(line: &[u8], syntax: &Syntax, state: &mut State) -> LineKind {
    if line.iter().all(u8::is_ascii_whitespace) {
        return LineKind::Blank;
    }
    let mut has_code = false;
    let mut i = 0;
    while i < line.len() {
        match *state {
            State::Block(depth) => {
                let Some(block) = syntax.block else {
                    *state = State::Code;
                    continue;
                };
                let rest = &line[i..];
                if rest.starts_with(block.close) {
                    i += block.close.len();
                    *state = if depth <= 1 {
                        State::Code
                    } else {
                        State::Block(depth - 1)
                    };
                } else if block.nests && rest.starts_with(block.open) {
                    i += block.open.len();
                    *state = State::Block(depth + 1);
                } else {
                    i += 1;
                }
            }
            State::Str(index) => {
                has_code = true;
                let string = syntax.strings[index];
                let rest = &line[i..];
                if string.escapes && rest[0] == b'\\' {
                    i += 2;
                } else if rest.starts_with(string.close) {
                    i += string.close.len();
                    *state = State::Code;
                } else {
                    i += 1;
                }
            }
            State::Code => {
                let rest = &line[i..];
                if rest[0].is_ascii_whitespace() {
                    i += 1;
                    continue;
                }
                if syntax
                    .line_comments
                    .iter()
                    .any(|marker| starts_token(line, i, marker))
                {
                    // The rest of the line is comment.
                    break;
                }
                if let Some(block) = syntax.block
                    && rest.starts_with(block.open)
                {
                    i += block.open.len();
                    *state = State::Block(1);
                    continue;
                }
                has_code = true;
                if syntax.char_literals
                    && rest[0] == b'\''
                    && let Some(len) = char_literal_len(rest)
                {
                    i += len;
                    continue;
                }
                if let Some(index) = syntax
                    .strings
                    .iter()
                    .position(|s| starts_token(line, i, s.open))
                {
                    i += syntax.strings[index].open.len();
                    *state = State::Str(index);
                    continue;
                }
                i += 1;
            }
        }
    }
    close_single_line_string(syntax, state);
    if has_code {
        LineKind::Code
    } else {
        LineKind::Comment
    }
}

/// A string that cannot span lines ends with its line, even if it never closed.
fn close_single_line_string(syntax: &Syntax, state: &mut State) {
    if let State::Str(index) = *state {
        let string: StringSyntax = syntax.strings[index];
        if !string.multiline {
            *state = State::Code;
        }
    }
}

/// Whether `marker` starts at byte `i` of `line` as its own token. A marker
/// that begins with a letter must not follow another identifier character, so
/// `bar"` is not a raw string opener. A `#` comment must follow whitespace or
/// the start of the line, so `$#` in a shell script is not a comment.
fn starts_token(line: &[u8], i: usize, marker: &[u8]) -> bool {
    if !line[i..].starts_with(marker) {
        return false;
    }
    let before = if i == 0 { None } else { Some(line[i - 1]) };
    match marker.first() {
        Some(b'#') => before.is_none_or(|b| b.is_ascii_whitespace()),
        Some(first) if first.is_ascii_alphabetic() => {
            before.is_none_or(|b| !(b.is_ascii_alphanumeric() || b == b'_'))
        }
        _ => true,
    }
}

/// The length of the character literal at the start of `rest`, if it is one.
/// `'a'` and `'\n'` are literals; `'a` followed by anything else is a lifetime.
fn char_literal_len(rest: &[u8]) -> Option<usize> {
    if rest.len() >= 3 && rest[1] == b'\\' {
        let end = rest[2..rest.len().min(12)]
            .iter()
            .position(|&b| b == b'\'')?;
        return Some(2 + end + 1);
    }
    if rest.len() >= 3 && rest[1] != b'\'' && rest[2] == b'\'' {
        return Some(3);
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn counts(language: Language, source: &str) -> LineCounts {
        count_lines(source.as_bytes(), language)
    }

    fn kinds(language: Language, source: &str) -> Vec<LineKind> {
        let mut out = Vec::new();
        for_each_line(source.as_bytes(), &language.syntax(), |_, kind| {
            out.push(kind);
        });
        out
    }

    #[test]
    fn empty_file_has_no_lines() {
        assert_eq!(counts(Language::Rust, "").total(), 0);
    }

    #[test]
    fn final_line_without_newline_counts() {
        // wc -l reports 1 for "a\nb"; the line count here is 2.
        assert_eq!(counts(Language::Rust, "a\nb").total(), 2);
        assert_eq!(counts(Language::Rust, "a\nb\n").total(), 2);
    }

    #[test]
    fn rust_line_and_nested_block_comments() {
        let source = "\
// header
fn main() { // trailing is code
    /* open
       still /* nested */ still
    */
    let x = 1; /* inline */
}

";
        assert_eq!(
            counts(Language::Rust, source),
            LineCounts {
                blank: 1,
                comment: 4,
                code: 3,
            }
        );
    }

    #[test]
    fn rust_block_comment_does_not_nest_in_javascript() {
        let source = "/* a /* b */\nlet x = 1;\n";
        assert_eq!(
            kinds(Language::JavaScript, source),
            [LineKind::Comment, LineKind::Code]
        );
    }

    #[test]
    fn comment_markers_inside_strings_are_code() {
        let source = "let s = \"// not a comment\";\nlet t = \"/* nor this\";\n";
        assert_eq!(
            kinds(Language::Rust, source),
            [LineKind::Code, LineKind::Code]
        );
        assert_eq!(
            kinds(Language::JavaScript, source),
            [LineKind::Code, LineKind::Code]
        );
    }

    #[test]
    fn escaped_quote_does_not_end_a_string() {
        let source = "let s = \"a \\\" // still string\"; // comment\n";
        assert_eq!(kinds(Language::Rust, source), [LineKind::Code]);
    }

    #[test]
    fn rust_raw_string_spans_lines() {
        let source = "let s = r#\"\n// inside\n\"#;\n// after\n";
        assert_eq!(
            kinds(Language::Rust, source),
            [
                LineKind::Code,
                LineKind::Code,
                LineKind::Code,
                LineKind::Comment
            ]
        );
    }

    #[test]
    fn rust_char_literal_quote_does_not_open_a_string() {
        let source = "let q = '\"'; // comment\nfn f<'a>(x: &'a str) {}\n";
        assert_eq!(
            kinds(Language::Rust, source),
            [LineKind::Code, LineKind::Code]
        );
    }

    #[test]
    fn python_triple_quoted_string_is_code() {
        let source = "\"\"\"Docstring\n\nmore\n\"\"\"\n# comment\nx = 1\n";
        assert_eq!(
            kinds(Language::Python, source),
            [
                LineKind::Code,
                LineKind::Blank,
                LineKind::Code,
                LineKind::Code,
                LineKind::Comment,
                LineKind::Code,
            ]
        );
    }

    #[test]
    fn hash_comments_need_a_leading_boundary() {
        let shell = "echo $# ${#arr[@]}\n# real comment\n";
        assert_eq!(
            kinds(Language::Shell, shell),
            [LineKind::Code, LineKind::Comment]
        );
        let yaml = "key: a#b\n";
        assert_eq!(kinds(Language::Yaml, yaml), [LineKind::Code]);
    }

    #[test]
    fn toml_literal_and_basic_strings() {
        let source = "a = 'x # y'\nb = \"z # w\" # real\n";
        assert_eq!(
            kinds(Language::Toml, source),
            [LineKind::Code, LineKind::Code]
        );
    }

    #[test]
    fn whitespace_lines_are_blank_even_inside_a_block_comment() {
        let source = "/*\n   \n*/\n";
        assert_eq!(
            counts(Language::Swift, source),
            LineCounts {
                blank: 1,
                comment: 2,
                code: 0,
            }
        );
    }

    #[test]
    fn markdown_has_no_comments() {
        assert_eq!(
            counts(Language::Markdown, "# Title\n\ntext\n"),
            LineCounts {
                blank: 1,
                comment: 0,
                code: 2,
            }
        );
    }

    #[test]
    fn json_has_no_comments() {
        assert_eq!(
            counts(Language::Json, "{\n  \"a\": \"//x\"\n}\n").comment,
            0
        );
    }

    #[test]
    fn crlf_lines_classify_like_lf_lines() {
        assert_eq!(
            counts(Language::Rust, "a\r\n\r\n// c\r\n"),
            LineCounts {
                blank: 1,
                comment: 1,
                code: 1,
            }
        );
    }

    #[test]
    fn unclosed_single_line_string_ends_at_end_of_line() {
        let source = "let s = \"open\nlet t = 2; // c\n";
        assert_eq!(
            kinds(Language::Rust, source),
            [LineKind::Code, LineKind::Code]
        );
        assert_eq!(counts(Language::Rust, source).comment, 0);
    }
}
