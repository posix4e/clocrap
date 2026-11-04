//! Functions in Lean 4 source, found from tokens rather than a grammar.
//!
//! Lean's syntax is extensible (notation, macros, do-notation), so a fixed
//! grammar misreads real files. The shape clocrap needs is regular, though:
//!
//! - A declaration is a command. It starts with attributes, modifiers or a
//!   keyword as the first token of a line, at column 0 or at the column of the
//!   first declaration inside a `mutual` block, and runs until the next command.
//! - `def`, `abbrev`, `instance` and `opaque` declarations are functions.
//!   Theorems, lemmas and examples are proofs: the kernel checks them and they
//!   never run, so they are not scored. Nor are structures, inductives,
//!   classes, macros and syntax.
//! - Each helper in a definition's `where` block is a function of its own,
//!   named `outer.helper` as Lean names it. A `where` with no `:=` before it is
//!   structure-instance notation, and its fields belong to the definition.
//!
//! A function's complexity is 1 plus one for each `if` (so each `else if`),
//! `unless`, `for`, `while`, `repeat`, `catch`, `&&`, `||`, `∧`, `∨`, `<|>` and
//! `|`, less one for each `match`, each `fun` that matches on alternatives, and
//! a definition by pattern matching. So n arms add n − 1, and a `do` block's
//! `let some x := e | fallback` adds one. A `termination_by` or `decreasing_by`
//! clause is a proof, and adds nothing.

use crate::complexity::{Function, Symbol};
use std::fmt::Write as _;

use crate::count::LineKind;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Ident,
    Symbol,
    Literal,
}

#[derive(Debug, Clone, Copy)]
struct Token<'a> {
    kind: Kind,
    text: &'a str,
    line: u64,
    /// The line the token ends on: a string can span lines.
    end_line: u64,
    column: usize,
    first_on_line: bool,
}

impl Token<'_> {
    fn is(&self, text: &str) -> bool {
        self.kind != Kind::Literal && self.text == text
    }
}

/// Symbols longer than one character that the analysis needs to tell apart.
/// Longest first, so `<|>` is not read as `<|` and `>`.
const SYMBOLS: &[&str] = &[
    "<|>", "|||", "&&&", "|>.", "&&", "||", "|>", "<|", ":=", "=>", "@[",
];

struct Lexer<'a> {
    source: &'a str,
    bytes: &'a [u8],
    i: usize,
    line: u64,
    line_start: usize,
    line_has_token: bool,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a str) -> Self {
        Lexer {
            source,
            bytes: source.as_bytes(),
            i: 0,
            line: 1,
            line_start: 0,
            line_has_token: false,
        }
    }

    fn at(&self, text: &[u8]) -> bool {
        self.bytes[self.i..].starts_with(text)
    }

    /// Steps over one byte, keeping track of lines.
    fn bump(&mut self) {
        if self.bytes[self.i] == b'\n' {
            self.line += 1;
            self.line_start = self.i + 1;
            self.line_has_token = false;
        }
        self.i += 1;
    }

    fn char_at(&self, i: usize) -> Option<char> {
        self.source.get(i..)?.chars().next()
    }

    fn tokens(mut self) -> Vec<Token<'a>> {
        let mut tokens = Vec::new();
        while self.i < self.bytes.len() {
            let b = self.bytes[self.i];
            if b.is_ascii_whitespace() {
                self.bump();
                continue;
            }
            if self.at(b"--") {
                while self.i < self.bytes.len() && self.bytes[self.i] != b'\n' {
                    self.i += 1;
                }
                continue;
            }
            if self.at(b"/-") {
                self.skip_block_comment();
                continue;
            }
            let (start, line, column) = (self.i, self.line, self.i - self.line_start);
            let first_on_line = !self.line_has_token;
            let kind = self.token();
            self.line_has_token = true;
            tokens.push(Token {
                kind,
                text: &self.source[start..self.i],
                line,
                end_line: self.line,
                column,
                first_on_line,
            });
        }
        tokens
    }

    fn skip_block_comment(&mut self) {
        let mut depth = 0_u32;
        while self.i < self.bytes.len() {
            if self.at(b"/-") {
                depth += 1;
                self.i += 2;
            } else if self.at(b"-/") {
                self.i += 2;
                depth -= 1;
                if depth == 0 {
                    return;
                }
            } else {
                self.bump();
            }
        }
    }

    /// Reads one token starting at a non-blank, non-comment byte.
    fn token(&mut self) -> Kind {
        let b = self.bytes[self.i];
        if b == b'"' {
            self.i += 1;
            self.skip_string(false);
            return Kind::Literal;
        }
        if b == b'r' && self.skip_raw_string() {
            return Kind::Literal;
        }
        if b == b'\'' && self.skip_char_literal() {
            return Kind::Literal;
        }
        if b.is_ascii_digit() {
            while self.i < self.bytes.len()
                && (self.bytes[self.i].is_ascii_alphanumeric()
                    || self.bytes[self.i] == b'_'
                    || (self.bytes[self.i] == b'.'
                        && self.bytes.get(self.i + 1).is_some_and(u8::is_ascii_digit)))
            {
                self.i += 1;
            }
            return Kind::Literal;
        }
        let c = self.char_at(self.i).unwrap_or('\u{fffd}');
        if is_id_start(c) || c == '«' {
            self.skip_ident();
            // `s!"…{x}…"`, `m!"…"`, `f!"…"`: an interpolated string.
            if self.source[..self.i].ends_with('!') && self.at(b"\"") {
                self.i += 1;
                self.skip_string(true);
                return Kind::Literal;
            }
            return Kind::Ident;
        }
        if let Some(symbol) = SYMBOLS
            .iter()
            .find(|s| self.bytes[self.i..].starts_with(s.as_bytes()))
        {
            self.i += symbol.len();
        } else {
            self.i += c.len_utf8();
        }
        Kind::Symbol
    }

    /// Skips a string body up to and including its closing quote. In an
    /// interpolated string, `{…}` holds code, which may hold strings itself.
    fn skip_string(&mut self, interpolated: bool) {
        let mut depth = 0_u32;
        while self.i < self.bytes.len() {
            match self.bytes[self.i] {
                b'\\' if depth == 0 => {
                    self.i += 1;
                    if self.i < self.bytes.len() {
                        self.bump();
                    }
                }
                b'"' if depth == 0 => {
                    self.i += 1;
                    return;
                }
                b'"' => {
                    self.i += 1;
                    self.skip_string(false);
                }
                b'{' if interpolated => {
                    depth += 1;
                    self.i += 1;
                }
                b'}' if interpolated && depth > 0 => {
                    depth -= 1;
                    self.i += 1;
                }
                _ => self.bump(),
            }
        }
    }

    /// `r"…"` or `r#"…"#`, with any number of `#`. Returns false, consuming
    /// nothing, when the `r` starts a name instead.
    fn skip_raw_string(&mut self) -> bool {
        let hashes = self.bytes[self.i + 1..]
            .iter()
            .take_while(|&&b| b == b'#')
            .count();
        if self.bytes.get(self.i + 1 + hashes) != Some(&b'"') {
            return false;
        }
        self.i += hashes + 2;
        let close: Vec<u8> = std::iter::once(b'"')
            .chain(std::iter::repeat_n(b'#', hashes))
            .collect();
        while self.i < self.bytes.len() {
            if self.at(&close) {
                self.i += close.len();
                return true;
            }
            self.bump();
        }
        true
    }

    /// `'a'`, `'\n'`, `'\x41'`, `'\u{1F600}'`. A prime that ends a name is
    /// part of the name, so it never gets here.
    fn skip_char_literal(&mut self) -> bool {
        let rest = &self.bytes[self.i..];
        if rest.get(1) == Some(&b'\\') {
            if let Some(end) = rest.iter().take(14).skip(3).position(|&b| b == b'\'') {
                self.i += end + 4;
                return true;
            }
            return false;
        }
        let Some(c) = self.char_at(self.i + 1) else {
            return false;
        };
        if c != '\'' && c != '\n' && rest.get(1 + c.len_utf8()) == Some(&b'\'') {
            self.i += c.len_utf8() + 2;
            return true;
        }
        false
    }

    /// A name: components joined by dots, each plain or in `«»`.
    fn skip_ident(&mut self) {
        loop {
            if self.at("«".as_bytes()) {
                match self.source[self.i..].find('»') {
                    Some(end) => self.i += end + '»'.len_utf8(),
                    None => self.i = self.bytes.len(),
                }
            } else {
                while let Some(c) = self.char_at(self.i) {
                    if !is_id_rest(c) {
                        break;
                    }
                    self.i += c.len_utf8();
                }
            }
            let continues = self.at(b".")
                && self
                    .char_at(self.i + 1)
                    .is_some_and(|c| is_id_start(c) || c == '«');
            if !continues {
                return;
            }
            self.i += 1;
        }
    }
}

/// Lean's `isLetterLike`: Greek but λ, Π and Σ, Coptic, extended Greek, the
/// letter-like symbols block and the mathematical alphabets.
fn is_letter_like(c: char) -> bool {
    let v = u32::from(c);
    (0x3b1..=0x3c9).contains(&v) && v != 0x3bb
        || (0x391..=0x3a9).contains(&v) && v != 0x3a0 && v != 0x3a3
        || (0x3ca..=0x3fb).contains(&v)
        || (0x1f00..=0x1ffe).contains(&v)
        || (0x2100..=0x214f).contains(&v)
        || (0x1d49c..=0x1d59f).contains(&v)
}

fn is_subscript(c: char) -> bool {
    let v = u32::from(c);
    (0x2080..=0x2089).contains(&v)
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
}

fn is_id_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || is_letter_like(c)
}

fn is_id_rest(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(c, '_' | '\'' | '!' | '?')
        || is_letter_like(c)
        || is_subscript(c)
}

/// Words that start a command when they open a line at the command column.
const COMMANDS: &[&str] = &[
    "def",
    "theorem",
    "lemma",
    "abbrev",
    "instance",
    "example",
    "opaque",
    "axiom",
    "structure",
    "inductive",
    "coinductive",
    "class",
    "namespace",
    "section",
    "end",
    "open",
    "variable",
    "universe",
    "set_option",
    "attribute",
    "export",
    "macro",
    "macro_rules",
    "syntax",
    "elab",
    "elab_rules",
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "declare_syntax_cat",
    "initialize",
    "builtin_initialize",
    "mutual",
    "deriving",
    "import",
    "module",
    "run_cmd",
    "run_elab",
    "run_meta",
    "add_decl_doc",
    "register_simp_attr",
    "register_option",
    "omit",
    "include",
    "@[",
    "#",
];

/// Modifiers that may come before a declaration keyword.
const MODIFIERS: &[&str] = &[
    "private",
    "protected",
    "public",
    "noncomputable",
    "partial",
    "unsafe",
    "nonrec",
    "meta",
    "scoped",
    "local",
];

fn starts_command(token: &Token) -> bool {
    token.kind != Kind::Literal
        && (COMMANDS.contains(&token.text) || MODIFIERS.contains(&token.text))
}

/// The kind of every line of a Lean source file, from its tokens: a line a
/// token touches is code (a string that spans lines makes each of its lines
/// code), any other line that is not blank holds only comment text. This reads
/// interpolated strings such as `s!"{f "x"}"` right, which a quote-matching
/// classifier cannot. Returns `None` for a file that is not UTF-8.
#[must_use]
pub fn line_kinds(source: &[u8]) -> Option<Vec<LineKind>> {
    let text = std::str::from_utf8(source).ok()?;
    let lines: Vec<&[u8]> = if source.is_empty() {
        Vec::new()
    } else {
        source
            .strip_suffix(b"\n")
            .unwrap_or(source)
            .split(|&b| b == b'\n')
            .collect()
    };
    let mut code = vec![false; lines.len()];
    for token in Lexer::new(text).tokens() {
        for line in token.line..=token.end_line {
            if let Some(flag) = usize::try_from(line - 1).ok().and_then(|i| code.get_mut(i)) {
                *flag = true;
            }
        }
    }
    Some(
        lines
            .iter()
            .zip(code)
            .map(|(line, code)| {
                if line.iter().all(u8::is_ascii_whitespace) {
                    LineKind::Blank
                } else if code {
                    LineKind::Code
                } else {
                    LineKind::Comment
                }
            })
            .collect(),
    )
}

/// The functions in a Lean source file, in source order. A file that is not
/// UTF-8 has none.
#[must_use]
pub fn functions(source: &[u8]) -> Vec<Function> {
    let Ok(source) = std::str::from_utf8(source) else {
        return Vec::new();
    };
    let tokens = Lexer::new(source).tokens();
    let mut functions = Vec::new();
    let mut namespaces: Vec<Vec<String>> = Vec::new();
    // `Some(None)` inside a `mutual` block before its first declaration.
    let mut mutual: Option<Option<usize>> = None;
    let mut starts = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        if !token.first_on_line || !starts_command(token) {
            continue;
        }
        let at_column = match mutual {
            Some(Some(column)) => token.column == 0 || token.column == column,
            Some(None) => {
                mutual = Some(Some(token.column));
                true
            }
            None => token.column == 0,
        };
        if !at_column {
            continue;
        }
        // Attributes or modifiers on lines of their own belong to the
        // declaration that follows them.
        let pending = starts
            .last()
            .is_some_and(|&last| header(&tokens[last..index]).1.is_none());
        if !pending {
            starts.push(index);
        }
        // A `mutual` block's own column is fixed by its first declaration.
        if token.is("mutual") {
            mutual = Some(None);
        } else if token.is("end") && token.column == 0 {
            mutual = None;
        }
    }
    let mut in_mutual = false;
    for (n, &start) in starts.iter().enumerate() {
        let end = starts.get(n + 1).copied().unwrap_or(tokens.len());
        let command = &tokens[start..end];
        let (private, keyword) = header(command);
        let Some(keyword) = keyword else { continue };
        let rest = &command[keyword + 1..];
        match command[keyword].text {
            "namespace" => {
                if let Some(name) = rest.first() {
                    namespaces.push(components(name.text));
                }
            }
            "section" => namespaces.push(Vec::new()),
            "mutual" => in_mutual = true,
            "end" if in_mutual => in_mutual = false,
            "end" => {
                namespaces.pop();
            }
            "def" | "abbrev" | "opaque" | "instance" => {
                let scope: Vec<String> = namespaces.iter().flatten().cloned().collect();
                declaration(command, keyword, private, &scope, &mut functions);
            }
            _ => {}
        }
    }
    functions.sort_by_key(|f| (f.start_line, f.end_line));
    functions
}

/// The index of the command's keyword, after its attributes and modifiers,
/// and whether it is `private`.
fn header(command: &[Token]) -> (bool, Option<usize>) {
    let mut private = false;
    let mut i = 0;
    while i < command.len() {
        let token = &command[i];
        if token.is("@[") {
            i = matching_bracket(command, i) + 1;
        } else if MODIFIERS.contains(&token.text) && token.kind == Kind::Ident {
            private |= token.text == "private";
            i += 1;
        } else {
            return (private, Some(i));
        }
    }
    (private, None)
}

/// The index of the `]` that closes the `@[` or `[` at `open`.
fn matching_bracket(tokens: &[Token], open: usize) -> usize {
    let mut depth = 0_i32;
    for (i, token) in tokens.iter().enumerate().skip(open) {
        if token.is("@[") || token.is("[") {
            depth += 1;
        } else if token.is("]") {
            depth -= 1;
            if depth == 0 {
                return i;
            }
        }
    }
    tokens.len()
}

fn opens(token: &Token) -> bool {
    token.kind == Kind::Symbol && matches!(token.text, "(" | "[" | "{" | "⟨" | "@[" | "⦃")
}

fn closes(token: &Token) -> bool {
    token.kind == Kind::Symbol && matches!(token.text, ")" | "]" | "}" | "⟩" | "⦄")
}

/// The index of the first token at bracket depth 0 that is one of `texts`.
fn first_at_top(tokens: &[Token], texts: &[&str]) -> Option<usize> {
    let mut depth = 0_i32;
    for (i, token) in tokens.iter().enumerate() {
        if depth == 0 && token.kind != Kind::Literal && texts.contains(&token.text) {
            return Some(i);
        }
        if opens(token) {
            depth += 1;
        } else if closes(token) {
            depth -= 1;
        }
    }
    None
}

/// A `def`, `abbrev`, `opaque` or `instance`, with its `where` helpers.
fn declaration(
    command: &[Token],
    keyword: usize,
    private: bool,
    scope: &[String],
    out: &mut Vec<Function>,
) {
    let mut after = keyword + 1;
    // `instance (priority := low) name : …`
    if command[keyword].text == "instance"
        && command.get(after).is_some_and(|t| t.is("("))
        && command.get(after + 1).is_some_and(|t| t.is("priority"))
    {
        let mut depth = 0;
        while after < command.len() {
            if opens(&command[after]) {
                depth += 1;
            } else if closes(&command[after]) {
                depth -= 1;
                if depth == 0 {
                    after += 1;
                    break;
                }
            }
            after += 1;
        }
    }
    let named = command.get(after).filter(|t| t.kind == Kind::Ident);
    let (name, symbol_name) = match named {
        Some(token) => (token.text.to_string(), qualified(scope, token.text)),
        None if command[keyword].text == "instance" => anonymous_instance(&command[after..], scope),
        None => return,
    };
    let body = &command[after..];
    // `opaque f : T` with no body has no code of its own.
    if command[keyword].text == "opaque" && first_at_top(body, &[":="]).is_none() {
        return;
    }
    // Helpers follow a `where` that comes after the body. A `where` with no
    // `:=` or `|` before it is structure-instance notation, part of the body.
    let split = (command[keyword].text != "instance")
        .then(|| first_at_top(body, &[":=", "|", "where"]))
        .flatten()
        .filter(|&i| !body[i].is("where"))
        .and_then(|_| first_at_top(body, &["where"]));
    let own = &command[..after + split.unwrap_or(body.len())];
    let equations = first_at_top(body, &[":=", "|", "where"]).is_some_and(|i| body[i].is("|"));
    out.push(function(
        name.clone(),
        own,
        equations,
        symbol_name.clone(),
        private,
    ));
    if let Some(split) = split {
        helpers(&body[split + 1..], &name, &symbol_name, private, out);
    }
}

/// The helpers in a `where` block: each starts at the column of the first.
fn helpers(
    tokens: &[Token],
    outer: &str,
    outer_symbol: &str,
    private: bool,
    out: &mut Vec<Function>,
) {
    let Some(column) = tokens.first().map(|t| t.column) else {
        return;
    };
    // A helper's own `termination_by` may sit at the helpers' column.
    let starts_helper = |i: usize, t: &Token| {
        i == 0
            || (t.first_on_line
                && t.column == column
                && !t.is("|")
                && !t.is("termination_by")
                && !t.is("decreasing_by")
                && !closes(t))
    };
    let starts: Vec<usize> = tokens
        .iter()
        .enumerate()
        .filter(|&(i, t)| starts_helper(i, t))
        .map(|(i, _)| i)
        .collect();
    for (n, &start) in starts.iter().enumerate() {
        let end = starts.get(n + 1).copied().unwrap_or(tokens.len());
        let helper = &tokens[start..end];
        let (_, Some(at)) = header(helper) else {
            continue;
        };
        let token = &helper[at];
        if token.kind != Kind::Ident {
            continue;
        }
        let rest = &helper[at + 1..];
        let equations = first_at_top(rest, &[":=", "|"]).is_some_and(|i| rest[i].is("|"));
        out.push(function(
            format!("{outer}.{}", token.text),
            helper,
            equations,
            format!("{outer_symbol}.{}", token.text),
            private,
        ));
    }
}

fn function(
    name: String,
    tokens: &[Token],
    equations: bool,
    symbol: String,
    private: bool,
) -> Function {
    let start_line = tokens.first().map_or(1, |t| t.line);
    let end_line = tokens
        .iter()
        .map(|t| t.end_line)
        .max()
        .unwrap_or(start_line);
    let complexity = complexity(tokens) - i64::from(equations);
    Function {
        name,
        start_line,
        end_line,
        complexity: u32::try_from(complexity.max(1)).unwrap_or(u32::MAX),
        symbol: Some(Symbol {
            name: symbol,
            private,
        }),
    }
}

/// 1 plus the decision points in `tokens`, before any proof clause.
fn complexity(tokens: &[Token]) -> i64 {
    let mut total = 1;
    for (i, token) in tokens.iter().enumerate() {
        if token.kind == Kind::Literal {
            continue;
        }
        total += match token.text {
            "termination_by" | "decreasing_by" => break,
            "if" | "unless" | "for" | "while" | "repeat" | "catch" if token.kind == Kind::Ident => {
                1
            }
            "&&" | "||" | "∧" | "∨" | "<|>" | "|" if token.kind == Kind::Symbol => 1,
            "match" if token.kind == Kind::Ident => -1,
            "fun" | "λ" if tokens.get(i + 1).is_some_and(|t| t.is("|")) => -1,
            _ => 0,
        };
    }
    total
}

/// The full name of a declaration written as `written` inside `scope`.
fn qualified(scope: &[String], written: &str) -> String {
    if let Some(root) = written.strip_prefix("_root_.") {
        return root.to_string();
    }
    let mut parts: Vec<String> = scope.to_vec();
    parts.extend(components(written));
    // A component with a dot in it keeps its `«»`, so it stays one component.
    parts
        .iter()
        .map(|part| {
            if part.contains('.') {
                format!("«{part}»")
            } else {
                part.clone()
            }
        })
        .collect::<Vec<_>>()
        .join(".")
}

/// The name Lean gives an instance that has none: `inst` and the type's
/// constants, as `instance : ToJson Foo` becomes `instToJsonFoo`. Only the
/// capitalised names count, since lower-case ones are usually variables.
fn anonymous_instance(tokens: &[Token], scope: &[String]) -> (String, String) {
    let ty = first_at_top(tokens, &[":"]).map_or(&tokens[..0], |i| &tokens[i + 1..]);
    let ty = &ty[..first_at_top(ty, &[":=", "where", "|"]).unwrap_or(ty.len())];
    let mut generated = String::from("inst");
    for token in ty.iter().filter(|t| t.kind == Kind::Ident) {
        let last = components(token.text).pop().unwrap_or_default();
        if last.starts_with(|c: char| c.is_ascii_uppercase()) {
            generated.push_str(&last);
        }
    }
    let shown: Vec<&str> = ty.iter().map(|t| t.text).collect();
    let shown = shown
        .join(" ")
        .replace("( ", "(")
        .replace(" )", ")")
        .replace("[ ", "[")
        .replace(" ]", "]");
    let mut name = format!("instance {shown}");
    if name.chars().count() > 48 {
        name = name.chars().take(47).collect::<String>() + "…";
    }
    (name, qualified(scope, &generated))
}

/// The components of a dotted name, with `«»` removed.
fn components(name: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut quoted = false;
    for c in name.chars() {
        match c {
            '«' => quoted = true,
            '»' => quoted = false,
            '.' if !quoted => parts.push(std::mem::take(&mut current)),
            _ => current.push(c),
        }
    }
    parts.push(current);
    parts
}

/// Lean's mangling of a name into a C identifier: components joined by `_`,
/// `_` doubled, and any other character that is not an ASCII letter or digit
/// written as `_xHH`, `_uHHHH` or `_UHHHHHHHH`, with `00` before a component
/// that starts with one.
#[must_use]
pub fn mangle(name: &str) -> String {
    let mut out = String::new();
    for (n, part) in components(name).iter().enumerate() {
        if n > 0 {
            out.push('_');
        }
        // A component that would start with an escape is marked with `00`.
        if part
            .chars()
            .next()
            .is_some_and(|c| !c.is_ascii_alphanumeric() && c != '_')
        {
            out.push_str("00");
        }
        for c in part.chars() {
            let v = u32::from(c);
            match c {
                _ if c.is_ascii_alphanumeric() => out.push(c),
                '_' => out.push_str("__"),
                _ if v < 0x100 => {
                    let _ = write!(out, "_x{v:02x}");
                }
                _ if v < 0x1_0000 => {
                    let _ = write!(out, "_u{v:04x}");
                }
                _ => {
                    let _ = write!(out, "_U{v:08x}");
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn found(source: &str) -> Vec<(String, u32)> {
        functions(source.as_bytes())
            .into_iter()
            .map(|f| (f.name, f.complexity))
            .collect()
    }

    fn symbols(source: &str) -> Vec<(String, bool)> {
        functions(source.as_bytes())
            .into_iter()
            .map(|f| {
                let s = f.symbol.unwrap();
                (s.name, s.private)
            })
            .collect()
    }

    #[test]
    fn straight_line_definition_has_complexity_one() {
        assert_eq!(found("def f (n : Nat) : Nat := n + 1\n"), [("f".into(), 1)]);
    }

    #[test]
    fn decisions_add_one_each() {
        // 1 base, `if` 1, `else if` 1, `&&` 1, `for` 1, `||` 1, `while` 1, `catch` 1, `<|>` 1.
        let source = "\
def f (a b : Bool) (n : Nat) : IO Nat := do
  if a then
    pure 1
  else if b && n > 0 then
    pure 2
  for _ in [0:n] do
    if a || b then pure () else pure ()
  while false do pure ()
  try pure () catch _ => pure ()
  let x := none <|> some 1
  pure 0
";
        assert_eq!(found(source), [("f".into(), 10)]);
    }

    #[test]
    fn match_counts_arms_minus_one() {
        let source = "\
def f (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 2
  | _ => 3
";
        assert_eq!(found(source), [("f".into(), 3)]);
    }

    #[test]
    fn definitions_by_pattern_matching_and_matching_lambdas() {
        let source = "\
def f : Nat → Nat
  | 0 => 1
  | 1 => 2
  | _ => 3

def g (xs : List (Option Nat)) : List Nat :=
  xs.map fun
    | some x => x
    | none => 0
";
        assert_eq!(found(source), [("f".into(), 3), ("g".into(), 2)]);
    }

    #[test]
    fn a_do_let_with_a_fallback_is_one_decision() {
        let source = "\
def f (o : Option Nat) : IO Nat := do
  let some x := o | return 0
  return x
";
        assert_eq!(found(source), [("f".into(), 2)]);
    }

    #[test]
    fn keywords_in_comments_and_strings_do_not_count() {
        let source = "\
/-- if this were code, `match` and `for` -/
def f (s : String) : String :=
  -- if not
  /- nested /- if -/ for -/
  s ++ \"if || && for\" ++ s!\"{if true then \"a\" else \"b\"} for\" ++ r#\"if\"#
";
        // The `if` inside the interpolation is code, but the whole string is
        // one token, so it is not counted: interpolations rarely branch.
        assert_eq!(found(source), [("f".into(), 1)]);
    }

    #[test]
    fn where_helpers_are_their_own_functions() {
        let source = "\
namespace Cov
def total (xs : List Nat) : Nat := go xs 0
where
  go : List Nat → Nat → Nat
    | [], acc => acc
    | x :: rest, acc => go rest (acc + x)
  @[inline] twice (n : Nat) : Nat := if n > 0 then n * 2 else 0
end Cov
";
        assert_eq!(
            found(source),
            [
                ("total".into(), 1),
                ("total.go".into(), 2),
                ("total.twice".into(), 2)
            ]
        );
        assert_eq!(
            symbols(source),
            [
                ("Cov.total".into(), false),
                ("Cov.total.go".into(), false),
                ("Cov.total.twice".into(), false)
            ]
        );
    }

    #[test]
    fn structure_instance_where_is_part_of_the_definition() {
        let source = "\
def config : Config where
  a := if b then 1 else 2
  c := 3
";
        assert_eq!(found(source), [("config".into(), 2)]);
    }

    #[test]
    fn proofs_types_and_syntax_are_not_functions() {
        let source = "\
theorem t : 1 = 1 := by
  if h : True then rfl else rfl
example : 2 = 2 := rfl
structure P where
  a : Nat
  deriving Repr
inductive T | a | b
macro \"x\" : term => `(1)
def real (n : Nat) : Nat := if n = 0 then 1 else n
";
        assert_eq!(found(source), [("real".into(), 2)]);
    }

    #[test]
    fn termination_proofs_add_nothing() {
        let source = "\
def f (n : Nat) : Nat := if n = 0 then 0 else f (n - 1)
termination_by n
decreasing_by
  all_goals (if h : n = 0 then omega else omega)
";
        assert_eq!(found(source), [("f".into(), 2)]);
    }

    #[test]
    fn namespaces_sections_private_and_root() {
        let source = "\
namespace A.B
private def p := 1
section S
def q := 2
end S
def _root_.r := 3
@[simp] protected def A.s := 4
end A.B
def t := 5
";
        assert_eq!(
            symbols(source),
            [
                ("A.B.p".into(), true),
                ("A.B.q".into(), false),
                ("r".into(), false),
                ("A.B.A.s".into(), false),
                ("t".into(), false)
            ]
        );
    }

    #[test]
    fn mutual_blocks_with_indented_declarations() {
        let source = "\
mutual
  private partial def a (n : Nat) : Nat := if n = 0 then 0 else b (n - 1)
  private partial def b (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | k + 1 => a k
end
def c := 1
";
        assert_eq!(
            found(source),
            [("a".into(), 2), ("b".into(), 2), ("c".into(), 1)]
        );
    }

    #[test]
    fn instances_named_and_anonymous() {
        let source = "\
namespace N
instance : ToString P := ⟨fun p => if p.a then \"y\" else \"n\"⟩
instance named : Inhabited P := ⟨⟨0⟩⟩
instance (priority := low) [ToJson α] : ToJson (Array α) where
  toJson xs := if xs.isEmpty then .null else .arr (xs.map toJson)
end N
";
        assert_eq!(
            found(source),
            [
                ("instance ToString P".into(), 2),
                ("named".into(), 1),
                ("instance ToJson (Array α)".into(), 2)
            ]
        );
        assert_eq!(
            symbols(source),
            [
                ("N.instToStringP".into(), false),
                ("N.named".into(), false),
                ("N.instToJsonArray".into(), false)
            ]
        );
    }

    #[test]
    fn spans_cover_attributes_and_multiline_strings() {
        let source = "\
/-- doc -/
@[inline]
def f : String := \"a
b\"

def g := 1
";
        let functions = functions(source.as_bytes());
        assert_eq!((functions[0].start_line, functions[0].end_line), (2, 4));
        assert_eq!((functions[1].start_line, functions[1].end_line), (6, 6));
    }

    #[test]
    fn names_with_primes_bangs_and_guillemets() {
        let source = "\
def f' (x' : Nat) : Nat := x' + 'a'.toNat
def get! (xs : Array Nat) : Nat := xs[0]!
def «weird name» := 1
";
        assert_eq!(
            found(source),
            [
                ("f'".into(), 1),
                ("get!".into(), 1),
                ("«weird name»".into(), 1)
            ]
        );
    }

    #[test]
    fn line_kinds_read_nested_interpolation() {
        use LineKind::{Blank, Code, Comment};
        // A quote-matching classifier leaves the last string open after the
        // first line, and takes the comment below for string text.
        let source = "\
def f (k : Option String) := s!\"marked {(k.map fun k => s!\"\\\"{k}\\\"\").getD \"none\"})\"
-- a comment
/- a block
   comment -/

def g := \"two
  lines\" -- trailing
";
        assert_eq!(
            line_kinds(source.as_bytes()).unwrap(),
            [Code, Comment, Comment, Comment, Blank, Code, Code]
        );
        assert_eq!(line_kinds(b"").unwrap(), []);
        assert_eq!(line_kinds(b"def x := 1").unwrap(), [Code]);
    }

    #[test]
    fn mangling_matches_lean() {
        // Names from the C that Lean 4.35 emits.
        assert_eq!(mangle("My_ns.my_fun"), "My__ns_my__fun");
        assert_eq!(mangle("My_ns.«weird name»"), "My__ns_weird_x20name");
        assert_eq!(mangle("My_ns._under"), "My__ns___under");
        assert_eq!(mangle("Std.Range.forIn'"), "Std_Range_forIn_x27");
        assert_eq!(mangle("α.β"), "00_u03b1_00_u03b2");
        assert_eq!(mangle("ℕat"), "00_u2115at");
        assert_eq!(mangle("Foo.«a.b»"), "Foo_a_x2eb");
        assert_eq!(
            mangle(&qualified(&["N".into()], "Foo.«a.b»")),
            "N_Foo_a_x2eb"
        );
        assert_eq!(mangle("x2._y3"), "x2___y3");
    }
}
