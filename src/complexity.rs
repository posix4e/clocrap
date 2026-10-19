//! Cyclomatic complexity per function, from a tree-sitter parse.
//!
//! A function's complexity is 1 plus one for each decision point in its body:
//! `if`, `while`, `for`, `loop`, each `match` arm beyond the first, `&&`, `||`,
//! `??`, `catch`, `except`, `case`, and the ternary operator. Closures and
//! lambdas are part of the function they sit in. A nested function is scored on
//! its own and does not add to the function that contains it.
//!
//! The `?` operator, `try` and `else` are not decision points.

use std::path::Path;

use tree_sitter::{Node, Parser};

use crate::lang::Language;

/// One function found in a source file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub name: String,
    /// 1-based first line of the function.
    pub start_line: u64,
    /// 1-based last line of the function.
    pub end_line: u64,
    pub complexity: u32,
}

/// The grammars clocrap can parse. TSX is its own grammar, so `.tsx` files
/// need it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Grammar {
    Rust,
    Python,
    Swift,
    TypeScript,
    Tsx,
    JavaScript,
}

impl Grammar {
    fn for_file(language: Language, extension: &str) -> Option<Grammar> {
        Some(match language {
            Language::Rust => Grammar::Rust,
            Language::Python => Grammar::Python,
            Language::Swift => Grammar::Swift,
            Language::TypeScript if extension.eq_ignore_ascii_case("tsx") => Grammar::Tsx,
            Language::TypeScript => Grammar::TypeScript,
            Language::JavaScript => Grammar::JavaScript,
            _ => return None,
        })
    }

    fn ts_language(self) -> tree_sitter::Language {
        match self {
            Grammar::Rust => tree_sitter_rust::LANGUAGE.into(),
            Grammar::Python => tree_sitter_python::LANGUAGE.into(),
            Grammar::Swift => tree_sitter_swift::LANGUAGE.into(),
            Grammar::TypeScript => tree_sitter_typescript::LANGUAGE_TYPESCRIPT.into(),
            Grammar::Tsx => tree_sitter_typescript::LANGUAGE_TSX.into(),
            Grammar::JavaScript => tree_sitter_javascript::LANGUAGE.into(),
        }
    }

    /// Node kinds that introduce a function.
    fn is_function(self, kind: &str) -> bool {
        match self {
            Grammar::Rust => kind == "function_item",
            Grammar::Python => kind == "function_definition",
            Grammar::Swift => matches!(kind, "function_declaration" | "init_declaration"),
            Grammar::TypeScript | Grammar::Tsx | Grammar::JavaScript => matches!(
                kind,
                "function_declaration"
                    | "generator_function_declaration"
                    | "function_expression"
                    | "function"
                    | "generator_function"
                    | "method_definition"
                    | "arrow_function"
            ),
        }
    }

    /// How much one node adds to the complexity of the function around it.
    /// Negative weights cancel the extra arm of a `match` or `switch`.
    fn weight(self, node: Node, source: &[u8]) -> i64 {
        let kind = node.kind();
        match self {
            Grammar::Rust => match kind {
                "if_expression" | "while_expression" | "for_expression" | "loop_expression"
                | "match_arm" => 1,
                "match_expression" => -1,
                "binary_expression" if operator_is(node, source, &["&&", "||"]) => 1,
                _ => 0,
            },
            Grammar::Python => match kind {
                "if_statement"
                | "elif_clause"
                | "for_statement"
                | "while_statement"
                | "except_clause"
                | "boolean_operator"
                | "conditional_expression"
                | "case_clause"
                | "for_in_clause"
                | "if_clause" => 1,
                "match_statement" => -1,
                _ => 0,
            },
            Grammar::Swift => match kind {
                "if_statement"
                | "guard_statement"
                | "for_statement"
                | "while_statement"
                | "repeat_while_statement"
                | "catch_block"
                | "switch_entry"
                | "conjunction_expression"
                | "disjunction_expression" => 1,
                "switch_statement" => -1,
                _ => 0,
            },
            Grammar::TypeScript | Grammar::Tsx | Grammar::JavaScript => match kind {
                "if_statement" | "for_statement" | "for_in_statement" | "while_statement"
                | "do_statement" | "switch_case" | "catch_clause" | "ternary_expression" => 1,
                "binary_expression" if operator_is(node, source, &["&&", "||", "??"]) => 1,
                _ => 0,
            },
        }
    }
}

/// Only named nodes can be functions. The keyword `function` in JavaScript is
/// an anonymous node with the same kind name.
fn is_function_node(grammar: Grammar, node: Node) -> bool {
    node.is_named() && grammar.is_function(node.kind())
}

fn operator_is(node: Node, source: &[u8], operators: &[&str]) -> bool {
    node.child_by_field_name("operator")
        .and_then(|op| op.utf8_text(source).ok())
        .is_some_and(|text| operators.contains(&text))
}

/// Parses source files and finds their functions. Keep one per thread: a
/// parser is not shared between threads, and building one per file is slow.
#[derive(Default)]
pub struct Analyzer {
    parsers: Vec<(Grammar, Parser)>,
}

impl Analyzer {
    /// Whether a file of this language and extension has a grammar here.
    #[must_use]
    pub fn supports(language: Language, path: &Path) -> bool {
        Grammar::for_file(language, extension_of(path)).is_some()
    }

    /// The functions in `source`, in source order. Returns an empty list for
    /// languages without a grammar, and for files the parser cannot read.
    pub fn functions(&mut self, language: Language, path: &Path, source: &[u8]) -> Vec<Function> {
        let Some(grammar) = Grammar::for_file(language, extension_of(path)) else {
            return Vec::new();
        };
        let Some(parser) = self.parser(grammar) else {
            return Vec::new();
        };
        let Some(tree) = parser.parse(source, None) else {
            return Vec::new();
        };

        let mut functions = Vec::new();
        let mut stack = vec![tree.root_node()];
        while let Some(node) = stack.pop() {
            if is_function_node(grammar, node) {
                functions.push(Function {
                    name: function_name(node, source),
                    start_line: row_to_line(node.start_position().row),
                    end_line: row_to_line(node.end_position().row),
                    complexity: complexity_of(grammar, node, source),
                });
            }
            let mut cursor = node.walk();
            stack.extend(node.children(&mut cursor));
        }
        functions.sort_by_key(|f| (f.start_line, f.end_line));
        functions
    }

    fn parser(&mut self, grammar: Grammar) -> Option<&mut Parser> {
        if let Some(index) = self.parsers.iter().position(|(g, _)| *g == grammar) {
            return Some(&mut self.parsers[index].1);
        }
        let mut parser = Parser::new();
        parser.set_language(&grammar.ts_language()).ok()?;
        self.parsers.push((grammar, parser));
        self.parsers.last_mut().map(|(_, parser)| parser)
    }
}

fn extension_of(path: &Path) -> &str {
    path.extension().and_then(|e| e.to_str()).unwrap_or("")
}

fn row_to_line(row: usize) -> u64 {
    u64::try_from(row).unwrap_or(u64::MAX - 1) + 1
}

/// 1 plus the weights of every node in the function's body, not counting the
/// bodies of nested functions, which are scored on their own.
fn complexity_of(grammar: Grammar, function: Node, source: &[u8]) -> u32 {
    let mut total: i64 = 1;
    let mut stack = Vec::new();
    let mut cursor = function.walk();
    stack.extend(function.children(&mut cursor));
    while let Some(node) = stack.pop() {
        if is_function_node(grammar, node) {
            continue;
        }
        total += grammar.weight(node, source);
        let mut cursor = node.walk();
        stack.extend(node.children(&mut cursor));
    }
    u32::try_from(total.max(1)).unwrap_or(u32::MAX)
}

/// The name a function is known by. Anonymous functions take the name of the
/// binding or property they are assigned to, when there is one.
fn function_name(node: Node, source: &[u8]) -> String {
    if let Some(name) = node.child_by_field_name("name") {
        return text_of(name, source);
    }
    if let Some(parent) = node.parent() {
        let binding = match parent.kind() {
            "variable_declarator" | "public_field_definition" => parent.child_by_field_name("name"),
            "pair" => parent.child_by_field_name("key"),
            _ => None,
        };
        if let Some(name) = binding {
            return text_of(name, source);
        }
    }
    "<anonymous>".to_string()
}

fn text_of(node: Node, source: &[u8]) -> String {
    String::from_utf8_lossy(&source[node.byte_range()]).into_owned()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn functions(path: &str, source: &str) -> Vec<Function> {
        let path = Path::new(path);
        let language = Language::from_extension(extension_of(path)).unwrap();
        Analyzer::default().functions(language, path, source.as_bytes())
    }

    fn complexity(path: &str, source: &str) -> Vec<(String, u32)> {
        functions(path, source)
            .into_iter()
            .map(|f| (f.name, f.complexity))
            .collect()
    }

    #[test]
    fn straight_line_rust_function_has_complexity_one() {
        assert_eq!(
            complexity("a.rs", "fn f() -> u8 {\n    1\n}\n"),
            [("f".to_string(), 1)]
        );
    }

    #[test]
    fn rust_decisions_add_one_each() {
        // 1 base, `if` 1, `else if` 1, `while` 1, `for` 1, `&&` 1, `||` 1.
        let source = "\
fn f(a: bool, b: bool, n: u32) {
    if a {
    } else if b && n > 0 {
    }
    while n > 0 {}
    for _ in 0..n {}
    let _ = a || b;
}
";
        assert_eq!(complexity("a.rs", source), [("f".to_string(), 7)]);
    }

    #[test]
    fn rust_match_counts_arms_minus_one() {
        // 1 base plus (4 arms - 1) = 4.
        let source = "\
fn f(n: u8) -> u8 {
    match n {
        0 => 1,
        1 => 2,
        2 => 3,
        _ => 4,
    }
}
";
        assert_eq!(complexity("a.rs", source), [("f".to_string(), 4)]);
    }

    #[test]
    fn nested_functions_are_scored_alone_and_closures_are_not() {
        let source = "\
fn outer(n: u32) -> u32 {
    fn inner(m: u32) -> u32 {
        if m > 1 { 1 } else { 2 }
    }
    let f = |x: u32| if x > 0 { x } else { 0 };
    if n > 0 { inner(n) + f(n) } else { 0 }
}
";
        let found = complexity("a.rs", source);
        assert_eq!(found, [("outer".to_string(), 3), ("inner".to_string(), 2)]);
    }

    #[test]
    fn rust_methods_inside_impl_blocks_are_found() {
        let source = "\
struct S;
impl S {
    fn a(&self) {}
    fn b(&self, x: bool) { if x {} }
}
";
        assert_eq!(
            complexity("a.rs", source),
            [("a".to_string(), 1), ("b".to_string(), 2)]
        );
    }

    #[test]
    fn python_functions_and_decisions() {
        // 1 base, `if` 1, `elif` 1, `for` 1, `and` 1, `except` 1, ternary 1.
        let source = "\
def f(a, b, xs):
    if a:
        pass
    elif b and xs:
        pass
    for x in xs:
        pass
    try:
        pass
    except ValueError:
        pass
    return 1 if a else 2
";
        assert_eq!(complexity("a.py", source), [("f".to_string(), 7)]);
    }

    #[test]
    fn python_match_counts_cases_minus_one() {
        let source = "\
def f(n):
    match n:
        case 0:
            return 1
        case 1:
            return 2
        case _:
            return 3
";
        assert_eq!(complexity("a.py", source), [("f".to_string(), 3)]);
    }

    #[test]
    fn typescript_functions_arrows_and_methods() {
        let source = "\
function f(a: boolean, b: boolean) {
    if (a && b) { return 1; }
    switch (a ? 1 : 2) {
        case 1: return 2;
        case 2: return 3;
        default: return 4;
    }
}
class C {
    m(x: number) { return x ?? 0; }
}
const g = (y: number) => y > 0 ? y : 0;
";
        assert_eq!(
            complexity("a.ts", source),
            [
                ("f".to_string(), 6),
                ("m".to_string(), 2),
                ("g".to_string(), 2),
            ]
        );
    }

    #[test]
    fn javascript_loops_and_catch() {
        let source = "\
function f(xs) {
    for (const x of xs) {
        try { x(); } catch (e) { continue; }
    }
    while (false) {}
}
";
        assert_eq!(complexity("a.js", source), [("f".to_string(), 4)]);
    }

    #[test]
    fn tsx_files_use_the_tsx_grammar() {
        // Plain TypeScript would not parse the JSX; with the TSX grammar it is
        // one function with a ternary.
        let source = "const C = (p: { ok: boolean }) => p.ok ? <b /> : null;\n";
        assert_eq!(complexity("a.tsx", source), [("C".to_string(), 2)]);
    }

    #[test]
    fn swift_functions_and_decisions() {
        // 1 base, `if` 1, `guard` 1, `&&` 1, `for` 1, switch with 3 entries = 2.
        let source = "\
func f(a: Bool, b: Bool, xs: [Int], n: Int) -> Int {
    if a && b { return 1 }
    guard n > 0 else { return 0 }
    for _ in xs {}
    switch n {
    case 1: return 1
    case 2: return 2
    default: return 3
    }
}
";
        assert_eq!(complexity("a.swift", source), [("f".to_string(), 7)]);
    }

    #[test]
    fn languages_without_a_grammar_have_no_functions() {
        assert_eq!(functions("a.kt", "fun f() {}\n"), Vec::new());
        assert!(!Analyzer::supports(Language::Kotlin, Path::new("a.kt")));
        assert!(Analyzer::supports(Language::Rust, Path::new("a.rs")));
    }
}
