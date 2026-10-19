//! Languages, the file extensions that select them, and the comment and string
//! syntax the line classifier needs for each one.

/// The languages clocrap counts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Language {
    Rust,
    Toml,
    Json,
    Markdown,
    Python,
    Swift,
    TypeScript,
    JavaScript,
    Kotlin,
    Shell,
    Yaml,
}

/// A block comment such as `/* ... */`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockComment {
    pub open: &'static [u8],
    pub close: &'static [u8],
    /// Whether a block comment may contain another one, as in Rust and Swift.
    pub nests: bool,
}

/// A string literal. Code inside a string is code, so a comment marker inside
/// one does not start a comment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StringSyntax {
    pub open: &'static [u8],
    pub close: &'static [u8],
    /// Whether a backslash escapes the next byte inside the string.
    pub escapes: bool,
    /// Whether the string may run across lines.
    pub multiline: bool,
}

/// How one language marks comments and strings.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Syntax {
    pub line_comments: &'static [&'static [u8]],
    pub block: Option<BlockComment>,
    /// Longer openers come first, so `"""` is tried before `"`.
    pub strings: &'static [StringSyntax],
    /// Whether `'x'` and `'\n'` are character literals. Rust and Kotlin need
    /// this, because a lifetime such as `'a` must not open a string.
    pub char_literals: bool,
}

const SLASH: &[&[u8]] = &[b"//"];
const HASH: &[&[u8]] = &[b"#"];
const NONE: &[&[u8]] = &[];

const DQ: StringSyntax = StringSyntax {
    open: b"\"",
    close: b"\"",
    escapes: true,
    multiline: false,
};
const SQ: StringSyntax = StringSyntax {
    open: b"'",
    close: b"'",
    escapes: false,
    multiline: false,
};
const SQ_ESC: StringSyntax = StringSyntax {
    open: b"'",
    close: b"'",
    escapes: true,
    multiline: false,
};
const TRIPLE_DQ: StringSyntax = StringSyntax {
    open: b"\"\"\"",
    close: b"\"\"\"",
    escapes: true,
    multiline: true,
};
const TRIPLE_SQ: StringSyntax = StringSyntax {
    open: b"'''",
    close: b"'''",
    escapes: true,
    multiline: true,
};
const BACKTICK: StringSyntax = StringSyntax {
    open: b"`",
    close: b"`",
    escapes: true,
    multiline: true,
};

const C_BLOCK: BlockComment = BlockComment {
    open: b"/*",
    close: b"*/",
    nests: false,
};
const NESTED_C_BLOCK: BlockComment = BlockComment {
    open: b"/*",
    close: b"*/",
    nests: true,
};

const RUST_STRINGS: &[StringSyntax] = &[
    StringSyntax {
        open: b"r##\"",
        close: b"\"##",
        escapes: false,
        multiline: true,
    },
    StringSyntax {
        open: b"r#\"",
        close: b"\"#",
        escapes: false,
        multiline: true,
    },
    StringSyntax {
        open: b"r\"",
        close: b"\"",
        escapes: false,
        multiline: true,
    },
    DQ,
];

impl Language {
    /// Every language, in the order they are documented.
    pub const ALL: [Language; 11] = [
        Language::Rust,
        Language::Toml,
        Language::Json,
        Language::Markdown,
        Language::Python,
        Language::Swift,
        Language::TypeScript,
        Language::JavaScript,
        Language::Kotlin,
        Language::Shell,
        Language::Yaml,
    ];

    /// The name printed in reports.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Language::Rust => "Rust",
            Language::Toml => "TOML",
            Language::Json => "JSON",
            Language::Markdown => "Markdown",
            Language::Python => "Python",
            Language::Swift => "Swift",
            Language::TypeScript => "TypeScript",
            Language::JavaScript => "JavaScript",
            Language::Kotlin => "Kotlin",
            Language::Shell => "Shell",
            Language::Yaml => "YAML",
        }
    }

    /// The language a file extension selects, matched case-insensitively.
    #[must_use]
    pub fn from_extension(extension: &str) -> Option<Language> {
        let lower = extension.to_ascii_lowercase();
        Some(match lower.as_str() {
            "rs" => Language::Rust,
            "toml" => Language::Toml,
            "json" => Language::Json,
            "md" | "markdown" => Language::Markdown,
            "py" => Language::Python,
            "swift" => Language::Swift,
            "ts" | "tsx" | "mts" | "cts" => Language::TypeScript,
            "js" | "jsx" | "mjs" | "cjs" => Language::JavaScript,
            "kt" | "kts" => Language::Kotlin,
            "sh" | "bash" | "zsh" => Language::Shell,
            "yml" | "yaml" => Language::Yaml,
            _ => return None,
        })
    }

    /// The comment and string syntax the line classifier uses.
    #[must_use]
    pub fn syntax(self) -> Syntax {
        match self {
            Language::Rust => Syntax {
                line_comments: SLASH,
                block: Some(NESTED_C_BLOCK),
                strings: RUST_STRINGS,
                char_literals: true,
            },
            Language::Toml => Syntax {
                line_comments: HASH,
                block: None,
                strings: &[TRIPLE_DQ, TRIPLE_SQ_LITERAL, DQ, SQ],
                char_literals: false,
            },
            Language::Json => Syntax {
                line_comments: NONE,
                block: None,
                strings: &[DQ],
                char_literals: false,
            },
            // cloc's convention: prose has no comments, so every non-blank line is code.
            Language::Markdown => Syntax {
                line_comments: NONE,
                block: None,
                strings: &[],
                char_literals: false,
            },
            Language::Python => Syntax {
                line_comments: HASH,
                block: None,
                strings: &[TRIPLE_DQ, TRIPLE_SQ, DQ, SQ_ESC],
                char_literals: false,
            },
            Language::Swift => Syntax {
                line_comments: SLASH,
                block: Some(NESTED_C_BLOCK),
                strings: &[TRIPLE_DQ, DQ],
                char_literals: false,
            },
            Language::TypeScript | Language::JavaScript => Syntax {
                line_comments: SLASH,
                block: Some(C_BLOCK),
                strings: &[DQ, SQ_ESC, BACKTICK],
                char_literals: false,
            },
            Language::Kotlin => Syntax {
                line_comments: SLASH,
                block: Some(NESTED_C_BLOCK),
                strings: &[TRIPLE_DQ_RAW, DQ],
                char_literals: true,
            },
            Language::Shell | Language::Yaml => Syntax {
                line_comments: HASH,
                block: None,
                strings: &[DQ, SQ],
                char_literals: false,
            },
        }
    }
}

/// TOML literal strings: `'''` and `'` never process escapes.
const TRIPLE_SQ_LITERAL: StringSyntax = StringSyntax {
    open: b"'''",
    close: b"'''",
    escapes: false,
    multiline: true,
};

/// Kotlin raw strings: `"""` has no escapes.
const TRIPLE_DQ_RAW: StringSyntax = StringSyntax {
    open: b"\"\"\"",
    close: b"\"\"\"",
    escapes: false,
    multiline: true,
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extensions_select_languages_case_insensitively() {
        assert_eq!(Language::from_extension("rs"), Some(Language::Rust));
        assert_eq!(Language::from_extension("RS"), Some(Language::Rust));
        assert_eq!(Language::from_extension("md"), Some(Language::Markdown));
        assert_eq!(Language::from_extension("tsx"), Some(Language::TypeScript));
        assert_eq!(Language::from_extension("mjs"), Some(Language::JavaScript));
        assert_eq!(Language::from_extension("kts"), Some(Language::Kotlin));
        assert_eq!(Language::from_extension("zsh"), Some(Language::Shell));
        assert_eq!(Language::from_extension("yaml"), Some(Language::Yaml));
        assert_eq!(Language::from_extension("exe"), None);
        assert_eq!(Language::from_extension(""), None);
    }

    #[test]
    fn every_language_has_a_distinct_name() {
        let mut names: Vec<&str> = Language::ALL.iter().map(|l| l.name()).collect();
        names.sort_unstable();
        names.dedup();
        assert_eq!(names.len(), Language::ALL.len());
    }
}
