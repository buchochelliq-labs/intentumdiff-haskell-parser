//! Haskell parser plugin — full-parse mode.
//!
//! Handles `.hs` and `.lhs` files.
//! The plugin parses source with Tree-sitter inside Rust/Wasm.
//!
//! Semantic model:
//! - `type_class_declaration` / `class_declaration`  → class-like (typeclass)
//! - `data_type` / `newtype_declaration`              → class-like (algebraic data type)
//! - `function_declaration` / `function_equation`     → method-like (top-level function)
//! - `type_class_instance_declaration` / `instance_declaration` → method-like (instance impl)
//! - Labels are extracted from the leading identifier or constructor name.

use intentumdiff_plugin_sdk::{
    cst::CstNode,
    hash::structural_hash_with_memo,
    tree::{SemanticNode, SemanticNodeBuilder},
};

wit_bindgen::generate!({
    path: "wit/plugin.wit",
    world: "parser-plugin",
});

use crate::exports::intentumdiff::plugin::parser::ExamplePair;
use crate::exports::intentumdiff::plugin::parser::Guest;
use crate::exports::intentumdiff::plugin::parser::LanguageInfoRecord;
use crate::exports::intentumdiff::plugin::parser::ParserMode;

const PLUGIN_METADATA: &str = include_str!("../plugin_metadata.info");

fn language_info_for(ids: Vec<String>) -> Vec<LanguageInfoRecord> {
    let metadata = intentumdiff_plugin_sdk::metadata::parse_plugin_metadata(PLUGIN_METADATA);
    ids.into_iter()
        .map(|language_id| {
            let info = metadata.language_or_default(&language_id);
            LanguageInfoRecord {
                language_id: info.language_id,
                language_name: info.language_name,
                language_short_name: info.language_short_name,
                monaco_language: info.monaco_language,
                default_filename: info.default_filename,
                language_file_extensions: info.language_file_extensions,
                author: metadata.author().to_string(),
                plugin_version: metadata.plugin_version().to_string(),
                last_updated: metadata.last_updated().to_string(),
            }
        })
        .collect()
}
struct HaskellParser;

const TRIVIA: &[&str] = &[
    "comment",
    "line_comment",
    "block_comment",
    "haddock",
    "cpp_directive",
    "pragma",
];

const SEMANTIC_TYPES: &[&str] = &[
    // Root
    "haskell",
    // Module structure
    "module",
    "module_head",
    "exports",
    "export",
    "imports",
    "import",
    "qualified_module_name",
    // Type class / instance
    "type_class_declaration",
    "class_declaration",
    "type_class_instance_declaration",
    "instance_declaration",
    // Data types
    "data_type",
    "newtype_declaration",
    "type_synonym",
    "type_definition",
    "gadt",
    "constructor",
    "record_fields",
    "field",
    // Functions
    "function_declaration",
    "function_equation",
    "function_body",
    "type_signature",
    "operator_declaration",
    "fixity_declaration",
    "pattern",
    "patterns",
    // Bindings
    "where_clause",
    "let_expression",
    "let_statement",
    // Expressions
    "do_expression",
    "do_statement",
    "case_expression",
    "alternative",
    "guard",
    "if_expression",
    "lambda",
    "list_comprehension",
    "tuple",
    "list",
    "apply",
    "infix_operator",
    // Literals
    "string",
    "char",
    "integer",
    "float",
    "negative_literal",
    // Names
    "name",
    "operator",
    "constructor",
    "variable",
    "qualified_name",
];

fn is_semantic(node_type: &str) -> bool {
    SEMANTIC_TYPES.contains(&node_type)
}

fn is_class_like(node_type: &str) -> bool {
    matches!(
        node_type,
        "type_class_declaration"
            | "class_declaration"
            | "data_type"
            | "newtype_declaration"
            | "gadt"
    )
}

fn is_method_like(node_type: &str) -> bool {
    matches!(
        node_type,
        "function_declaration"
            | "function_equation"
            | "type_class_instance_declaration"
            | "instance_declaration"
            | "operator_declaration"
    )
}

/// Extract label for a node.
///
/// Haskell nodes generally have a leading name or constructor that serves as the label.
fn label_for(node: &CstNode) -> String {
    if node.is_leaf() {
        return node.text_or_empty().to_string();
    }
    // Literal containers label with their captured source text (SDK-shared, issue #47).
    if let Some(label) = intentumdiff_plugin_sdk::ts_convert::literal_label(node) {
        return label;
    }
    match node.node_type.as_str() {
        "function_declaration" | "function_equation" | "type_signature" => {
            // First child is usually the function name
            for child in &node.children {
                if matches!(
                    child.node_type.as_str(),
                    "name" | "variable" | "operator" | "identifier"
                ) {
                    return child.text_or_empty().to_string();
                }
            }
        }
        "type_class_declaration" | "class_declaration" => {
            // `class Eq a where` — extract class name
            for child in &node.children {
                if matches!(
                    child.node_type.as_str(),
                    "name" | "constructor" | "type_name" | "class_name"
                ) {
                    return child.text_or_empty().to_string();
                }
            }
        }
        "type_class_instance_declaration" | "instance_declaration" => {
            // `instance Eq Int` — use all type tokens as label
            let parts: Vec<&str> = node
                .children
                .iter()
                .filter(|c| matches!(c.node_type.as_str(), "name" | "constructor" | "type_name"))
                .map(|c| c.text_or_empty())
                .collect();
            if !parts.is_empty() {
                return parts.join(" ");
            }
        }
        "data_type" | "newtype_declaration" | "gadt" => {
            for child in &node.children {
                if matches!(
                    child.node_type.as_str(),
                    "name" | "constructor" | "type_name"
                ) {
                    return child.text_or_empty().to_string();
                }
            }
        }
        "type_synonym" | "type_definition" => {
            for child in &node.children {
                if matches!(child.node_type.as_str(), "name" | "type_name") {
                    return child.text_or_empty().to_string();
                }
            }
        }
        "import" => {
            for child in &node.children {
                if matches!(
                    child.node_type.as_str(),
                    "qualified_module_name" | "module_name" | "name"
                ) {
                    return child.text_or_empty().to_string();
                }
            }
        }
        "module" | "module_head" => {
            for child in &node.children {
                if matches!(
                    child.node_type.as_str(),
                    "qualified_module_name" | "module_name" | "name"
                ) {
                    return child.text_or_empty().to_string();
                }
            }
        }
        _ => {}
    }
    for child in &node.children {
        if matches!(
            child.node_type.as_str(),
            "name" | "variable" | "constructor" | "operator"
        ) {
            return child.text_or_empty().to_string();
        }
    }
    node.node_type.clone()
}

fn convert(
    node: &CstNode,
    id_prefix: &str,
    parent_class: Option<&str>,
    memo: &mut std::collections::HashMap<usize, String>,
) -> Option<SemanticNode> {
    convert_semantic_classed(
        node,
        id_prefix,
        parent_class,
        memo,
        &|t| TRIVIA.contains(&t),
        &is_semantic,
        &is_class_like,
        &is_method_like,
        &label_for,
    )
}



use intentumdiff_plugin_sdk::ts_convert::{convert_semantic_classed, node_to_cst};

fn parse_source(source: &str) -> Result<CstNode, String> {
    let mut parser = tree_sitter::Parser::new();
    let lang = tree_sitter_haskell::LANGUAGE.into();
    parser
        .set_language(&lang)
        .map_err(|_| "Failed to load haskell grammar".to_string())?;
    let tree = parser
        .parse(source, None)
        .ok_or_else(|| "Parse failed".to_string())?;
    Ok(node_to_cst(tree.root_node(), source.as_bytes()))
}

fn process_impl(source: &str) -> String {
    let root: CstNode = match parse_source(source) {
        Ok(n) => n,
        Err(e) => return format!(r#"{{\"error\":\"{}\"}}"#, e),
    };
    let mut memo = std::collections::HashMap::new();
    let sem = match convert(&root, "0", None, &mut memo) {
        Some(n) => n,
        None => return r#"{"error":"Empty semantic tree"}"#.to_string(),
    };
    match serde_json::to_string(&sem) {
        Ok(s) => s,
        Err(e) => format!(r#"{{"error":"Serialisation error: {}"}}"#, e),
    }
}

impl Guest for HaskellParser {
    fn get_parser_mode() -> ParserMode {
        ParserMode::FullParse
    }
    fn grammar_id() -> String {
        "haskell".to_string()
    }
    fn detect_language(filename: String, _content: String) -> String {
        let lower = filename.to_lowercase();
        if lower.ends_with(".hs") || lower.ends_with(".lhs") {
            return "haskell".to_string();
        }
        String::new()
    }
    fn preprocess_source(source: String) -> String {
        source
    }
    fn process(input: String, _language: String, _filename: String) -> String {
        process_impl(&input)
    }
    fn trivia_node_types() -> Vec<String> {
        TRIVIA.iter().map(|s| s.to_string()).collect()
    }
    fn language_ids() -> Vec<String> {
        vec!["haskell".to_string()]
    }
    fn language_info() -> Vec<LanguageInfoRecord> {
        language_info_for(Self::language_ids())
    }
    fn priority() -> i32 {
        0
    }

    fn example(_language: String) -> ExamplePair {
        ExamplePair {
            old: "greet :: String -> String\ngreet name = \"Hello, \" ++ name\n\nadd :: Int -> Int -> Int\nadd a b = a + b\n".to_string(),
            new: "greet :: String -> String\ngreet name = \"Hello, \" ++ name ++ \"!\"\n\nadd :: Int -> Int -> Int\nadd x y = x + y\n\nmultiply :: Int -> Int -> Int\nmultiply x y = x * y\n".to_string(),
        }
    }
}
export!(HaskellParser);

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exports::intentumdiff::plugin::parser::Guest;
    use intentumdiff_plugin_sdk::testing as t;

    #[test]
    fn grammar_id_nonempty() {
        assert!(!HaskellParser::grammar_id().is_empty());
    }

    #[test]
    fn language_ids_contain_grammar_id() {
        let gid = HaskellParser::grammar_id();
        let ids = HaskellParser::language_ids();
        assert!(
            ids.contains(&gid),
            "language_ids {:?} must contain {:?}",
            ids,
            gid
        );
    }

    #[test]
    fn detect_language_known_ext() {
        let r = HaskellParser::detect_language("test.hs".to_string(), "".to_string());
        assert_eq!(r.as_str(), "haskell");
    }

    #[test]
    fn detect_language_unknown_ext() {
        let r = HaskellParser::detect_language(
            "test.xyz_notareal_ext_9z8y".to_string(),
            "".to_string(),
        );
        assert_eq!(r.as_str(), "");
    }

    #[test]
    fn parser_mode_is_full_parse() {
        assert!(matches!(
            HaskellParser::get_parser_mode(),
            ParserMode::FullParse
        ));
    }

    #[test]
    fn process_impl_accepts_raw_example_source() {
        let example = HaskellParser::example(HaskellParser::grammar_id());
        let out = process_impl(&example.old);
        t::assert_valid_json(&out, "process(raw example)");
        assert!(!out.contains("\"error\""), "{out}");
    }
    #[test]
    fn process_impl_empty_returns_valid_json() {
        let out = process_impl("");
        t::assert_valid_json(&out, "process(empty)");
    }

    #[test]
    fn process_impl_whitespace_returns_valid_json() {
        let out = process_impl("   \n  ");
        t::assert_valid_json(&out, "process(whitespace)");
    }
}
