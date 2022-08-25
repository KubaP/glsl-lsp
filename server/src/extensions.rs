use serde::{Deserialize, Serialize};
use tower_lsp::lsp_types::{Position, Range, Url};

// This file contains custom extensions to the Langauge Server Protocol. It is a mirror of
// `client/src/extensions.ts`

pub const SYNTAX_TREE_CONTENT: &str = "glsl/syntaxTreeContent";
#[derive(Debug, PartialEq, Eq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SyntaxTreeContentParams {
	pub text_document_uri: Url,
	pub text_document_version: i32,
	pub range: Option<Range>,
}
#[derive(Debug, PartialEq, Eq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SyntaxTreeContentResult {
	pub cst: String,
	pub highlight: Range,
}

pub const SYNTAX_TREE_HIGHLIGHT: &str = "glsl/syntaxTreeHighlight";
#[derive(Debug, PartialEq, Eq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SyntaxTreeHighlightParams {
	pub text_document_uri: Url,
	pub text_document_version: i32,
	pub cursor: Position,
}
#[derive(Debug, PartialEq, Eq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SyntaxTreeHighlightResult {
	pub highlight: Range,
}
