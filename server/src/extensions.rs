use serde::{Deserialize, Serialize};
use tower_lsp::lsp_types::{Range, Url};

// This file contains custom extensions to the Langauge Server Protocol. It is a mirror of
// `client/src/extensions.ts`

pub const SYNTAX_TREE: &str = "glsl/syntaxTree";
#[derive(Debug, PartialEq, Eq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SyntaxTreeParams {
	pub text_document_uri: Url,
	pub range: Option<Range>,
}
