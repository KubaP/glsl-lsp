use serde::{Deserialize, Serialize};
use tower_lsp::lsp_types::Url;

/* This file contains custom LSP extensions. It is a mirror of `/client/src/extensions.ts` */

pub const AST_CONTENT: &str = "glsl/astContent";
#[derive(Debug, PartialEq, Eq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AstContentParams {
	pub text_document_uri: Url,
	pub text_document_version: i32,
}
#[derive(Debug, PartialEq, Eq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AstContentResult {
	pub ast: String,
}
