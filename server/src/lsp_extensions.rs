use serde::{Deserialize, Serialize};
use tower_lsp::lsp_types::Url;

/* This file contains custom LSP extensions. It is a mirror of `/client/src/lsp_extensions.ts` */

pub const AST_CONTENT: &str = "glsl/astContent";
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AstContentParams {
	pub text_document_uri: Url,
	pub text_document_version: i32,
}
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AstContentResult {
	pub ast: String,
}

pub const EVAL_CONDITIONAL: &str = "glsl/evalConditional";
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EvalConditionalParams {
	pub text_document_uri: Url,
	pub choice: EvalConditionalChoice,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvalConditionalChoice {
	Off,
	Evaluate,
	Choice(u64),
}
impl<'de> Deserialize<'de> for EvalConditionalChoice {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: serde::Deserializer<'de>,
	{
		struct Visitor;
		impl<'v> serde::de::Visitor<'v> for Visitor {
			type Value = EvalConditionalChoice;

			fn expecting(
				&self,
				formatter: &mut std::fmt::Formatter,
			) -> std::fmt::Result {
				formatter.write_str("a string with the value \"off\" or \"eval\", or an integer greater than 0")
			}

			fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
			where
				E: serde::de::Error,
			{
				match v {
					"off" => Ok(EvalConditionalChoice::Off),
					"eval" => Ok(EvalConditionalChoice::Evaluate),
					_ => Err(E::custom(format!(
						"str is not \"off\" or \"eval\""
					))),
				}
			}

			fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
			where
				E: serde::de::Error,
			{
				Ok(EvalConditionalChoice::Choice(v))
			}
		}

		deserializer.deserialize_any(Visitor)
	}
}
