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
	ChoiceOn(u64),
	ChoiceOff(u64),
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

			fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
			where
				A: serde::de::MapAccess<'v>,
			{
				let Some((key, value)) = map.next_entry::<String, u64>()? else {
					return Err(serde::de::Error::custom(format!(
						"map does not have a \"on\" or \"off\" key"
					)));
				};
				match key.as_ref() {
					"on" => Ok(EvalConditionalChoice::ChoiceOn(value)),
					"off" => Ok(EvalConditionalChoice::ChoiceOff(value)),
					_ => Err(serde::de::Error::custom(format!(
						"map does not have a \"on\" or \"off\" key"
					))),
				}
			}
		}

		deserializer.deserialize_any(Visitor)
	}
}
