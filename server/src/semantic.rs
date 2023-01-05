//! Semantic token highlighting functionality.

use glast::syntax::*;
use tower_lsp::lsp_types::{Position, SemanticToken};

/// Converts [`SyntaxToken`]s to LSP semantic tokens.
pub fn convert(
	syntax_tokens: &[SyntaxToken],
	file: &crate::file::File,
	supports_multiline: bool,
) -> Vec<SemanticToken> {
	let mut tokens = Vec::new();
	let mut prev_line = 0;
	let mut prev_start_char = 0;
	for SyntaxToken {
		ty,
		modifiers,
		span,
	} in syntax_tokens
	{
		let range = file.span_to_lsp(*span);
		if range.start.line != range.end.line && !supports_multiline {
			// We have a multi-line token but the client doesn't support that, so we must split it per-line. What
			// we do is the following:
			// 1. Record the start and end positions, and the positions of the beginnings of each line in-between
			//    (the dots):
			//
			// ./*
			// .
			// .
			// .   */.
			//
			// 2. Iterate over pairs of points, like a chain: A-B, B-C, C-D, etc.
			// 3. For the first iteration, perform the same checks as normal, i.e. if there's something on the same
			//    line before then create the correct deltas.
			// 4. For the rest, create a span between the first and second points. We also set the `prev_*`
			//    variables to the value of the first point, so that once the multi-line span is finished, whatever
			//    next token will have the correct data to perform its own deltas.
			let mut points = Vec::new();
			points.push(span.start);
			let start = file.position_to_lsp(span.start);
			let end = file.position_to_lsp(span.end);
			for i in start.line + 1..=end.line {
				if let Some((_, start_pos)) = file.lines.get(i as usize) {
					points.push(*start_pos);
				} else {
					break;
				}
			}
			points.push(span.end);

			// Invariant: Since the range spans more than one line, it's guaranteed that we have at least 3 points
			// here, so at least two iterations. That is why the `is_first` branch doesn't set the `prev_*`
			// variables.
			let mut is_first = true;
			for t in points.windows(2) {
				let a = t[0];
				let b = t[1];

				if is_first {
					// Apply the correct deltas to the first span.
					let Position { line, character } = file.position_to_lsp(a);
					let length = (b - a) as u32;
					let (delta_line, delta_start) = if line == prev_line {
						(0, character - prev_start_char)
					} else {
						(line - prev_line, character)
					};

					tokens.push(SemanticToken {
						delta_line,
						delta_start,
						length,
						token_type: convert_to_lsp_ty(ty),
						token_modifiers_bitset: modifiers.bits(),
					});

					is_first = false;
				} else {
					//  Since we know that this span begins on a new line, we don't need to calculate any deltas.
					tokens.push(SemanticToken {
						delta_line: 1,
						delta_start: 0,
						length: (b - a) as u32,
						token_type: convert_to_lsp_ty(ty),
						token_modifiers_bitset: modifiers.bits(),
					});
					let Position { line, character } = file.position_to_lsp(a);
					prev_line = line;
					prev_start_char = character;
				}
			}
		} else {
			let Position { line, character } = file.position_to_lsp(span.start);
			let length = (span.end - span.start) as u32;
			let (delta_line, delta_start) = if line == prev_line {
				(0, character - prev_start_char)
			} else {
				(line - prev_line, character)
			};

			tokens.push(SemanticToken {
				delta_line,
				delta_start,
				length,
				token_type: convert_to_lsp_ty(ty),
				token_modifiers_bitset: modifiers.bits(),
			});

			prev_line = line;
			prev_start_char = character;
		}
	}

	tokens
}

/* WARNING: Ensure that the array and constant numbers match */

pub const TOKEN_TYPES: [&str; 31] = [
	"keyword",
	"punctuation", // nonstandard - inherits from `operator`
	"operator",
	"number",
	"boolean", // nonstandard - inherits from `keyword`
	"string",
	"comment",
	"builtInType", // nonstandard - inherits from `keyword`
	"struct",
	"function",
	"subroutine", // nonstandard - inherits from `function`
	"variable",
	"parameter",
	"layoutQualifier",       // custom - inherits from `variable`
	"ident",                 // custom - inherits from `variable`
	"unresolvedReference",   // nonstandard
	"invalid", // custom - inherits from nonstandard `unresolvedReference`
	"lineContinuator", // custom - inherits from nonstandard `escapeSequence`, which inherits from `string`
	"objectMacro",     // custom - inherits from `macro`
	"functionMacro",   // custom - inherits from `macro`
	"directive",       // custom - inherits from `keyword`
	"directiveConcat", // custom - inherits from custom `directive`
	"directiveHash",   // custom - inherits from custom `directive`
	"directiveName",   // custom - inherits from custom `directive`
	"directiveVersion", // custom - inherits from `number`
	"directiveProfile", // custom - inherits from custom `directive`
	"directiveExtName", // custom - inherits from `variable`
	"directiveExtBehaviour", // custom - inherits from custom `directive`
	"directiveLineNumber", // custom - inherits from `number`
	"directiveError",  // custom - inherits from custom `directive`
	"directivePragma", // custom - inherits from custom `directive`
];

const KEYWORD: u32 = 0;
const PUNCTUATION: u32 = 1;
const OPERATOR: u32 = 2;
const NUMBER: u32 = 3;
const BOOLEAN: u32 = 4;
const _STRING: u32 = 5;
const COMMENT: u32 = 6;
const _PRIMITIVE: u32 = 7;
const _STRUCT: u32 = 8;
const _FUNCTION: u32 = 9;
const _SUBROUTINE: u32 = 10;
const _VARIABLE: u32 = 11;
const PARAMETER: u32 = 12;
const LAYOUT_QUALIFIER: u32 = 13;
const IDENT: u32 = 14;
const UNRESOLVED_REFERENCE: u32 = 15;
const INVALID: u32 = 16;
const _LINE_CONTINUATOR: u32 = 17;
const OBJECT_MACRO: u32 = 18;
const FUNCTION_MACRO: u32 = 19;
const DIRECTIVE: u32 = 20;
const DIRECTIVE_CONCAT: u32 = 21;
const DIRECTIVE_HASH: u32 = 22;
const DIRECTIVE_NAME: u32 = 23;
const DIRECTIVE_VERSION: u32 = 24;
const DIRECTIVE_PROFILE: u32 = 25;
const DIRECTIVE_EXT_NAME: u32 = 26;
const DIRECTIVE_EXT_BEHAVIOUR: u32 = 27;
const DIRECTIVE_LINE_NUMBER: u32 = 28;
const DIRECTIVE_ERROR: u32 = 29;
const DIRECTIVE_PRAGMA: u32 = 30;

fn convert_to_lsp_ty(ty: &SyntaxType) -> u32 {
	match ty {
		SyntaxType::Keyword => KEYWORD,
		SyntaxType::Punctuation => PUNCTUATION,
		SyntaxType::Operator => OPERATOR,
		SyntaxType::Number => NUMBER,
		SyntaxType::Boolean => BOOLEAN,
		SyntaxType::Comment => COMMENT,
		SyntaxType::Parameter => PARAMETER,
		SyntaxType::LayoutQualifier => LAYOUT_QUALIFIER,
		SyntaxType::UncheckedIdent => IDENT,
		SyntaxType::Ident => IDENT,
		SyntaxType::UnresolvedIdent => UNRESOLVED_REFERENCE,
		SyntaxType::Invalid => INVALID,
		SyntaxType::ObjectMacro => OBJECT_MACRO,
		SyntaxType::FunctionMacro => FUNCTION_MACRO,
		SyntaxType::Directive => DIRECTIVE,
		SyntaxType::DirectiveConcat => DIRECTIVE_CONCAT,
		SyntaxType::DirectiveHash => DIRECTIVE_HASH,
		SyntaxType::DirectiveName => DIRECTIVE_NAME,
		SyntaxType::DirectiveVersion => DIRECTIVE_VERSION,
		SyntaxType::DirectiveProfile => DIRECTIVE_PROFILE,
		SyntaxType::DirectiveExtName => DIRECTIVE_EXT_NAME,
		SyntaxType::DirectiveExtBehaviour => DIRECTIVE_EXT_BEHAVIOUR,
		SyntaxType::DirectiveLineNumber => DIRECTIVE_LINE_NUMBER,
		SyntaxType::DirectiveError => DIRECTIVE_ERROR,
		SyntaxType::DirectivePragma => DIRECTIVE_PRAGMA,
	}
}

/* WARNING: Ensure that this array and order of declaration of `glast::parser::SyntaxModifiers` match */

pub const TOKEN_MODIFIERS: [&str; 4] = [
	"macroSignature", // custom
	"macroBody",      // custom
	"undefine",       // custom
	"conditional",    // custom
];
