use glast::parser::{SyntaxToken, SyntaxType};
use tower_lsp::lsp_types::{Position, SemanticToken};

/// Converts [`SyntaxToken`]s to LSP semantic tokens.
pub fn convert(
	syntax_tokens: Vec<SyntaxToken>,
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
		let range = file.span_to_lsp(span);
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
			//    next token will have the correct data to perform it's own deltas.
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

pub const TOKEN_TYPES: [&str; 28] = [
	"keyword",
	"builtInType", // nonstandard - inherits from `keyword`
	"struct",
	"punctuation", // nonstandard - inherits from `operator`
	"operator",
	"function",
	"variable",
	"parameter",
	"layout", // custom - inherits from `variable`
	"number",
	"boolean", // nonstandard - inherits from `keyword`
	"string",
	"comment",
	"lineContinuator", // custom - inherits from nonstandard `escapeSequence`, which inherits from `string`
	"unresolvedReference", // nonstandard
	"invalid",         // custom - inherits from nonstandard `unresolvedReference`
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
];

const KEYWORD: u32 = 0;
const _PRIMITIVE: u32 = 1;
const _STRUCT: u32 = 2;
const PUNCTUATION: u32 = 3;
const OPERATOR: u32 = 4;
const _FUNCTION: u32 = 5;
const VARIABLE: u32 = 6;
const PARAMETER: u32 = 7;
const LAYOUT: u32 = 8;
const NUMBER: u32 = 9;
const BOOLEAN: u32 = 10;
const COMMENT: u32 = 11;
const _STRING: u32 = 12;
const _LINE_CONTINUATOR: u32 = 13;
const UNRESOLVED: u32 = 14;
const INVALID: u32 = 15;
const OBJECT_MACRO: u32 = 16;
const FUNCTION_MACRO: u32 = 17;
const DIRECTIVE: u32 = 18;
const DIRECTIVE_CONCAT: u32 = 19;
const DIRECTIVE_HASH: u32 = 20;
const DIRECTIVE_NAME: u32 = 21;
const DIRECTIVE_VERSION: u32 = 22;
const DIRECTIVE_PROFILE: u32 = 23;
const DIRECTIVE_EXT_NAME: u32 = 24;
const DIRECTIVE_EXT_BEHAVIOUR: u32 = 25;
const DIRECTIVE_LINE_NUMBER: u32 = 26;
const DIRECTIVE_ERROR: u32 = 27;

fn convert_to_lsp_ty(ty: SyntaxType) -> u32 {
	match ty {
		SyntaxType::Keyword => KEYWORD,
		SyntaxType::Punctuation => PUNCTUATION,
		SyntaxType::Operator => OPERATOR,
		SyntaxType::Parameter => PARAMETER,
		SyntaxType::LayoutQualifier => LAYOUT,
		SyntaxType::Number => NUMBER,
		SyntaxType::Boolean => BOOLEAN,
		SyntaxType::Comment => COMMENT,
		SyntaxType::UncheckedIdent => VARIABLE,
		SyntaxType::UnresolvedIdent => UNRESOLVED,
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
		SyntaxType::Ident => VARIABLE,
	}
}

/* WARNING: Ensure that this array and order of declaration of `glast::parser::SyntaxModifiers` match */

pub const TOKEN_MODIFIERS: [&str; 4] = [
	"macroDefinition", // nonstandard
	"macroBody",       // nonstandard
	"undefine",        // nonstandard
	"conditional",     // nonstandard
];
