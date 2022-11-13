#![allow(unused)]
use glast::{parser::SyntaxToken, Spanned};
use tower_lsp::lsp_types::{Position, SemanticToken};

/// Converts [`SyntaxToken`]s to LSP semantic tokens.
pub fn convert(
	syntax_tokens: Vec<Spanned<SyntaxToken>>,
	file: &crate::File,
	supports_multiline: bool,
) -> Vec<SemanticToken> {
	let mut tokens = Vec::new();
	let mut prev_line = 0;
	let mut prev_start_char = 0;
	for (token, span) in syntax_tokens {
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
						token_type: convert_to_lsp_token(token.clone()),
						token_modifiers_bitset: 0,
					});

					is_first = false;
				} else {
					//  Since we know that this span begins on a new line, we don't need to calculate any deltas.
					tokens.push(SemanticToken {
						delta_line: 1,
						delta_start: 0,
						length: (b - a) as u32,
						token_type: convert_to_lsp_token(token.clone()),
						token_modifiers_bitset: 0,
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
				token_type: convert_to_lsp_token(token),
				token_modifiers_bitset: 0,
			});

			prev_line = line;
			prev_start_char = character;
		}
	}

	tokens
}

/* WARNING: Ensure that the array and constant numbers match */

pub const TOKEN_TYPES: [&str; 15] = [
	"keyword",
	"builtInType",
	"punctuation",
	"operator",
	"function",
	"macro",
	"struct",
	"variable",
	"parameter",
	"number",
	"boolean",
	"comment",
	"espaceSequence",
	"unresolvedReference",
	"invalid",
];

const KEYWORD: u32 = 0;
const PRIMITIVE: u32 = 1;
const PUNCTUATION: u32 = 2;
const OPERATOR: u32 = 3;
const FUNCTION: u32 = 4;
const MACRO: u32 = 5;
const STRUCT: u32 = 6;
const VARIABLE: u32 = 7;
const PARAMETER: u32 = 8;
const NUMBER: u32 = 9;
const BOOLEAN: u32 = 10;
const COMMENT: u32 = 11;
const LINE_CONTINUATOR: u32 = 12;
const UNRESOLVED: u32 = 13;
const INVALID: u32 = 14;

fn convert_to_lsp_token(token: SyntaxToken) -> u32 {
	match token {
		SyntaxToken::Number => NUMBER,
		SyntaxToken::Boolean => BOOLEAN,
		SyntaxToken::UncheckedIdent => VARIABLE,
		SyntaxToken::LayoutIdent => VARIABLE,
		SyntaxToken::UnresolvedIdent => UNRESOLVED,
		SyntaxToken::Keyword => KEYWORD,
		SyntaxToken::Punctuation => PUNCTUATION,
		SyntaxToken::Operator => OPERATOR,
		SyntaxToken::Comment => COMMENT,
		SyntaxToken::Invalid => INVALID,
		SyntaxToken::Directive => MACRO,
		SyntaxToken::ObjectMacro => MACRO,
		SyntaxToken::FunctionMacro => MACRO,
		SyntaxToken::Ident => VARIABLE,
		SyntaxToken::MacroConcat => MACRO,
	}
}
