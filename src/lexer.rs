#![allow(unused)]

/// Concrete syntax tree tokens.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
	Num {
		num: String,
		suffix: Option<String>,
		base: NumBase,
		type_: NumType,
	},
	Bool(bool),
	Ident(String),
	Directive(String),
	Invalid(String),
	// Keywords
	If,
	Else,
	For,
	Switch,
	Case,
	Default,
	Break,
	Return,
	Discard,
	Struct,
	// Qualifiers
	In,
	Out,
	InOut,
	Uniform,
	Buffer,
	Const,
	Invariant,
	Interpolation,
	Precision,
	Layout,
	Location,
	Component,
	FragCoord,
	FragDepth,
	Index,
	FragTest,
	// Punctuation
	Op(OpType),
	Eq,
	Comma,
	Dot,
	Semi,
	Colon,
	Question,
	LParen,
	RParen,
	LBracket,
	RBracket,
	LBrace,
	RBrace,
}

/// Numerical bases.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumBase {
	Oct,
	Dec,
	Hex,
}

/// Specifies distinction between integers and floating points.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumType {
	Int,
	Float,
}

/// Mathematical and comparison operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpType {
	// Maths
	Add,
	Sub,
	Mul,
	Div,
	Rem,
	And,
	Or,
	Xor,
	LShift,
	RShift,
	AddEq,
	SubEq,
	MulEq,
	DivEq,
	RemEq,
	AndEq,
	OrEq,
	XorEq,
	LShiftEq,
	RShiftEq,
	AddAdd,
	SubSub,
	Flip,
	// Comparison
	EqEq,
	NotEq,
	Gt,
	Lt,
	Ge,
	Le,
	AndAnd,
	OrOr,
	XorXor,
	Not,
}

/// A lexer which allows stepping through a string character by character.
struct Lexer {
	/// The string stored as a vector of characters.
	chars: Vec<char>,
	/// The index of the current character.
	cursor: usize,
}

impl Lexer {
	/// Constructs a new `Lexer` from the given source string.
	fn new(source: &str) -> Self {
		Self {
			chars: source.chars().collect(),
			cursor: 0,
		}
	}

	/// Returns the current character under the cursor, without advancing the cursor.
	fn peek(&self) -> Option<char> {
		self.chars.get(self.cursor).map(|c| *c)
	}

	/// Peeks the next character without advancing the cursor; (returns the character under `cursor + 1`).
	fn lookahead_1(&self) -> Option<char> {
		self.chars.get(self.cursor + 1).map(|c| *c)
	}

	/// Advances the cursor by one.
	fn advance(&mut self) {
		self.cursor += 1;
	}

	/// Returns the current character under the cursor and advances the cursor by one.
	fn next(&mut self) -> Option<char> {
		// If we are successful in getting the character, advance the cursor.
		match self.chars.get(self.cursor) {
			Some(c) => {
				self.cursor += 1;
				Some(*c)
			}
			None => None,
		}
	}

	/// Tries to match a pattern starting at the current character under the cursor. If the match is successful,
	/// `true` is returned and the cursor is advanced to consume the pattern. If the match is unsuccessful, `false`
	/// is returned and the cursor stays in place.
	fn take_pat(&mut self, pat: &str) -> bool {
		let len = pat.len();

		// If the pattern fits within the remaining length of the character string, compare.
		if self.chars.len() >= self.cursor + len {
			let res = self.chars[self.cursor..self.cursor + len]
				.iter()
				.zip(pat.chars())
				.all(|(c, p)| *c == p);

			// If the match was successful, advance the cursor.
			if res {
				self.cursor += len;
			}

			return res;
		}

		false
	}

	/// Returns whether the `Lexer` has reached the end of the source string.
	fn is_done(&self) -> bool {
		// We check that the cursor is equal to the length, because that means we have gone past the last character
		// of the string, and hence, we are done.
		self.cursor == self.chars.len()
	}
}
