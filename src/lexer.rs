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

/// Whether the character is allowed to start a word.
fn is_word_start(c: &char) -> bool {
	c.is_ascii_alphabetic() || *c == '_'
}

/// Whether the character is allowed to be part of a word.
fn is_word(c: &char) -> bool {
	c.is_ascii_alphanumeric() || *c == '_'
}

/// Whether the character is allowed to start a number.
fn is_number_start(c: &char) -> bool {
	c.is_ascii_digit() || *c == '.'
}

/// Whether the character is allowed to be part of an octal number.
fn is_octal(c: &char) -> bool {
	match c {
		'0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' => true,
		_ => false,
	}
}

/// Whether the character is allowed to start a punctuation.
///
/// Note: The `.` is also caught by the `is_number_start()` function which may execute first.
fn is_punctuation_start(c: &char) -> bool {
	match c {
		'=' | ',' | '.' | ';' | '(' | ')' | '[' | ']' | '{' | '}' | ':'
		| '+' | '-' | '*' | '/' | '%' | '>' | '<' | '!' | '~' | '?' | '&'
		| '|' | '^' => true,
		_ => false,
	}
}

macro_rules! match_op {
	($lexer:ident, $str:expr, $token:expr) => {
		if $lexer.take_pat($str) {
			return $token;
		}
	};
}

/// Matches punctuation.
fn match_punctuation(lexer: &mut Lexer) -> Token {
	match_op!(lexer, "<<=", Token::Op(OpType::LShiftEq));
	match_op!(lexer, ">>=", Token::Op(OpType::RShiftEq));
	match_op!(lexer, "==", Token::Op(OpType::EqEq));
	match_op!(lexer, "!=", Token::Op(OpType::NotEq));
	match_op!(lexer, ">=", Token::Op(OpType::Le));
	match_op!(lexer, "<=", Token::Op(OpType::Ge));
	match_op!(lexer, "&&", Token::Op(OpType::AndAnd));
	match_op!(lexer, "||", Token::Op(OpType::OrOr));
	match_op!(lexer, "++", Token::Op(OpType::AddAdd));
	match_op!(lexer, "--", Token::Op(OpType::SubSub));
	match_op!(lexer, "<<", Token::Op(OpType::LShift));
	match_op!(lexer, ">>", Token::Op(OpType::RShift));
	match_op!(lexer, "+=", Token::Op(OpType::AddEq));
	match_op!(lexer, "-=", Token::Op(OpType::SubEq));
	match_op!(lexer, "*=", Token::Op(OpType::MulEq));
	match_op!(lexer, "/=", Token::Op(OpType::DivEq));
	match_op!(lexer, "%=", Token::Op(OpType::RemEq));
	match_op!(lexer, "&=", Token::Op(OpType::AndEq));
	match_op!(lexer, "|=", Token::Op(OpType::OrEq));
	match_op!(lexer, "^^", Token::Op(OpType::XorXor));
	match_op!(lexer, "^=", Token::Op(OpType::XorEq));
	match_op!(lexer, ";", Token::Semi);
	match_op!(lexer, ".", Token::Dot);
	match_op!(lexer, ",", Token::Comma);
	match_op!(lexer, "=", Token::Eq);
	match_op!(lexer, "(", Token::LParen);
	match_op!(lexer, ")", Token::RParen);
	match_op!(lexer, "[", Token::LBracket);
	match_op!(lexer, "]", Token::RBracket);
	match_op!(lexer, "{", Token::LBrace);
	match_op!(lexer, "}", Token::RBrace);
	match_op!(lexer, ":", Token::Colon);
	match_op!(lexer, "+", Token::Op(OpType::Add));
	match_op!(lexer, "-", Token::Op(OpType::Sub));
	match_op!(lexer, "*", Token::Op(OpType::Mul));
	match_op!(lexer, "/", Token::Op(OpType::Div));
	match_op!(lexer, ">", Token::Op(OpType::Gt));
	match_op!(lexer, "<", Token::Op(OpType::Lt));
	match_op!(lexer, "!", Token::Op(OpType::Not));
	match_op!(lexer, "~", Token::Op(OpType::Flip));
	match_op!(lexer, "?", Token::Question);
	match_op!(lexer, "%", Token::Op(OpType::Rem));
	match_op!(lexer, "&", Token::Op(OpType::And));
	match_op!(lexer, "|", Token::Op(OpType::Or));
	match_op!(lexer, "^", Token::Op(OpType::Xor));
	unreachable!()
}

/// Matches a word to either the `true`/`false` literal, a keyword or an identifier; in that order of precedence.
fn match_word(str: String) -> Token {
	match str.as_ref() {
		// Booleans
		"true" => Token::Bool(true),
		"false" => Token::Bool(false),
		// Keywords
		"if" => Token::If,
		"else" => Token::Else,
		"for" => Token::For,
		"switch" => Token::Switch,
		"case" => Token::Case,
		"default" => Token::Default,
		"break" => Token::Break,
		"return" => Token::Return,
		"discard" => Token::Discard,
		"struct" => Token::Struct,
		// Qualifiers
		"in" => Token::In,
		"out" => Token::Out,
		"inout" => Token::InOut,
		"uniform" => Token::Uniform,
		"buffer" => Token::Buffer,
		"const" => Token::Const,
		"invariant" => Token::Invariant,
		"highp" => Token::Precision,
		"mediump" => Token::Precision,
		"lowp" => Token::Precision,
		"flat" => Token::Interpolation,
		"smooth" => Token::Interpolation,
		"noperspective" => Token::Interpolation,
		"layout" => Token::Layout,
		"location" => Token::Location,
		"component" => Token::Component,
		"origin_upper_left" => Token::FragCoord,
		"pixel_center_integer" => Token::FragCoord,
		"depth_any" => Token::FragDepth,
		"depth_greater" => Token::FragDepth,
		"depth_less" => Token::FragDepth,
		"depth_unchanged" => Token::FragDepth,
		"index" => Token::Index,
		"early_fragment_test" => Token::FragTest,
		// Identifier
		_ => Token::Ident(str),
	}
}

/// Performs lexical analysis of the source string and returns a vector of [`Token`]s.
fn lexer(source: &str) -> Vec<Token> {
	let mut tokens = Vec::new();
	let mut lexer = Lexer::new(source);
	let mut buffer = String::new();
	let mut current = ' ';

	// Any time we want to test the next character, we first `peek()` to see what it is. If it is valid in whatever
	// branch we are in, we can `advance()` the lexer to the next character and repeat the process. If it is
	// invalid (and hence we want to finish this branch and try another one), we don't `advance()` the lexer
	// because we don't want to consume this character; we want to test it against other branches.
	while !lexer.is_done() {
		// Peek the current character.
		current = match lexer.peek() {
			Some(c) => c,
			None => {
				break;
			}
		};

		if is_word_start(&current) {
			buffer.push(current);
			lexer.advance();

			'word: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of the word.
						tokens.push(match_word(std::mem::take(&mut buffer)));
						break 'word;
					}
				};

				// Check if it can be part of a word.
				if is_word(&current) {
					// The character can be part of an word, so consume it and continue looping.
					buffer.push(current);
					lexer.advance();
				} else {
					// The character can't be part of an word, so we can produce a token and exit this loop without
					// consuming it.
					tokens.push(match_word(std::mem::take(&mut buffer)));
					break 'word;
				}
			}
		}
	}

	tokens
}
