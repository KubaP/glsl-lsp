#![allow(unused)]
// Note: The `Hash` derives are only needed because of the chumsky parser.

/// Concrete syntax tree tokens.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token {
	Num {
		num: String,
		suffix: Option<String>,
		type_: NumType,
	},
	Bool(bool),
	Ident(String),
	Directive(String),
	Comment {
		str: String,
		/// Only `true` is this is a `/*...` comment at the end of the file without an ending delimiter.
		contains_eof: bool,
	},
	Invalid(char),
	// Keywords
	If,
	Else,
	For,
	Do,
	While,
	Continue,
	Switch,
	Case,
	Default,
	Break,
	Return,
	Discard,
	Struct,
	Subroutine,
	Reserved(String),
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

/// The different number types/notations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NumType {
	Dec,
	Oct,
	Hex,
	Float,
}

/// Mathematical and comparison operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
	Flip,
	AddAdd,
	SubSub,
	//
	// Comparison
	EqEq,
	NotEq,
	Not,
	Gt,
	Lt,
	Ge,
	Le,
	AndAnd,
	OrOr,
	XorXor,
	//
	// Shunting Yard
	//
	// These variants are never constructed by the Lexer. These are constructed when the shunting yard is looking
	// for prefix/postfix operators and comes across one of the above that is valid. It gets converted into these
	// variants depending on the state of the yard to make the distinction clear when building the ast once the
	// yard has finished.
	Neg,
	AddAddPre,
	AddAddPost,
	SubSubPre,
	SubSubPost,
	GroupStart, // Start of a bracket group
}

pub type Spanned<T> = (T, std::ops::Range<usize>);

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

	/// Peeks the character after the next one without advancing the cursor; (returns the character under `cursor +
	/// 2`).
	fn lookahead_2(&self) -> Option<char> {
		self.chars.get(self.cursor + 2).map(|c| *c)
	}

	/// Advances the cursor by one.
	fn advance(&mut self) {
		self.cursor += 1;
	}

	/// Returns the current character under the cursor and advances the cursor by one.
	///
	/// Equivalent to [`peek()`](Self::peek) followed by [`advance()`](Self::advance).
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

	/// Returns the position of the cursor.
	fn position(&self) -> usize {
		self.cursor
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
	match_op!(lexer, ">=", Token::Op(OpType::Ge));
	match_op!(lexer, "<=", Token::Op(OpType::Le));
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
		"do" => Token::Do,
		"while" => Token::While,
		"continue" => Token::Continue,
		"switch" => Token::Switch,
		"case" => Token::Case,
		"default" => Token::Default,
		"break" => Token::Break,
		"return" => Token::Return,
		"discard" => Token::Discard,
		"struct" => Token::Struct,
		"subroutine" => Token::Subroutine,
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
		// Reserved
		"common" | "partition" | "active" | "asm" | "class" | "union"
		| "enum" | "typedef" | "template" | "this" | "resource" | "goto"
		| "inline" | "noinline" | "public" | "static" | "extern"
		| "external" | "interface" | "long" | "short" | "half" | "fixed"
		| "unsigned" | "superp" | "input" | "output" | "hvec2" | "hvec3"
		| "hvec4" | "fvec2" | "fvec3" | "fvec4" | "sampler3DRect"
		| "filter" | "sizeof" | "cast" | "namespace" | "using" => {
			Token::Reserved(str)
		}
		// Identifier
		_ => Token::Ident(str),
	}
}

/// Matches a line-continuator at the end of a line.
fn match_line_continuator(buffer: &mut String, lexer: &mut Lexer) -> bool {
	let current = lexer.peek().unwrap();

	// Line-continuators begin with `\`.
	if current != '\\' {
		return false;
	}

	if let Some(lookahead) = lexer.lookahead_1() {
		if lookahead == '\n' {
			// We have a `\<\n>`.
			buffer.push('\n');
			lexer.advance();
			lexer.advance();
			return true;
		} else if lookahead == '\r' {
			if let Some(lookahead_2) = lexer.lookahead_2() {
				if lookahead_2 == '\n' {
					// We have a `\<\r><\n>`.
					buffer.push('\r');
					buffer.push('\n');
					lexer.advance();
					lexer.advance();
					lexer.advance();
					return true;
				} else {
					// We have a `\<\r><something else>`
					buffer.push('\r');
					lexer.advance();
					lexer.advance();
					return true;
				}
			} else {
				// We have a `\<\r><eof>`, so this is a defacto line-continuator.
				buffer.push('\r');
				lexer.advance();
				lexer.advance();
				return true;
			}
		} else if lookahead == '\\' {
			// We have `\\` which escapes the `\`. Technically this isn't a line-continuator, but
			// the escaping of a `\` happens in pairs so it makes sense to treat this condition as
			// true and push to the buffer here.
			buffer.push('\\');
			buffer.push('\\');
			lexer.advance();
			lexer.advance();
			return true;
		} else {
			// We have a `\` followed by another character, so this isn't a line-continuator.
			return false;
		}
	} else {
		// We have a `\<eof>`, so this is a defacto line-continuator.
		lexer.advance();
		return true;
	}
}

/// The current state when parsing a number.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NumState {
	/// Parsing either an octal or decimal or a floating point number (depending on what follows).
	Zero,
	/// Parsing a hexadecimal number.
	Hex,
	/// Parsing a decimal number.
	Dec,
	/// Parsing a decimal floating point number.
	Float,
}

/// Performs lexical analysis of the source string and returns a vector of [`Token`]s.
/// 
/// This lexer uses the "Maximal munch" principle to greedily create Tokens. This means the longest possible valid
/// token is always produced. Some examples:
/// 
/// ```text
/// i-- -7 lexes as (--) (-)
/// i-- - --7 lexes as (--) (--) (-)
/// ```
pub fn lexer(source: &str) -> Vec<Spanned<Token>> {
	let mut tokens = Vec::new();
	let mut lexer = Lexer::new(source);
	let mut buffer_start: usize = 0;
	let mut buffer = String::new();
	let mut current = ' ';
	let mut can_start_directive = true;

	// Any time we want to test the next character, we first `peek()` to see what it is. If it is valid in whatever
	// branch we are in, we can `advance()` the lexer to the next character and repeat the process. If it is
	// invalid (and hence we want to finish this branch and try another one), we don't `advance()` the lexer
	// because we don't want to consume this character; we want to test it against other branches.
	//
	// `can_start_directive` is a flag as to whether we can start parsing a directive if we encounter a `#` symbol.
	// After an EOL this is set to `true`. Any branch other than the whitespace branch sets this to `false`. This
	// makes it easy to keep track of when we are allowed to parse a directive, since they must exist at the start
	// of a line barring any whitespace.
	while !lexer.is_done() {
		buffer_start = lexer.position();
		// Peek the current character.
		current = match lexer.peek() {
			Some(c) => c,
			None => {
				break;
			}
		};

		if is_word_start(&current) {
			can_start_directive = false;
			buffer.push(current);
			lexer.advance();

			'word: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of the word.
						tokens.push((
							match_word(std::mem::take(&mut buffer)),
							buffer_start..lexer.position(),
						));
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
					tokens.push((
						match_word(std::mem::take(&mut buffer)),
						buffer_start..lexer.position(),
					));
					break 'word;
				}
			}
		} else if is_number_start(&current) {
			can_start_directive = false;
			// We don't need to worry about having a word character before this first digit character because if
			// there was a word character before, this digit character would be getting parsed as part of the
			// word in the first place, so this branch would not be executing.

			let mut num_buffer = String::new();
			let mut suffix_buffer = None;

			// If we begin with [1-9], we know it's 100% a decimal number. If we begin with `0x`, we know it's 100%
			// a hexadecimal number and we can ignore this prefix as it's not part of the number itself.
			//
			// If we begin with a `0`, however, this can either be:
			// - an octal number (and we need to ignore this prefix later down the line) or,
			// - a decimal number `0` assuming the number ends at the next character or,
			// - it's a floating point which can have a variable amount of `0`s before the decimal point.
			//
			// If we begin with a `.`, we 100% know it's a floating point if there's at least one [0-9] digit
			// afterwards, otherwise this is just a dot token.
			let mut state = if lexer.take_pat("0x") {
				NumState::Hex
			} else if lexer.take_pat("0X") {
				NumState::Hex
			} else if current == '0' {
				// We have a `0`, so either an octal number or a decimal `0` or a floating point.
				num_buffer.push(current);
				lexer.advance();
				NumState::Zero
			} else if current == '.' {
				if let Some(lookahead) = lexer.lookahead_1() {
					if lookahead.is_ascii_digit() {
						// We have a `.` followed by a character that is a floating point digit.
						num_buffer.push(current);
						lexer.advance();
						NumState::Float
					} else {
						// We have a `.` followed by a character that is not a digit, so this must be a punctuation
						// token. We consume the character because otherwise we'd end up back in this branch again.
						lexer.advance();
						tokens
							.push((Token::Dot, buffer_start..lexer.position()));
						continue;
					}
				} else {
					// We have a `.` followed by the end of the source string, so this must be a punctuation token.
					// We consume the character because otherwise we'd end up back in this branch again.
					lexer.advance();
					tokens.push((Token::Dot, buffer_start..lexer.position()));
					continue;
				}
			} else {
				// We have a [1-9] digit, so a decimal number.
				num_buffer.push(current);
				lexer.advance();
				NumState::Dec
			};

			'number: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of the number.
						let type_ = match state {
							NumState::Hex => NumType::Hex,
							NumState::Zero => {
								if num_buffer.as_str() == "0" {
									NumType::Dec
								} else {
									num_buffer.remove(0);
									NumType::Oct
								}
							}
							NumState::Dec => NumType::Dec,
							NumState::Float => NumType::Float,
						};
						tokens.push((
							Token::Num {
								num: num_buffer,
								suffix: suffix_buffer,
								type_,
							},
							buffer_start..lexer.position(),
						));
						break 'number;
					}
				};

				if current == '.' && state == NumState::Hex {
					// If we encounter a `.` and we are parsing a hexadecimal number, that means we've reached the
					// end of this number, and the `.` is a punctuation symbol. We consume the character because
					// otherwise we'd end up back in this branch again.
					tokens.push((
						Token::Num {
							num: num_buffer,
							suffix: suffix_buffer,
							type_: NumType::Hex,
						},
						buffer_start..lexer.position(),
					));
					tokens.push((
						Token::Dot,
						lexer.position()..lexer.position() + 1,
					));
					lexer.advance();
					break 'number;
				}
				if current == '.' && suffix_buffer.is_some() {
					// If we have finished parsing the digits and are now parsing the suffix, that means we've
					// reached the end of the number and this `.` is a punctuation symbol. We consume the character
					// because otherwise we'd end up back in this branch again.
					let type_ = match state {
						NumState::Hex => NumType::Hex,
						NumState::Zero => {
							if num_buffer.as_str() == "0" {
								NumType::Dec
							} else {
								num_buffer.remove(0);
								NumType::Oct
							}
						}
						NumState::Dec => NumType::Dec,
						NumState::Float => NumType::Float,
					};
					tokens.push((
						Token::Num {
							num: num_buffer,
							suffix: suffix_buffer,
							type_,
						},
						buffer_start..lexer.position(),
					));
					tokens.push((
						Token::Dot,
						lexer.position()..lexer.position() + 1,
					));
					lexer.advance();
					break 'number;
				}
				if current == '.'
					&& (state == NumState::Dec || state == NumState::Zero)
				{
					// If we are still parsing the digits of a number beginning with [0-9] and haven't reached a
					// suffix yet, and haven't encountered a `.` yet either, that means this number is a floating
					// point.
					state = NumState::Float;
					num_buffer.push(current);
					lexer.advance();
					continue 'number;
				}
				if current == '.' && state == NumState::Float {
					// If we are still parsing the digits and haven't reached a suffix yet, and have already
					// encountered a `.` before, that means we've reached the end of the number and this `.` is a
					// punctuation symbol. We consume the character because otherwise we'd end up back in this
					// branch again.
					let type_ = match state {
						NumState::Hex => NumType::Hex,
						NumState::Zero => {
							if num_buffer.as_str() == "0" {
								NumType::Dec
							} else {
								num_buffer.remove(0);
								NumType::Oct
							}
						}
						NumState::Dec => NumType::Dec,
						NumState::Float => NumType::Float,
					};
					tokens.push((
						Token::Num {
							num: num_buffer,
							suffix: suffix_buffer,
							type_,
						},
						buffer_start..lexer.position(),
					));
					tokens.push((
						Token::Dot,
						lexer.position()..lexer.position() + 1,
					));
					lexer.advance();
					break 'number;
				}

				if current == 'e' {
					// Note: In the case we encounter an `e` followed by nothing after, that can only be a suffix,
					// so the logic below will deal with that.
					if let Some(lookahead) = lexer.lookahead_1() {
						if lookahead.is_ascii_digit() {
							// We have an `e` followed by a digit, so this is an exponent notation rather than a
							// suffix.
							num_buffer.push(current);
							lexer.advance();
							// If the number isn't already a float, then an exponent makes it one.
							state = NumState::Float;
							continue 'number;
						} else if lookahead == '+' || lookahead == '-' {
							//  We have an `e` followed by a `+`/`-`, so this _may_ be an exponent notation depending
							//  on whether a digit follows.
							if let Some(lookahead_2) = lexer.lookahead_2() {
								if lookahead_2.is_ascii_digit() {
									// We have an `e+`/`e-` followed by a digit, so this is an exponent notation rather
									// than a suffix.
									num_buffer.push(current);
									num_buffer.push(lookahead);
									lexer.advance();
									lexer.advance();
									// If the number isn't already a float, then an exponent makes it one.
									state = NumState::Float;
									continue 'number;
								} else {
									// We have an `e` followed by a `+`/`-` and something that's not a digit after, so
									// this becomes a suffix.
									lexer.advance();
									suffix_buffer = Some(String::from(current));
									let type_ = match state {
										NumState::Hex => NumType::Hex,
										NumState::Zero => {
											if num_buffer.as_str() == "0" {
												NumType::Dec
											} else {
												num_buffer.remove(0);
												NumType::Oct
											}
										}
										NumState::Dec => NumType::Dec,
										NumState::Float => NumType::Float,
									};
									tokens.push((
										Token::Num {
											num: num_buffer,
											suffix: suffix_buffer,
											type_,
										},
										buffer_start..lexer.position(),
									));
									break 'number;
								}
							} else {
								// We have an `e` followed by a `+`/`-` and nothing after, so this becomes a suffix.
								suffix_buffer = Some(String::from(current));
								lexer.advance();
								let type_ = match state {
									NumState::Hex => NumType::Hex,
									NumState::Zero => {
										if num_buffer.as_str() == "0" {
											NumType::Dec
										} else {
											num_buffer.remove(0);
											NumType::Oct
										}
									}
									NumState::Dec => NumType::Dec,
									NumState::Float => NumType::Float,
								};
								tokens.push((
									Token::Num {
										num: num_buffer,
										suffix: suffix_buffer,
										type_,
									},
									buffer_start..lexer.position(),
								));
								break 'number;
							}
						}
					}
				}

				// We want to check for any word characters (and digits of course). This is to follow the spec.
				//
				// Something like `51ufoo` should be parsed as a decimal integer `51` with an invalid postfix
				// `ufoo`, hence why we must be greedy and pick up _any_ word characters.
				if current.is_ascii_hexdigit() || is_word(&current) {
					match state {
						NumState::Zero | NumState::Dec | NumState::Float => {
							if !current.is_ascii_digit()
								&& suffix_buffer.is_none()
							{
								// We have reached the beginning of a word, so flag that we are now parsing the
								// suffix.
								suffix_buffer = Some(String::new());
							}
						}
						NumState::Hex => {
							if !current.is_ascii_hexdigit()
								&& suffix_buffer.is_none()
							{
								// We have reached the beginning of a word, so flag that we are now parsing the
								// suffix.
								suffix_buffer = Some(String::new());
							}
						}
					}

					// Append the character to the appropriate buffer.
					if let Some(suffix) = &mut suffix_buffer {
						suffix.push(current);
					} else {
						num_buffer.push(current);
					}

					lexer.advance();
				} else {
					// The character can't be part of a number, so we can produce a token and exit this loop
					// without consuming it.
					let type_ = match state {
						NumState::Hex => NumType::Hex,
						NumState::Zero => {
							if num_buffer.as_str() == "0" {
								NumType::Dec
							} else {
								num_buffer.remove(0);
								NumType::Oct
							}
						}
						NumState::Dec => NumType::Dec,
						NumState::Float => NumType::Float,
					};
					tokens.push((
						Token::Num {
							num: num_buffer,
							suffix: suffix_buffer,
							type_,
						},
						buffer_start..lexer.position(),
					));
					break 'number;
				}
			}
		} else if is_punctuation_start(&current) {
			can_start_directive = false;
			if lexer.take_pat("//") {
				// If we have a `//`, that means this is a comment until the EOL.
				'line_comment: loop {
					// Peek the current character.
					current = match lexer.peek() {
						Some(c) => c,
						None => {
							// We have reached the end of the source string, and therefore the end of the comment.
							tokens.push((
								Token::Comment {
									str: std::mem::take(&mut buffer),
									contains_eof: false,
								},
								buffer_start..lexer.position(),
							));
							break 'line_comment;
						}
					};

					if match_line_continuator(&mut buffer, &mut lexer) {
						continue 'line_comment;
					} else if current == '\r' || current == '\n' {
						// We have an EOL without a line-continuator, so therefore this is the end of the directive.
						tokens.push((
							Token::Comment {
								str: std::mem::take(&mut buffer),
								contains_eof: false,
							},
							buffer_start..lexer.position(),
						));
						break 'line_comment;
					} else {
						// Any other character is just added to the comment buffer.
						buffer.push(current);
						lexer.advance();
					}
				}
			} else if lexer.take_pat("/*") {
				// If we have a `/*`, that means this is a comment until the first `*/`
				'comment: loop {
					// Test if the end delimiter is here.
					if lexer.take_pat("*/") {
						tokens.push((
							Token::Comment {
								str: std::mem::take(&mut buffer),
								contains_eof: false,
							},
							buffer_start..lexer.position(),
						));
						break 'comment;
					}

					// Continue pushing any characters into the buffer.
					if let Some(char) = lexer.next() {
						buffer.push(char);
					} else {
						// We have reached the end of the source string, and therefore the end of the comment. This
						// comment however therefore contains the EOF and hence is not valid.
						tokens.push((
							Token::Comment {
								str: std::mem::take(&mut buffer),
								contains_eof: true,
							},
							buffer_start..lexer.position(),
						));
						break 'comment;
					}
				}
			} else {
				tokens.push((
					match_punctuation(&mut lexer),
					buffer_start..lexer.position(),
				));
			}
		} else if current.is_whitespace() {
			// Check for an EOL, to reset the directive parsing flag.
			if current == '\n' || current == '\r' {
				can_start_directive = true;
			}
			// We ignore whitespace characters.
			lexer.advance();
		} else if can_start_directive && current == '#' {
			lexer.advance();

			'directive: loop {
				// Peek the current character.
				current = match lexer.peek() {
					Some(c) => c,
					None => {
						// We have reached the end of the source string, and therefore the end of the comment.
						tokens.push((
							Token::Directive(std::mem::take(&mut buffer)),
							buffer_start..lexer.position(),
						));
						break 'directive;
					}
				};

				if match_line_continuator(&mut buffer, &mut lexer) {
					continue 'directive;
				} else if current == '\r' || current == '\n' {
					// We have an EOL without a line-continuator, so therefore this is the end of the directive.
					tokens.push((
						Token::Directive(std::mem::take(&mut buffer)),
						buffer_start..lexer.position(),
					));
					break 'directive;
				} else {
					// Any other character is just added to the comment buffer.
					buffer.push(current);
					lexer.advance();
				}
			}
		} else {
			// This character isn't valid to start any token.
			lexer.advance();
			tokens.push((
				Token::Invalid(current),
				buffer_start..lexer.position(),
			));
		}
	}

	tokens
}

#[test]
#[rustfmt::skip]
fn spans() {
	// Identifiers/keywords
	assert_eq!(lexer("return"), vec![(Token::Return, 0..6)]);
	assert_eq!(lexer("break "), vec![(Token::Break, 0..5)]);
	assert_eq!(lexer("return break"), vec![(Token::Return, 0..6), (Token::Break, 7..12)]);
	// Punctuation
	assert_eq!(lexer(";"), vec![(Token::Semi, 0..1)]);
	assert_eq!(lexer(": "), vec![(Token::Colon, 0..1)]);
	assert_eq!(lexer("; :"), vec![(Token::Semi, 0..1), (Token::Colon, 2..3)]);
	// Comments
	assert_eq!(lexer("// comment"), vec![(Token::Comment { str: " comment".into(), contains_eof: false }, 0..10)]);
	assert_eq!(lexer("/* a */"), vec![(Token::Comment { str: " a ".into(), contains_eof: false }, 0..7)]);
	assert_eq!(lexer("/* a"), vec![(Token::Comment { str: " a".into(), contains_eof: true }, 0..4)]);
	// Directive
	assert_eq!(lexer("#dir"), vec![(Token::Directive("dir".into()), 0..4)]);
	assert_eq!(lexer("#dir a "), vec![(Token::Directive("dir a ".into()), 0..7)]);
	// Invalid
	assert_eq!(lexer("@"), vec![(Token::Invalid('@'), 0..1)]);
	assert_eq!(lexer("¬"), vec![(Token::Invalid('¬'), 0..1)]);
	assert_eq!(lexer("@  ¬"), vec![(Token::Invalid('@'), 0..1), (Token::Invalid('¬'), 3..4)]);
	// Numbers
	assert_eq!(lexer("."), vec![(Token::Dot, 0..1)]);
	assert_eq!(lexer(". "), vec![(Token::Dot, 0..1)]);
	assert_eq!(lexer("0xF."), vec![(Token::Num { num: "F".into(), suffix: None, type_: NumType::Hex }, 0..3), (Token::Dot, 3..4)]);
	assert_eq!(lexer("123u."), vec![(Token::Num { num: "123".into(), suffix: Some("u".into()), type_: NumType::Dec }, 0..4), (Token::Dot, 4..5)]);
	assert_eq!(lexer("1.2."), vec![(Token::Num { num: "1.2".into(), suffix: None, type_: NumType::Float }, 0..3), (Token::Dot, 3..4)]);
	assert_eq!(lexer("1.2."), vec![(Token::Num { num: "1.2".into(), suffix: None, type_: NumType::Float }, 0..3), (Token::Dot, 3..4)]);
	assert_eq!(lexer("1e"), vec![(Token::Num { num: "1".into(), suffix: Some("e".into()), type_: NumType::Dec }, 0..2)]);
	assert_eq!(lexer("123 "), vec![(Token::Num { num: "123".into(), suffix: None, type_: NumType::Dec }, 0..3)]);
	assert_eq!(lexer("1e+="), vec![(Token::Num { num: "1".into(), suffix: Some("e".into()), type_: NumType::Dec }, 0..2), (Token::Op(OpType::AddEq), 2..4)]);
	assert_eq!(lexer("1e+"), vec![(Token::Num { num: "1".into(), suffix: Some("e".into()), type_: NumType::Dec }, 0..2), (Token::Op(OpType::Add), 2..3)]);
}

/// Asserts the token output of the `lexer()` matches the right hand side; ignores the spans.
#[allow(unused_macros)]
macro_rules! assert_tokens {
    ($src:expr, $($token:expr),*) => {
		let output = lexer($src).into_iter().map(|(t, s)| t).collect::<Vec<_>>();
        assert_eq!(output, vec![
            $(
                $token,
            )*
        ])
    };
}

#[test]
fn identifiers() {
	assert_tokens!("ident", Token::Ident("ident".into()));
	assert_tokens!("gl_something", Token::Ident("gl_something".into()));
	assert_tokens!("id_145", Token::Ident("id_145".into()));
	assert_tokens!("_9ga", Token::Ident("_9ga".into()));
}

#[test]
fn keywords() {
	assert_tokens!("true", Token::Bool(true));
	assert_tokens!("false", Token::Bool(false));
	assert_tokens!("if", Token::If);
	assert_tokens!("else", Token::Else);
	assert_tokens!("for", Token::For);
	assert_tokens!("do", Token::Do);
	assert_tokens!("while", Token::While);
	assert_tokens!("continue", Token::Continue);
	assert_tokens!("switch", Token::Switch);
	assert_tokens!("case", Token::Case);
	assert_tokens!("default", Token::Default);
	assert_tokens!("break", Token::Break);
	assert_tokens!("return", Token::Return);
	assert_tokens!("discard", Token::Discard);
	assert_tokens!("struct", Token::Struct);
	assert_tokens!("subroutine", Token::Subroutine);
	assert_tokens!("in", Token::In);
	assert_tokens!("out", Token::Out);
	assert_tokens!("inout", Token::InOut);
	assert_tokens!("uniform", Token::Uniform);
	assert_tokens!("buffer", Token::Buffer);
	assert_tokens!("const", Token::Const);
	assert_tokens!("invariant", Token::Invariant);
	assert_tokens!("highp", Token::Precision);
	assert_tokens!("mediump", Token::Precision);
	assert_tokens!("lowp", Token::Precision);
	assert_tokens!("flat", Token::Interpolation);
	assert_tokens!("smooth", Token::Interpolation);
	assert_tokens!("noperspective", Token::Interpolation);
	assert_tokens!("layout", Token::Layout);
	assert_tokens!("location", Token::Location);
	assert_tokens!("component", Token::Component);
	assert_tokens!("origin_upper_left", Token::FragCoord);
	assert_tokens!("pixel_center_integer", Token::FragCoord);
	assert_tokens!("depth_any", Token::FragDepth);
	assert_tokens!("depth_greater", Token::FragDepth);
	assert_tokens!("depth_less", Token::FragDepth);
	assert_tokens!("depth_unchanged", Token::FragDepth);
	assert_tokens!("index", Token::Index);
	assert_tokens!("early_fragment_test", Token::FragTest);
	// Reserved
	assert_tokens!("common", Token::Reserved("common".into()));
	assert_tokens!("partition", Token::Reserved("partition".into()));
	assert_tokens!("active", Token::Reserved("active".into()));
	assert_tokens!("asm", Token::Reserved("asm".into()));
	assert_tokens!("class", Token::Reserved("class".into()));
	assert_tokens!("union", Token::Reserved("union".into()));
	assert_tokens!("enum", Token::Reserved("enum".into()));
	assert_tokens!("typedef", Token::Reserved("typedef".into()));
	assert_tokens!("template", Token::Reserved("template".into()));
	assert_tokens!("this", Token::Reserved("this".into()));
	assert_tokens!("resource", Token::Reserved("resource".into()));
	assert_tokens!("goto", Token::Reserved("goto".into()));
	assert_tokens!("inline", Token::Reserved("inline".into()));
	assert_tokens!("noinline", Token::Reserved("noinline".into()));
	assert_tokens!("public", Token::Reserved("public".into()));
	assert_tokens!("static", Token::Reserved("static".into()));
	assert_tokens!("extern", Token::Reserved("extern".into()));
	assert_tokens!("external", Token::Reserved("external".into()));
	assert_tokens!("interface", Token::Reserved("interface".into()));
	assert_tokens!("long", Token::Reserved("long".into()));
	assert_tokens!("short", Token::Reserved("short".into()));
	assert_tokens!("half", Token::Reserved("half".into()));
	assert_tokens!("fixed", Token::Reserved("fixed".into()));
	assert_tokens!("unsigned", Token::Reserved("unsigned".into()));
	assert_tokens!("superp", Token::Reserved("superp".into()));
	assert_tokens!("input", Token::Reserved("input".into()));
	assert_tokens!("output", Token::Reserved("output".into()));
	assert_tokens!("hvec2", Token::Reserved("hvec2".into()));
	assert_tokens!("hvec3", Token::Reserved("hvec3".into()));
	assert_tokens!("hvec4", Token::Reserved("hvec4".into()));
	assert_tokens!("fvec2", Token::Reserved("fvec2".into()));
	assert_tokens!("fvec3", Token::Reserved("fvec3".into()));
	assert_tokens!("fvec4", Token::Reserved("fvec4".into()));
	assert_tokens!("sampler3DRect", Token::Reserved("sampler3DRect".into()));
	assert_tokens!("filter", Token::Reserved("filter".into()));
	assert_tokens!("sizeof", Token::Reserved("sizeof".into()));
	assert_tokens!("cast", Token::Reserved("cast".into()));
	assert_tokens!("namespace", Token::Reserved("namespace".into()));
	assert_tokens!("using", Token::Reserved("using".into()));
}

#[test]
fn punctuation() {
	assert_tokens!(";", Token::Semi);
	assert_tokens!(".", Token::Dot);
	assert_tokens!(",", Token::Comma);
	assert_tokens!("=", Token::Eq);
	assert_tokens!("(", Token::LParen);
	assert_tokens!(")", Token::RParen);
	assert_tokens!("[", Token::LBracket);
	assert_tokens!("]", Token::RBracket);
	assert_tokens!("{", Token::LBrace);
	assert_tokens!("}", Token::RBrace);
	assert_tokens!(":", Token::Colon);
	assert_tokens!("+", Token::Op(OpType::Add));
	assert_tokens!("-", Token::Op(OpType::Sub));
	assert_tokens!("*", Token::Op(OpType::Mul));
	assert_tokens!("/", Token::Op(OpType::Div));
	assert_tokens!(">", Token::Op(OpType::Gt));
	assert_tokens!("<", Token::Op(OpType::Lt));
	assert_tokens!("!", Token::Op(OpType::Not));
	assert_tokens!("~", Token::Op(OpType::Flip));
	assert_tokens!("?", Token::Question);
	assert_tokens!("%", Token::Op(OpType::Rem));
	assert_tokens!("&", Token::Op(OpType::And));
	assert_tokens!("|", Token::Op(OpType::Or));
	assert_tokens!("^", Token::Op(OpType::Xor));
	assert_tokens!("==", Token::Op(OpType::EqEq));
	assert_tokens!("!=", Token::Op(OpType::NotEq));
	assert_tokens!(">=", Token::Op(OpType::Ge));
	assert_tokens!("<=", Token::Op(OpType::Le));
	assert_tokens!("&&", Token::Op(OpType::AndAnd));
	assert_tokens!("||", Token::Op(OpType::OrOr));
	assert_tokens!("^^", Token::Op(OpType::XorXor));
	assert_tokens!("++", Token::Op(OpType::AddAdd));
	assert_tokens!("--", Token::Op(OpType::SubSub));
	assert_tokens!("<<", Token::Op(OpType::LShift));
	assert_tokens!(">>", Token::Op(OpType::RShift));
	assert_tokens!("+=", Token::Op(OpType::AddEq));
	assert_tokens!("-=", Token::Op(OpType::SubEq));
	assert_tokens!("*=", Token::Op(OpType::MulEq));
	assert_tokens!("/=", Token::Op(OpType::DivEq));
	assert_tokens!("%=", Token::Op(OpType::RemEq));
	assert_tokens!("&=", Token::Op(OpType::AndEq));
	assert_tokens!("|=", Token::Op(OpType::OrEq));
	assert_tokens!("^=", Token::Op(OpType::XorEq));
	assert_tokens!("<<=", Token::Op(OpType::LShiftEq));
	assert_tokens!(">>=", Token::Op(OpType::RShiftEq));
}

#[test]
#[rustfmt::skip]
fn comments() {
	// Line comments
	assert_tokens!("// a comment", Token::Comment{str: " a comment".into(), contains_eof: false});
	assert_tokens!("//a comment", Token::Comment{str: "a comment".into(), contains_eof: false});
	assert_tokens!("//a comment \\", Token::Comment{str: "a comment ".into(), contains_eof: false});
	assert_tokens!("//a comment \\\\", Token::Comment{str: "a comment \\\\".into(), contains_eof: false});
	assert_tokens!("//a comment \\n", Token::Comment{str: "a comment \\n".into(), contains_eof: false});
	assert_tokens!("//a comment \\\r\n continuation", Token::Comment{str: "a comment \r\n continuation".into(), contains_eof: false});
	assert_tokens!("// a comment \\\r continuation", Token::Comment{str: " a comment \r continuation".into(), contains_eof: false});
	assert_tokens!("//a comment\\\ncontinuation", Token::Comment{str: "a comment\ncontinuation".into(), contains_eof: false});
	// Multi-line comments
	assert_tokens!("/* a comment */", Token::Comment{ str: " a comment ".into(), contains_eof: false});
	assert_tokens!("/*a comment*/", Token::Comment{ str: "a comment".into(), contains_eof: false});
	assert_tokens!("/* <Ll#,;#l,_!\"^$!6 */", Token::Comment{ str: " <Ll#,;#l,_!\"^$!6 ".into(), contains_eof: false});
	assert_tokens!("/* open-ended comment", Token::Comment{ str: " open-ended comment".into(), contains_eof: true});
}

#[test]
#[rustfmt::skip]
fn integers(){
	// Zero
	assert_tokens!("0", Token::Num{num: "0".into(), suffix: None, type_: NumType::Dec});
	// Zero with suffix
	assert_tokens!("0u", Token::Num{num: "0".into(), suffix: Some("u".into()), type_: NumType::Dec});
	// Decimal
	assert_tokens!("1", Token::Num{num: "1".into(), suffix: None, type_: NumType::Dec});
	assert_tokens!("123456", Token::Num{num: "123456".into(), suffix: None, type_: NumType::Dec});
	assert_tokens!("100008", Token::Num{num: "100008".into(), suffix: None,  type_: NumType::Dec});
	// Decimal with suffix
	assert_tokens!("1u", Token::Num{num: "1".into(), suffix: Some("u".into()), type_: NumType::Dec});
	assert_tokens!("123456u", Token::Num{num: "123456".into(), suffix: Some("u".into()), type_: NumType::Dec});
	assert_tokens!("100008u", Token::Num{num: "100008".into(), suffix: Some("u".into()),  type_: NumType::Dec});
	// Octal
	assert_tokens!("00", Token::Num{num: "0".into(), suffix: None,  type_: NumType::Oct});
	assert_tokens!("01715", Token::Num{num: "1715".into(), suffix: None,  type_: NumType::Oct});
	assert_tokens!("09183", Token::Num{num: "9183".into(), suffix: None, type_: NumType::Oct});
	// Octal with suffix
	assert_tokens!("00u", Token::Num{num: "0".into(), suffix: Some("u".into()),  type_: NumType::Oct});
	assert_tokens!("01715u", Token::Num{num: "1715".into(), suffix: Some("u".into()),  type_: NumType::Oct});
	assert_tokens!("09183u", Token::Num{num: "9183".into(), suffix: Some("u".into()), type_: NumType::Oct});
	// Hexadecimal
	assert_tokens!("0x", Token::Num{num: "".into(), suffix: None, type_: NumType::Hex});
	assert_tokens!("0x91fa", Token::Num{num: "91fa".into(), suffix: None,  type_: NumType::Hex});
	assert_tokens!("0x00F", Token::Num{num: "00F".into(), suffix: None,  type_: NumType::Hex});
	// Hexadecimal with suffix
	assert_tokens!("0xu", Token::Num{num: "".into(), suffix: Some("u".into()), type_: NumType::Hex});
	assert_tokens!("0x91fau", Token::Num{num: "91fa".into(), suffix: Some("u".into()),  type_: NumType::Hex});
	assert_tokens!("0x00Fu", Token::Num{num: "00F".into(), suffix: Some("u".into()),  type_: NumType::Hex});
}

#[test]
#[rustfmt::skip]
fn floats() {
	// Zeroes
	assert_tokens!("0.0", Token::Num{num: "0.0".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.", Token::Num{num: "0.".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".0", Token::Num{num: ".0".into(), suffix: None, type_: NumType::Float});
	// Zeroes with suffix
	assert_tokens!("0.0lf", Token::Num{num: "0.0".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.lf", Token::Num{num: "0.".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".0lf", Token::Num{num: ".0".into(), suffix: Some("lf".into()), type_: NumType::Float});
	// Zeroes with exponent
	assert_tokens!("0e7", Token::Num{num: "0e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0e+7", Token::Num{num: "0e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0e-7", Token::Num{num: "0e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.0e7", Token::Num{num: "0.0e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.0e+7", Token::Num{num: "0.0e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.0e-7", Token::Num{num: "0.0e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.e7", Token::Num{num: "0.e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.e+7", Token::Num{num: "0.e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("0.e-7", Token::Num{num: "0.e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".0e7", Token::Num{num: ".0e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".0e+7", Token::Num{num: ".0e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".0e-7", Token::Num{num: ".0e-7".into(), suffix: None, type_: NumType::Float});
	// Zeroes with exponent and suffix
	assert_tokens!("0e7lf", Token::Num{num: "0e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0e+7lf", Token::Num{num: "0e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0e-7lf", Token::Num{num: "0e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.0e7lf", Token::Num{num: "0.0e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.0e+7lf", Token::Num{num: "0.0e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.0e-7lf", Token::Num{num: "0.0e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.e7lf", Token::Num{num: "0.e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.e+7lf", Token::Num{num: "0.e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("0.e-7lf", Token::Num{num: "0.e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".0e7lf", Token::Num{num: ".0e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".0e+7lf", Token::Num{num: ".0e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".0e-7lf", Token::Num{num: ".0e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	// Digits
	assert_tokens!("1.0", Token::Num{num: "1.0".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.1", Token::Num{num: "1.1".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.", Token::Num{num: "1.".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".1", Token::Num{num: ".1".into(), suffix: None, type_: NumType::Float});
	// Digits with suffix
	assert_tokens!("1.0lf", Token::Num{num: "1.0".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.1lf", Token::Num{num: "1.1".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.lf", Token::Num{num: "1.".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".1lf", Token::Num{num: ".1".into(), suffix: Some("lf".into()), type_: NumType::Float});
	// Digits with exponent
	assert_tokens!("1e7", Token::Num{num: "1e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1e+7", Token::Num{num: "1e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1e-7", Token::Num{num: "1e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.0e7", Token::Num{num: "1.0e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.0e+7", Token::Num{num: "1.0e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.0e-7", Token::Num{num: "1.0e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.1e7", Token::Num{num: "1.1e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.1e+7", Token::Num{num: "1.1e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.1e-7", Token::Num{num: "1.1e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.e7", Token::Num{num: "1.e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.e+7", Token::Num{num: "1.e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!("1.e-7", Token::Num{num: "1.e-7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".1e7", Token::Num{num: ".1e7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".1e+7", Token::Num{num: ".1e+7".into(), suffix: None, type_: NumType::Float});
	assert_tokens!(".1e-7", Token::Num{num: ".1e-7".into(), suffix: None, type_: NumType::Float});
	// Digits with exponent and suffix
	assert_tokens!("1e7lf", Token::Num{num: "1e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1e+7lf", Token::Num{num: "1e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1e-7lf", Token::Num{num: "1e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.0e7lf", Token::Num{num: "1.0e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.0e+7lf", Token::Num{num: "1.0e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.0e-7lf", Token::Num{num: "1.0e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.1e7lf", Token::Num{num: "1.1e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.1e+7lf", Token::Num{num: "1.1e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.1e-7lf", Token::Num{num: "1.1e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.e7lf", Token::Num{num: "1.e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.e+7lf", Token::Num{num: "1.e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!("1.e-7lf", Token::Num{num: "1.e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".1e7lf", Token::Num{num: ".1e7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".1e+7lf", Token::Num{num: ".1e+7".into(), suffix: Some("lf".into()), type_: NumType::Float});
	assert_tokens!(".1e-7lf", Token::Num{num: ".1e-7".into(), suffix: Some("lf".into()), type_: NumType::Float});
}

#[test]
#[rustfmt::skip]
fn directives(){
	assert_tokens!("#directive", Token::Directive("directive".into()));
	assert_tokens!("#   directive", Token::Directive("   directive".into()));
	assert_tokens!("#directive args", Token::Directive("directive args".into()));
	assert_tokens!("  #directive", Token::Directive("directive".into()));
	assert_tokens!("\t#directive", Token::Directive("directive".into()));
	assert_tokens!("#directive\\", Token::Directive("directive".into()));
	assert_tokens!("#directive \\\\", Token::Directive("directive \\\\".into()));
	assert_tokens!("#directive \\n", Token::Directive("directive \\n".into()));
	assert_tokens!("#directive \\\r\n args", Token::Directive("directive \r\n args".into()));
	assert_tokens!("#  directive \\\r args", Token::Directive("  directive \r args".into()));
	assert_tokens!("#directive\\\nargs", Token::Directive("directive\nargs".into()));
	assert_tokens!("#", Token::Directive("".into()));
	assert_tokens!("   #", Token::Directive("".into()));
}

#[test]
#[rustfmt::skip]
fn illegal(){
	// Note: All of these characters will be parsed as part of a preprocessor directive string; only later once the
	// string is tokenised will any errors come up.
	assert_tokens!("@", Token::Invalid('@'));
	assert_tokens!("¬", Token::Invalid('¬'));
	assert_tokens!("`", Token::Invalid('`'));
	assert_tokens!("¦", Token::Invalid('¦'));
	assert_tokens!("'", Token::Invalid('\''));
	assert_tokens!("\"", Token::Invalid('"'));
	assert_tokens!("£", Token::Invalid('£'));
	assert_tokens!("$", Token::Invalid('$'));
	assert_tokens!("€", Token::Invalid('€'));
}
