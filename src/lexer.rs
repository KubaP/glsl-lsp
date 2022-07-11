use crate::{
	ast::{Expr, Layout},
	span::{Span, Spanned},
	Either,
};

#[cfg(test)]
use crate::span::span;

/// Lexer tokens.
#[derive(Debug, Clone, PartialEq, Eq)]
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
	// General keywords
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
	// Qualifier keywords
	Const,
	In,
	Out,
	InOut,
	Attribute,
	Uniform,
	Varying,
	Buffer,
	Shared,
	Centroid,
	Sample,
	Patch,
	Layout,
	Flat,
	Smooth,
	NoPerspective,
	HighP,
	MediumP,
	LowP,
	Invariant,
	Precise,
	Coherent,
	Volatile,
	Restrict,
	Readonly,
	Writeonly,
	// Punctuation
	Op(OpTy),
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

impl Token {
	/// Returns whether the current `Token` is a keyword that can start a statement.
	pub fn starts_statement(&self) -> bool {
		match self {
			Self::If
			| Self::Else
			| Self::For
			| Self::Do
			| Self::While
			| Self::Continue
			| Self::Switch
			| Self::Case
			| Self::Default
			| Self::Break
			| Self::Return
			| Self::Discard
			| Self::Struct
			| Self::Subroutine
			| Self::Reserved(_)
			| Self::Const
			| Self::In
			| Self::Out
			| Self::InOut
			| Self::Attribute
			| Self::Uniform
			| Self::Varying
			| Self::Buffer
			| Self::Shared
			| Self::Centroid
			| Self::Sample
			| Self::Patch
			| Self::Layout
			| Self::Flat
			| Self::Smooth
			| Self::NoPerspective
			| Self::HighP
			| Self::MediumP
			| Self::LowP
			| Self::Invariant
			| Self::Precise
			| Self::Coherent
			| Self::Volatile
			| Self::Restrict
			| Self::Readonly
			| Self::Writeonly => true,
			_ => false,
		}
	}

	/// Returns whether the current `Token` is a qualifier, or in the case of `layout`, whether it starts a
	/// qualifier (since a layout has a parenthesis group after it).
	pub fn is_qualifier(&self) -> bool {
		match self {
			Self::Const
			| Self::In
			| Self::Out
			| Self::InOut
			| Self::Attribute
			| Self::Uniform
			| Self::Varying
			| Self::Buffer
			| Self::Shared
			| Self::Centroid
			| Self::Sample
			| Self::Patch
			| Self::Layout
			| Self::Flat
			| Self::Smooth
			| Self::NoPerspective
			| Self::HighP
			| Self::MediumP
			| Self::LowP
			| Self::Invariant
			| Self::Precise
			| Self::Coherent
			| Self::Volatile
			| Self::Restrict
			| Self::Readonly
			| Self::Writeonly => true,
			_ => false,
		}
	}

	/// Tries to convert the current `Token` into a [`Layout`] identifier.
	/// 
	/// If the token matches a layout identifier that doesn't take an expression, e.g. `early_fragment_tests`, then
	/// `Left` is returned with the converted `Layout`. If the token matches a layout identifier that takes an
	/// expression, e.g. `location = n`, then `Right` is returned with a constructor for the appropriate `Layout`
	/// (the constructor takes the expression once that has been parsed).
	/// 
	/// If `None` is returned, the current token is not a valid layout identifier.
	pub fn to_layout(&self) -> Option<Either<Layout, fn(Expr) -> Layout>> {
		match self {
			// `shared` is a keyword in all circumstances, apart from when it is used as a qualifier, hence it's a
			// distinct variant rather than a string.
			Self::Shared => Some(Either::Left(Layout::Shared)),
			Self::Ident(s) => match s.as_ref() {
				"packed" => Some(Either::Left(Layout::Packed)),
				"std140" => Some(Either::Left(Layout::Std140)),
				"std430" => Some(Either::Left(Layout::Std430)),
				"row_major" => Some(Either::Left(Layout::RowMajor)),
				"column_major" => Some(Either::Left(Layout::ColumnMajor)),
				"binding" => Some(Either::Right(Layout::Binding)),
				"offset" => Some(Either::Right(Layout::Offset)),
				"align" => Some(Either::Right(Layout::Align)),
				"location" => Some(Either::Right(Layout::Location)),
				"component" => Some(Either::Right(Layout::Component)),
				"index" => Some(Either::Right(Layout::Index)),
				"points" => Some(Either::Left(Layout::Points)),
				"lines" => Some(Either::Left(Layout::Lines)),
				"isolines" => Some(Either::Left(Layout::Isolines)),
				"triangles" => Some(Either::Left(Layout::Triangles)),
				"quads" => Some(Either::Left(Layout::Quads)),
				"equal_spacing" => Some(Either::Left(Layout::EqualSpacing)),
				"fractional_even_spacing" => {
					Some(Either::Left(Layout::FractionalEvenSpacing))
				}
				"fractional_odd_spacing" => {
					Some(Either::Left(Layout::FractionalOddSpacing))
				}
				"cw" => Some(Either::Left(Layout::Clockwise)),
				"ccw" => Some(Either::Left(Layout::CounterClockwise)),
				"point_mode" => Some(Either::Left(Layout::PointMode)),
				"line_adjacency" => Some(Either::Left(Layout::LinesAdjacency)),
				"triangle_adjacency" => {
					Some(Either::Left(Layout::TrianglesAdjacency))
				}
				"invocations" => Some(Either::Right(Layout::Invocations)),
				"origin_upper_left" => {
					Some(Either::Left(Layout::OriginUpperLeft))
				}
				"pixel_center_integer" => {
					Some(Either::Left(Layout::PixelCenterInteger))
				}
				"early_fragment_tests" => {
					Some(Either::Left(Layout::EarlyFragmentTests))
				}
				"local_size_x" => Some(Either::Right(Layout::LocalSizeX)),
				"local_size_y" => Some(Either::Right(Layout::LocalSizeY)),
				"local_size_z" => Some(Either::Right(Layout::LocalSizeZ)),
				"xfb_buffer" => Some(Either::Right(Layout::XfbBuffer)),
				"xfb_stride" => Some(Either::Right(Layout::XfbStride)),
				"xfb_offset" => Some(Either::Right(Layout::XfbOffset)),
				"vertices" => Some(Either::Right(Layout::Vertices)),
				"line_strip" => Some(Either::Left(Layout::LineStrip)),
				"triangle_strip" => Some(Either::Left(Layout::TriangleStrip)),
				"max_vertices" => Some(Either::Right(Layout::MaxVertices)),
				"stream" => Some(Either::Right(Layout::Stream)),
				"depth_any" => Some(Either::Left(Layout::DepthAny)),
				"depth_greater" => Some(Either::Left(Layout::DepthGreater)),
				"depth_less" => Some(Either::Left(Layout::DepthLess)),
				"depth_unchanged" => Some(Either::Left(Layout::DepthUnchanged)),
				_ => None,
			},
			_ => None,
		}
	}
}

/// The different number types/notations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumType {
	Dec,
	Oct,
	Hex,
	Float,
}

/// Mathematical and comparison operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpTy {
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
	Neg,
	Flip,
	Eq,
	AddAdd,
	SubSub,
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
	// for prefix/postfix operators and comes across one of the above ambiguous operators. It gets converted into
	// these variants depending on the state of the yard to make the distinction clear when building the ast.
	//
	// The reason these variants are in this type is because the shunting yard stores this type in its stack. It
	// makes more sense to add these variants to this type rather than to create a new subtype which includes all
	// of the above plus these variants. Furthermore these operators in the shunting yard stack are later converted
	// to `ast::Expr` which stores this type.
	AddAddPre,
	AddAddPost,
	SubSubPre,
	SubSubPost,
	/// Parenthesis group.
	/// 
	/// The `Span`s represent the spans for the left and right parenthesis. The reason this group has this but
	/// other groups don't is for the following:
	/// 
	/// `Paren` groups may be closed as valid even if missing the closing `)`, hence when we collapse a parenthesis
	/// group and emit this token onto the shunting yard stack, we need to figure out these spans there and then,
	/// because afterwards this information gets lost. The only other group which can be collapsed at the end of
	/// the parse is the `List` group, but that doesn't have any delimiters. All other groups get invalidated if
	/// they're open so there's no need for extra tracking.
	Paren(Span, Span),
	/// Index operator. `bool` notes whether there is a node within the `[...]` brackets.
	Index(bool),
	/// Object access operator.
	ObjAccess,
	/// Function call. Consumes the `usize` amount of nodes as arguments for the function call. The first node is
	/// guaranteed to be an `Expr::Ident` which is the function identifier.
	FnCall(usize),
	/// Initializer list. Consumes the `usize` amount of nodes as arguments for the initializer list.
	Init(usize),
	/// Array constructor. Consumes the `usize` amount of nodes as arguments for the function call. The first node
	/// is guaranteed to be a `Expr::Index` which is the array constructor type.
	ArrInit(usize),
	/// A list, e.g. `a, b`. Consumes the `usize` amount of nodes as arguments for the list.
	List(usize),
	// The following are never present in the final output of the shunting yard; just stored temporarily.
	BracketStart,
	FnStart,
	IndexStart,
	InitStart,
	ArrInitStart,
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
#[allow(unused)]
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
	match_op!(lexer, "<<=", Token::Op(OpTy::LShiftEq));
	match_op!(lexer, ">>=", Token::Op(OpTy::RShiftEq));
	match_op!(lexer, "==", Token::Op(OpTy::EqEq));
	match_op!(lexer, "!=", Token::Op(OpTy::NotEq));
	match_op!(lexer, ">=", Token::Op(OpTy::Ge));
	match_op!(lexer, "<=", Token::Op(OpTy::Le));
	match_op!(lexer, "&&", Token::Op(OpTy::AndAnd));
	match_op!(lexer, "||", Token::Op(OpTy::OrOr));
	match_op!(lexer, "++", Token::Op(OpTy::AddAdd));
	match_op!(lexer, "--", Token::Op(OpTy::SubSub));
	match_op!(lexer, "<<", Token::Op(OpTy::LShift));
	match_op!(lexer, ">>", Token::Op(OpTy::RShift));
	match_op!(lexer, "+=", Token::Op(OpTy::AddEq));
	match_op!(lexer, "-=", Token::Op(OpTy::SubEq));
	match_op!(lexer, "*=", Token::Op(OpTy::MulEq));
	match_op!(lexer, "/=", Token::Op(OpTy::DivEq));
	match_op!(lexer, "%=", Token::Op(OpTy::RemEq));
	match_op!(lexer, "&=", Token::Op(OpTy::AndEq));
	match_op!(lexer, "|=", Token::Op(OpTy::OrEq));
	match_op!(lexer, "^^", Token::Op(OpTy::XorXor));
	match_op!(lexer, "^=", Token::Op(OpTy::XorEq));
	match_op!(lexer, "=", Token::Op(OpTy::Eq));
	match_op!(lexer, ";", Token::Semi);
	match_op!(lexer, ".", Token::Dot);
	match_op!(lexer, ",", Token::Comma);
	match_op!(lexer, "(", Token::LParen);
	match_op!(lexer, ")", Token::RParen);
	match_op!(lexer, "[", Token::LBracket);
	match_op!(lexer, "]", Token::RBracket);
	match_op!(lexer, "{", Token::LBrace);
	match_op!(lexer, "}", Token::RBrace);
	match_op!(lexer, ":", Token::Colon);
	match_op!(lexer, "+", Token::Op(OpTy::Add));
	match_op!(lexer, "-", Token::Op(OpTy::Sub));
	match_op!(lexer, "*", Token::Op(OpTy::Mul));
	match_op!(lexer, "/", Token::Op(OpTy::Div));
	match_op!(lexer, ">", Token::Op(OpTy::Gt));
	match_op!(lexer, "<", Token::Op(OpTy::Lt));
	match_op!(lexer, "!", Token::Op(OpTy::Not));
	match_op!(lexer, "~", Token::Op(OpTy::Flip));
	match_op!(lexer, "?", Token::Question);
	match_op!(lexer, "%", Token::Op(OpTy::Rem));
	match_op!(lexer, "&", Token::Op(OpTy::And));
	match_op!(lexer, "|", Token::Op(OpTy::Or));
	match_op!(lexer, "^", Token::Op(OpTy::Xor));
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
		"const" => Token::Const,
		"in" => Token::In,
		"out" => Token::Out,
		"inout" => Token::InOut,
		"attribute" => Token::Attribute,
		"uniform" => Token::Uniform,
		"varying" => Token::Varying,
		"buffer" => Token::Buffer,
		"shared" => Token::Shared,
		"centroid" => Token::Centroid,
		"sample" => Token::Sample,
		"patch" => Token::Patch,
		"layout" => Token::Layout,
		"flat" => Token::Flat,
		"smooth" => Token::Smooth,
		"noperspective" => Token::NoPerspective,
		"highp" => Token::HighP,
		"mediump" => Token::MediumP,
		"lowp" => Token::LowP,
		"invariant" => Token::Invariant,
		"precise" => Token::Precise,
		"coherent" => Token::Coherent,
		"volatile" => Token::Volatile,
		"restrict" => Token::Restrict,
		"readonly" => Token::Readonly,
		"writeonly" => Token::Writeonly,
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

/// Performs lexical analysis of the source string and returns a vector of [`Token`]s.
///
/// This lexer uses the "Maximal munch" principle to greedily create Tokens. This means the longest possible valid
/// token is always produced. Some examples:
///
/// ```text
/// i---7     lexes as (--) (-)
/// i-----7   lexes as (--) (--) (-)
/// i-- - --7 lexes as (--) (-) (--)
/// ```
pub fn lexer(source: &str) -> Vec<Spanned<Token>> {
	let mut tokens = Vec::new();
	let mut lexer = Lexer::new(source);
	let mut buffer = String::new();
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
		let buffer_start = lexer.position();
		// Peek the current character.
		let mut current = match lexer.peek() {
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
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
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
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
					));
					break 'word;
				}
			}
		} else if is_number_start(&current) {
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
						tokens.push((
							Token::Dot,
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
						));
						continue;
					}
				} else {
					// We have a `.` followed by the end of the source string, so this must be a punctuation token.
					// We consume the character because otherwise we'd end up back in this branch again.
					lexer.advance();
					tokens.push((
						Token::Dot,
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
					));
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
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
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
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
					));
					tokens.push((
						Token::Dot,
						Span {
							start: lexer.position(),
							end: lexer.position() + 1,
						},
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
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
					));
					tokens.push((
						Token::Dot,
						Span {
							start: lexer.position(),
							end: lexer.position() + 1,
						},
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
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
					));
					tokens.push((
						Token::Dot,
						Span {
							start: lexer.position(),
							end: lexer.position() + 1,
						},
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
										Span {
											start: buffer_start,
											end: lexer.position(),
										},
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
									Span {
										start: buffer_start,
										end: lexer.position(),
									},
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
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
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
								Span {
									start: buffer_start,
									end: lexer.position(),
								},
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
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
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
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
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
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
						));
						break 'comment;
					}
				}
			} else {
				tokens.push((
					match_punctuation(&mut lexer),
					Span {
						start: buffer_start,
						end: lexer.position(),
					},
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
							Span {
								start: buffer_start,
								end: lexer.position(),
							},
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
						Span {
							start: buffer_start,
							end: lexer.position(),
						},
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
				Span {
					start: buffer_start,
					end: lexer.position(),
				},
			));
		}
	}

	tokens
}

#[test]
#[rustfmt::skip]
fn spans() {
	// Identifiers/keywords
	assert_eq!(lexer("return"), vec![(Token::Return, span(0, 6))]);
	assert_eq!(lexer("break "), vec![(Token::Break, span(0, 5))]);
	assert_eq!(lexer("return break"), vec![(Token::Return, span(0, 6)), (Token::Break, span(7, 12))]);
	// Punctuation
	assert_eq!(lexer(";"), vec![(Token::Semi, span(0, 1))]);
	assert_eq!(lexer(": "), vec![(Token::Colon, span(0, 1))]);
	assert_eq!(lexer("; :"), vec![(Token::Semi, span(0, 1)), (Token::Colon, span(2, 3))]);
	// Comments
	assert_eq!(lexer("// comment"), vec![(Token::Comment { str: " comment".into(), contains_eof: false }, span(0, 10))]);
	assert_eq!(lexer("/* a */"), vec![(Token::Comment { str: " a ".into(), contains_eof: false }, span(0, 7))]);
	assert_eq!(lexer("/* a"), vec![(Token::Comment { str: " a".into(), contains_eof: true }, span(0, 4))]);
	// Directive
	assert_eq!(lexer("#dir"), vec![(Token::Directive("dir".into()), span(0, 4))]);
	assert_eq!(lexer("#dir a "), vec![(Token::Directive("dir a ".into()), span(0, 7))]);
	// Invalid
	assert_eq!(lexer("@"), vec![(Token::Invalid('@'), span(0, 1))]);
	assert_eq!(lexer("¬"), vec![(Token::Invalid('¬'), span(0, 1))]);
	assert_eq!(lexer("@  ¬"), vec![(Token::Invalid('@'), span(0, 1)), (Token::Invalid('¬'), span(3, 4))]);
	// Numbers
	assert_eq!(lexer("."), vec![(Token::Dot, span(0, 1))]);
	assert_eq!(lexer(". "), vec![(Token::Dot, span(0, 1))]);
	assert_eq!(lexer("0xF."), vec![(Token::Num { num: "F".into(), suffix: None, type_: NumType::Hex }, span(0, 3)), (Token::Dot, span(3, 4))]);
	assert_eq!(lexer("123u."), vec![(Token::Num { num: "123".into(), suffix: Some("u".into()), type_: NumType::Dec }, span(0, 4)), (Token::Dot, span(4, 5))]);
	assert_eq!(lexer("1.2."), vec![(Token::Num { num: "1.2".into(), suffix: None, type_: NumType::Float }, span(0, 3)), (Token::Dot, span(3, 4))]);
	assert_eq!(lexer("1.2."), vec![(Token::Num { num: "1.2".into(), suffix: None, type_: NumType::Float }, span(0, 3)), (Token::Dot, span(3, 4))]);
	assert_eq!(lexer("1e"), vec![(Token::Num { num: "1".into(), suffix: Some("e".into()), type_: NumType::Dec }, span(0, 2))]);
	assert_eq!(lexer("123 "), vec![(Token::Num { num: "123".into(), suffix: None, type_: NumType::Dec }, span(0, 3))]);
	assert_eq!(lexer("1e+="), vec![(Token::Num { num: "1".into(), suffix: Some("e".into()), type_: NumType::Dec }, span(0, 2)), (Token::Op(OpTy::AddEq), span(2, 4))]);
	assert_eq!(lexer("1e+"), vec![(Token::Num { num: "1".into(), suffix: Some("e".into()), type_: NumType::Dec }, span(0, 2)), (Token::Op(OpTy::Add), span(2, 3))]);
}

/// Asserts the token output of the `lexer()` matches the right hand side; ignores the spans.
#[cfg(test)]
macro_rules! assert_tokens {
    ($src:expr, $($token:expr),*) => {
		let output = lexer($src).into_iter().map(|(t, _)| t).collect::<Vec<_>>();
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
	assert_tokens!("const", Token::Const);
	assert_tokens!("in", Token::In);
	assert_tokens!("out", Token::Out);
	assert_tokens!("inout", Token::InOut);
	assert_tokens!("attribute", Token::Attribute);
	assert_tokens!("uniform", Token::Uniform);
	assert_tokens!("varying", Token::Varying);
	assert_tokens!("buffer", Token::Buffer);
	assert_tokens!("shared", Token::Shared);
	assert_tokens!("centroid", Token::Centroid);
	assert_tokens!("sample", Token::Sample);
	assert_tokens!("patch", Token::Patch);
	assert_tokens!("layout", Token::Layout);
	assert_tokens!("flat", Token::Flat);
	assert_tokens!("smooth", Token::Smooth);
	assert_tokens!("noperspective", Token::NoPerspective);
	assert_tokens!("highp", Token::HighP);
	assert_tokens!("mediump", Token::MediumP);
	assert_tokens!("lowp", Token::LowP);
	assert_tokens!("invariant", Token::Invariant);
	assert_tokens!("precise", Token::Precise);
	assert_tokens!("coherent", Token::Coherent);
	assert_tokens!("volatile", Token::Volatile);
	assert_tokens!("restrict", Token::Restrict);
	assert_tokens!("readonly", Token::Readonly);
	assert_tokens!("writeonly", Token::Writeonly);
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
	assert_tokens!("(", Token::LParen);
	assert_tokens!(")", Token::RParen);
	assert_tokens!("[", Token::LBracket);
	assert_tokens!("]", Token::RBracket);
	assert_tokens!("{", Token::LBrace);
	assert_tokens!("}", Token::RBrace);
	assert_tokens!(":", Token::Colon);
	assert_tokens!("=", Token::Op(OpTy::Eq));
	assert_tokens!("+", Token::Op(OpTy::Add));
	assert_tokens!("-", Token::Op(OpTy::Sub));
	assert_tokens!("*", Token::Op(OpTy::Mul));
	assert_tokens!("/", Token::Op(OpTy::Div));
	assert_tokens!(">", Token::Op(OpTy::Gt));
	assert_tokens!("<", Token::Op(OpTy::Lt));
	assert_tokens!("!", Token::Op(OpTy::Not));
	assert_tokens!("~", Token::Op(OpTy::Flip));
	assert_tokens!("?", Token::Question);
	assert_tokens!("%", Token::Op(OpTy::Rem));
	assert_tokens!("&", Token::Op(OpTy::And));
	assert_tokens!("|", Token::Op(OpTy::Or));
	assert_tokens!("^", Token::Op(OpTy::Xor));
	assert_tokens!("==", Token::Op(OpTy::EqEq));
	assert_tokens!("!=", Token::Op(OpTy::NotEq));
	assert_tokens!(">=", Token::Op(OpTy::Ge));
	assert_tokens!("<=", Token::Op(OpTy::Le));
	assert_tokens!("&&", Token::Op(OpTy::AndAnd));
	assert_tokens!("||", Token::Op(OpTy::OrOr));
	assert_tokens!("^^", Token::Op(OpTy::XorXor));
	assert_tokens!("++", Token::Op(OpTy::AddAdd));
	assert_tokens!("--", Token::Op(OpTy::SubSub));
	assert_tokens!("<<", Token::Op(OpTy::LShift));
	assert_tokens!(">>", Token::Op(OpTy::RShift));
	assert_tokens!("+=", Token::Op(OpTy::AddEq));
	assert_tokens!("-=", Token::Op(OpTy::SubEq));
	assert_tokens!("*=", Token::Op(OpTy::MulEq));
	assert_tokens!("/=", Token::Op(OpTy::DivEq));
	assert_tokens!("%=", Token::Op(OpTy::RemEq));
	assert_tokens!("&=", Token::Op(OpTy::AndEq));
	assert_tokens!("|=", Token::Op(OpTy::OrEq));
	assert_tokens!("^=", Token::Op(OpTy::XorEq));
	assert_tokens!("<<=", Token::Op(OpTy::LShiftEq));
	assert_tokens!(">>=", Token::Op(OpTy::RShiftEq));
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
