use crate::ast::{
	Either, Expr, ExtBehaviour, Ident, Lit, Preproc, Primitive, Stmt, Type,
};
use chumsky::{prelude::*, Stream};

pub fn parse(source: &str) {
	let (cst, errors) = lexer().parse_recovery(source);
	println!("{cst:?}");
	println!("errors: {errors:?}");

	if let Some(tokens) = cst {
		let len = source.chars().count();
		let (ast, errors) = parser().parse_recovery(Stream::from_iter(
			len..len + 1,
			tokens.into_iter(),
		));
		println!("{ast:?}");
		if let Some(ast) = ast {
			for stmt in ast {
				print_stmt(&stmt, 0);
			}
		}
		println!("\r\nerrors: {errors:?}");
	}
}

fn print_stmt(stmt: &Stmt, indent: usize) {
	match stmt {
		Stmt::Empty => print!(
			"\r\n{:indent$}\x1b[9m(Empty)\x1b[0m",
			"",
			indent = indent * 4
		),
		Stmt::VarDecl {
			type_,
			ident,
			value,
			is_const,
		} => {
			print!(
				"\r\n{:indent$}\x1b[32mVar\x1b[0m(type: {type_}, ident: {ident}",
				"",
				indent = indent * 4
			);
			if *is_const {
				print!(", \x1b[4mconst\x1b[0m");
			}
			print!(")");
			if let Some(value) = value {
				print!(" = {value}");
			}
		}
		Stmt::FnDecl {
			type_,
			ident,
			params,
			body,
		} => {
			print!(
				"\r\n{:indent$}\x1b[34mFn\x1b[0m(return: {type_} ident: {ident}, params: [",
				"",
				indent = indent * 4
			);
			for (type_, ident) in params {
				print!("{type_}: {ident}, ");
			}
			print!("]) {{");
			for inner in body {
				print_stmt(inner, indent + 1);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		Stmt::StructDecl { ident, members } => {
			print!(
				"\r\n{:indent$}\x1b[32mStruct\x1b[0m(ident: {ident}, members: [",
				"",
				indent = indent * 4
			);
			for (t, i) in members {
				print!("{i}: {t}, ");
			}
			print!("])");
		}
		Stmt::FnCall { ident, args } => {
			print!(
				"\r\n{:indent$}\x1b[34mCall\x1b[0m(ident: {ident}, args: [",
				"",
				indent = indent * 4
			);
			for arg in args {
				print!("{arg}, ");
			}
			print!("])");
		}
		Stmt::VarAssign { ident, value } => {
			print!(
				"\r\n{:indent$}\x1b[32mAssign\x1b[0m(ident: {ident}) = {value}",
				"",
				indent = indent * 4
			);
		}
		Stmt::VarEq { ident, value, op } => {
			print!(
				"\r\n{:indent$}\x1b[32mAssign\x1b[0m(ident: {ident}, op: \x1b[36m{op:?}\x1b[0m) = {value}",
				"",
				indent = indent * 4
			);
		}
		Stmt::Preproc(p) => print!(
			"\r\n{:indent$}\x1b[4mPreproc({p})\x1b[0m",
			"",
			indent = indent * 4
		),
		Stmt::If {
			cond,
			body,
			else_ifs,
			else_,
		} => {
			print!("\r\n{:indent$}If({cond}) {{", "", indent = indent * 4);
			for stmt in body {
				print_stmt(stmt, indent + 1);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);

			for (cond, body) in else_ifs {
				print!("\r\n{:indent$}ElseIf({cond})", "", indent = indent * 4);
				for stmt in body {
					print_stmt(stmt, indent + 1);
				}
				print!("\r\n{:indent$}}}", "", indent = indent * 4);
			}

			if let Some(body) = else_ {
				print!("\r\n{:indent$}Else {{", "", indent = indent * 4);
				for stmt in body {
					print_stmt(stmt, indent + 1);
				}
				print!("\r\n{:indent$}}}", "", indent = indent * 4);
			}
		}
		Stmt::Switch { expr, cases } => {
			print!("\r\n{:indent$}Switch({expr}) {{", "", indent = indent * 4);
			for (expr, stmts) in cases {
				if let Some(expr) = expr {
					print!(
						"\r\n{:indent$}Case({expr}) {{",
						"",
						indent = (indent + 1) * 4
					);
				} else {
					print!(
						"\r\n{:indent$}Default {{",
						"",
						indent = (indent + 1) * 4
					);
				}
				for stmt in stmts {
					print_stmt(stmt, indent + 2);
				}
				print!("\r\n{:indent$}}}", "", indent = (indent + 1) * 4);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		Stmt::For {
			var,
			cond,
			inc,
			body,
		} => {
			print!("\r\n{:indent$}For(", "", indent = indent * 4);
			if let Some(var) = var {
				print!("var:");
				print_stmt(var, indent + 2);
				print!(", ");
			}
			if let Some(cond) = cond {
				print!(
					"\r\n{:indent$}cond:\r\n{:indent_2$}{cond}, ",
					"",
					"",
					indent = (indent + 1) * 4,
					indent_2 = (indent + 2) * 4
				);
			}
			if let Some(inc) = inc {
				print!(
					"\r\n{:indent$}inc:\r\n{:indent_2$}{inc}, ",
					"",
					"",
					indent = (indent + 1) * 4,
					indent_2 = (indent + 2) * 4
				);
			}
			print!(") {{");
			for stmt in body {
				print_stmt(stmt, indent + 1);
			}
			print!("\r\n{:indent$}}}", "", indent = indent * 4);
		}
		Stmt::Return(expr) => {
			print!("\r\n{:indent$}RETURN", "", indent = indent * 4);
			if let Some(expr) = expr {
				print!("(value: {expr})");
			}
		}
		Stmt::Break => {
			print!("\r\n{:indent$}BREAK", "", indent = indent * 4)
		}
		Stmt::Discard => {
			print!("\r\n{:indent$}DISCARD", "", indent = indent * 4)
		}
	}
}

/// Filters only the specified operands.
///
/// # Example
/// ```rust
/// match_op!(OpType::Mul, OpType::Div).then(/*...*/)
/// ```
macro_rules! match_op {
	($($op:pat),*) => {
		filter(|t: &Token| match t {
			Token::Op(op) => match op {
				$(
					$op => true,
				)*
				_ => false,
			},
			_ => false,
		})
	};
}

/// Creates a pattern for a binary expression with the specified operands.
///
/// # Example
/// ```rust
/// let product = {/*...*/};
/// let sum = binary_expr!(product, OpType::Add, OpType::Sub);
/// ```
macro_rules! binary_expr {
	($prev:expr, $($op:pat),*) => {
		$prev
			.clone()
			.then(
				filter(|t: &Token| match t {
					Token::Op(op) => match op {
						$(
							$op => true,
						)*
						_ => false,
					},
					_ => false,
				})
				.map(|t| match t {
					Token::Op(op) => op,
					_ => unreachable!(),
				})
				.then($prev)
				.repeated(),
			)
			.foldl(|lhs, (op, rhs)| Expr::Binary {
				left: Box::from(lhs),
				op,
				right: Box::from(rhs),
			})
	};
}

/// Concrete syntax tree tokens.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Token {
	Num(String, NumType),
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

/// The different number types/notations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NumType {
	Normal,
	Oct,
	Hex,
	Float,
	Double,
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

type Spanned<T> = (T, Span);
type Span = std::ops::Range<usize>;

/// Performs lexical parsing of the steam of `char`s into a list of [`Token`]s with their span in the string.
fn lexer() -> impl Parser<char, Vec<Spanned<Token>>, Error = Simple<char>> {
	// Preprocessor directive lines must be parsed first and as a whole string. This must be done because unlike
	// with statements, where the 'parser()' is looking for a series of tokens followed a semi-colon, directives
	// have no semi-colon and instead their end is categorised by the EOL. By parsing the entire directive line
	// into a single string, we simplify this parser and reduce the number of edge cases we need to track.
	// Meanwhile, the directive can be parsed on its own in the 'preproc_parser()' function.
	let directive = just('#')
		.then(
			filter(|c: &char| {
				// TODO: Check which characters are actually valid within a preprocessor directive.
				c.is_ascii_alphanumeric()
					|| c.is_ascii_punctuation()
					|| *c == ' '
			})
			.repeated()
			.at_least(1),
		)
		.then_ignore(text::newline().or(end()))
		.map(|(_, v)| Token::Directive(v.iter().collect()))
		.padded();

	// Parse the source code in order of least ambiguity, to ensure the correct tokens are given out every time.
	let token = literals()
		.or(punctuation())
		.or(keywords())
		.or(text::ident().map(|s| Token::Ident(s)))
		// If none of the patterns have succeeded, then we must have a character that is straight up illegal in
		// glsl source code (or a situation where a character is legal but can't start the token with it, e.g.
		// '_'), so create an 'Invalid' token.
		.or(filter(|_| true).map(|c| Token::Invalid(String::from(c))))
		.padded();

	directive
		.or(token)
		.map_with_span(|t, s| (t, s))
		.repeated()
		.recover_with(skip_then_retry_until([]))
}

/// Parse any valid punctuation or operator symbols.
fn punctuation() -> impl Parser<char, Token, Error = Simple<char>> {
	// Parse in order of least ambiguity, so starting with 3 characters and going to 1, and most common occurrence,
	// to reduce the average amount of checks necessary.
	//
	// Split because of limit; 'choice()' is a generic function for performance reasons and it only has 26 generic
	// overrides.
	choice((
		just("<<=").to(Token::Op(OpType::LShiftEq)),
		just(">>=").to(Token::Op(OpType::RShiftEq)),
		just("==").to(Token::Op(OpType::EqEq)),
		just("!=").to(Token::Op(OpType::NotEq)),
		just(">=").to(Token::Op(OpType::Ge)),
		just("<=").to(Token::Op(OpType::Le)),
		just("&&").to(Token::Op(OpType::AndAnd)),
		just("||").to(Token::Op(OpType::OrOr)),
		just("++").to(Token::Op(OpType::AddAdd)),
		just("--").to(Token::Op(OpType::SubSub)),
		just("<<").to(Token::Op(OpType::LShift)),
		just(">>").to(Token::Op(OpType::RShift)),
		just("+=").to(Token::Op(OpType::AddEq)),
		just("-=").to(Token::Op(OpType::SubEq)),
		just("*=").to(Token::Op(OpType::MulEq)),
		just("/=").to(Token::Op(OpType::DivEq)),
		just("%=").to(Token::Op(OpType::RemEq)),
		just("&=").to(Token::Op(OpType::AndEq)),
		just("|=").to(Token::Op(OpType::OrEq)),
		just("^^").to(Token::Op(OpType::XorXor)),
		just("^=").to(Token::Op(OpType::XorEq)),
	))
	.or(choice((
		just('=').to(Token::Eq),
		just(',').to(Token::Comma),
		just('.').to(Token::Dot),
		just(';').to(Token::Semi),
		just('(').to(Token::LParen),
		just(')').to(Token::RParen),
		just('[').to(Token::LBracket),
		just(']').to(Token::RBracket),
		just('{').to(Token::LBrace),
		just('}').to(Token::RBrace),
		just(':').to(Token::Colon),
		just('+').to(Token::Op(OpType::Add)),
		just('-').to(Token::Op(OpType::Sub)),
		just('*').to(Token::Op(OpType::Mul)),
		just('/').to(Token::Op(OpType::Div)),
		just('>').to(Token::Op(OpType::Gt)),
		just('<').to(Token::Op(OpType::Lt)),
		just('!').to(Token::Op(OpType::Not)),
		just('~').to(Token::Op(OpType::Flip)),
		just('?').to(Token::Question),
		just('%').to(Token::Op(OpType::Rem)),
		just('&').to(Token::Op(OpType::And)),
		just('|').to(Token::Op(OpType::Or)),
		just('^').to(Token::Op(OpType::Xor)),
	)))
}

/// Parse keywords.
fn keywords() -> impl Parser<char, Token, Error = Simple<char>> {
	// Split because of limit; 'choice()' is a generic function for performance reasons and it only has 26 generic
	// overrides.
	choice((
		text::keyword("if").to(Token::If),
		text::keyword("else").to(Token::Else),
		text::keyword("for").to(Token::For),
		text::keyword("switch").to(Token::Switch),
		text::keyword("case").to(Token::Case),
		text::keyword("default").to(Token::Default),
		text::keyword("break").to(Token::Break),
		text::keyword("return").to(Token::Return),
		text::keyword("discard").to(Token::Discard),
		text::keyword("struct").to(Token::Struct),
		// TODO: Parse reserved keywords which have no use currently.
	))
	.or(choice((
		text::keyword("in").to(Token::In),
		text::keyword("out").to(Token::Out),
		text::keyword("inout").to(Token::InOut),
		text::keyword("uniform").to(Token::Uniform),
		text::keyword("buffer").to(Token::Buffer),
		text::keyword("const").to(Token::Const),
		text::keyword("invariant").to(Token::Invariant),
		text::keyword("highp").to(Token::Precision),
		text::keyword("mediump").to(Token::Precision),
		text::keyword("lowp").to(Token::Precision),
		text::keyword("flat").to(Token::Interpolation),
		text::keyword("smooth").to(Token::Interpolation),
		text::keyword("noperspective").to(Token::Interpolation),
		text::keyword("layout").to(Token::Layout),
		text::keyword("location").to(Token::Location),
		text::keyword("component").to(Token::Component),
		text::keyword("origin_upper_left").to(Token::FragCoord),
		text::keyword("pixel_center_integer").to(Token::FragCoord),
		text::keyword("depth_any").to(Token::FragDepth),
		text::keyword("depth_greater").to(Token::FragDepth),
		text::keyword("depth_less").to(Token::FragDepth),
		text::keyword("depth_unchanged").to(Token::FragDepth),
		text::keyword("index").to(Token::Index),
		text::keyword("early_fragment_tests").to(Token::FragTest),
	)))
}

/// Parse literal values, i.e. numbers and booleans.
///
/// If this parser encounters a partially valid number, where the first *n* characters are valid but the last *m*
/// are not, it will return a [`Token::Invalid`]. This is done because of the following reason:
///
/// For every token other than number literals, spaces don't matter, i.e. `i+=5` will be parsed as a
/// `[Token::Ident("i"), Token::AddEq, Token::Num(5)]`. However, because numbers *can* contain ascii letters at the
/// end (such as the `u` postfix), this creates an element of ambiguity. Take for example the string `5.0ufoo`.
/// According to the glsl spec, this string is seen as a float of value `5.0` with a postfix of `ufoo` (which is an
/// invalid postfix). If this literal parser only cared about valid patterns, the `lexer()` would produce
/// `[Token::Num(5, NumType::Float), Token::Ident("ufoo")]`, which is clearly incorrect, because after a number we
/// need padding **if** the next token is an identifier (we don't need padding for punctuation). So instead, by
/// also matching for invalid characters after a number, we can produce a `Token::Invalid("5.0ufoo")` which is the
/// corrent result.
///
/// You may think that an alternative like this would work:
/// ```
/// num_float
///     .or(num_double)
///     /*...*/
///     .then_ignore(filter(|c: &char| *c == ' '))
/// ```
/// But it doesn't. This wouldn't parse `5+` because of the missing space between the number and operator. The key
/// isn't that we want a space after a number. It's that we want a space if the characters (after any valid
/// postfix) are letters.
fn literals() -> impl Parser<char, Token, Error = Simple<char>> {
	// Unsigned integer suffix.
	let suffix = filter(|c: &char| *c == 'u' || *c == 'U').or_not();
	// Double specifier suffix.
	let lf = just('l').then(just('f')).or(just('L').then(just('F')));

	let zero_valid = just('0')
		.chain::<char, _, _>(suffix)
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Normal));
	let zero_invalid = just('0')
		.chain::<char, _, _>(suffix)
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_alphanumeric())
				.repeated()
				.at_least(1),
		)
		.collect::<String>()
		.map(|s| Token::Invalid(s));

	let num = filter(|c: &char| c.is_ascii_digit() && *c != '0')
		.chain::<char, _, _>(filter(|c: &char| c.is_ascii_digit()).repeated())
		.chain::<char, _, _>(suffix);
	let num_valid = num.collect().map(|s| Token::Num(s, NumType::Normal));
	let num_invalid = num
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_alphanumeric())
				.repeated()
				.at_least(1),
		)
		.collect::<String>()
		.map(|s| Token::Invalid(s));

	let num_hex = just('0')
		.then(just('x'))
		.chain::<char, _, _>(
			filter::<_, _, Simple<char>>(|c: &char| c.is_ascii_hexdigit())
				.repeated()
				.at_least(1),
		)
		.chain::<char, _, _>(suffix);
	let num_hex_valid = num_hex.collect().map(|s| Token::Num(s, NumType::Hex));
	let num_hex_invalid = num_hex
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_alphanumeric())
				.repeated()
				.at_least(1),
		)
		.collect::<String>()
		.map(|s| Token::Invalid(s));

	let num_oct = just('0')
		.chain::<char, _, _>(
			filter(|c: &char| match c {
				'0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' => true,
				_ => false,
			})
			.repeated()
			.at_least(1),
		)
		.chain::<char, _, _>(suffix);
	let num_oct_valid = num_oct.collect().map(|s| Token::Num(s, NumType::Oct));
	let num_oct_invalid = num_oct
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_alphanumeric())
				.repeated()
				.at_least(1),
		)
		.collect::<String>()
		.map(|s| Token::Invalid(s));

	let num_float = filter(|c: &char| c.is_ascii_digit())
		.repeated()
		.at_least(1)
		.chain(just('.'))
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1),
		);
	let num_float_valid = num_float
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Float));
	let num_float_invalid = num_float
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_alphanumeric())
				.repeated()
				.at_least(1),
		)
		.collect::<String>()
		.map(|s| Token::Invalid(s));

	let num_float_exp = filter(|c: &char| c.is_ascii_digit())
		.repeated()
		.at_least(1)
		.chain(just('.'))
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1),
		)
		.chain(just('E').or(just('e')))
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1),
		);
	let num_float_exp_valid = num_float_exp
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Float));
	let num_float_exp_invalid = num_float_exp
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_alphanumeric())
				.repeated()
				.at_least(1),
		)
		.collect::<String>()
		.map(|s| Token::Invalid(s));

	let num_float_exp_no_decimal = filter(|c: &char| c.is_ascii_digit())
		.repeated()
		.at_least(1)
		.chain(just('E').or(just('e')))
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1),
		);
	let num_float_exp_no_decimal_valid = num_float_exp_no_decimal
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Float));
	let num_float_exp_no_decimal_invalid = num_float_exp_no_decimal
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_alphanumeric())
				.repeated()
				.at_least(1),
		)
		.collect::<String>()
		.map(|s| Token::Invalid(s));

	let num_double = filter(|c: &char| c.is_ascii_digit())
		.repeated()
		.at_least(1)
		.chain(just('.'))
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1),
		)
		.chain::<char, _, _>(lf);
	let num_double_valid = num_double
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Double));
	let num_double_invalid = num_double
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_alphanumeric())
				.repeated()
				.at_least(1),
		)
		.collect::<String>()
		.map(|s| Token::Invalid(s));

	let num_double_exp = filter(|c: &char| c.is_ascii_digit())
		.repeated()
		.at_least(1)
		.chain(just('.'))
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1),
		)
		.chain(just('E').or(just('e')))
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1),
		)
		.chain::<char, _, _>(lf);
	let num_double_exp_valid = num_double_exp
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Double));
	let num_double_exp_invalid = num_double_exp
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_alphanumeric())
				.repeated()
				.at_least(1),
		)
		.collect::<String>()
		.map(|s| Token::Invalid(s));

	let num_double_exp_no_decimal = filter(|c: &char| c.is_ascii_digit())
		.repeated()
		.at_least(1)
		.chain(just('E').or(just('e')))
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1),
		)
		.chain::<char, _, _>(lf);
	let num_double_exp_no_decimal_valid = num_double_exp_no_decimal
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Double));
	let num_double_exp_no_decimal_invalid = num_double_exp_no_decimal
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_alphanumeric())
				.repeated()
				.at_least(1),
		)
		.collect::<String>()
		.map(|s| Token::Invalid(s));

	// Unlike with the number parsers, we don't need to check for characters after the boolean, i.e. 'truep'
	// because the 'text::keyword()' function already makes sure that the string is not followed by any other
	// letters (still allows punctuation, etc.).
	let b_true = text::keyword("true").map(|_| Token::Bool(true));
	let b_false = text::keyword("false").map(|_| Token::Bool(false));

	num_hex_invalid
		.or(num_hex_valid)
		.or(num_oct_invalid)
		.or(num_oct_valid)
		.or(num_double_exp_invalid)
		.or(num_double_exp_valid)
		.or(num_double_exp_no_decimal_invalid)
		.or(num_double_exp_no_decimal_valid)
		.or(num_double_invalid)
		.or(num_double_valid)
		.or(num_float_exp_invalid)
		.or(num_float_exp_valid)
		.or(num_float_exp_no_decimal_invalid)
		.or(num_float_exp_no_decimal_valid)
		.or(num_float_invalid)
		.or(num_float_valid)
		.or(num_invalid)
		.or(num_valid)
		.or(zero_invalid)
		.or(zero_valid)
		.or(b_true)
		.or(b_false)
}

fn parser() -> impl Parser<Token, Vec<Stmt>, Error = Simple<Token>> {
	// Identifier for a name.
	let ident = filter(|t: &Token| match t {
		Token::Ident(_) => true,
		_ => false,
	})
	.try_map(|t, span| {
		let str = if let Token::Ident(s) = t {
			s
		} else {
			unreachable!()
		};

		match Ident::parse_name(&str) {
			Ok(i) => Ok(i),
			Err(_) => Err(Simple::custom(
				span,
				"Identifier cannot be the same as a type",
			)),
		}
	});

	// Type identifiers of any type, (incl. void).
	let type_ident = filter(|t: &Token| match t {
		Token::Ident(_) => true,
		_ => false,
	})
	.try_map(|t, span| {
		// Deconstruct the string.
		let str = if let Token::Ident(s) = t {
			s
		} else {
			unreachable!()
		};

		// First, try to parse a primitive type identifier. If not, try to parse a valid custom type identifier.
		match Primitive::parse(&str) {
			Ok(p) => Ok(Either::Left(p)),
			Err(_) => match Ident::parse_struct(&str) {
				Ok(i) => Ok(Either::Right(i)),
				Err(_) => Err(Simple::custom(span, "Invalid type")),
			},
		}
	});

	// Type identifiers that are allowed in variable declarations.
	let var_type_ident = filter(|t: &Token| match t {
		Token::Ident(_) => true,
		_ => false,
	})
	.try_map(|t, span| {
		// Deconstruct the string.
		let str = if let Token::Ident(s) = t {
			s
		} else {
			unreachable!()
		};

		// First, try to parse a primitive type identifier. If not, try to parse a valid custom type identifier.
		match Primitive::parse_var(&str) {
			Ok(p) => Ok(Either::Left(p)),
			Err(_) => match Ident::parse_struct(&str) {
				Ok(i) => Ok(Either::Right(i)),
				Err(_) => Err(Simple::custom(span, "Invalid type")),
			},
		}
	});

	// Array size, i.e. `[...]`.
	let arr = {
		let size = filter(|t: &Token| match t {
			Token::Num(_, _) => true,
			Token::Ident(_) => true,
			_ => false,
		})
		.try_map(|t, span| match t {
			Token::Num(s, t) => match t {
				NumType::Normal | NumType::Oct | NumType::Hex => {
					match Lit::parse_num(&s, t) {
						Ok(l) => match l {
							Lit::UInt(u) => Ok(Either::Left(u as usize)),
							Lit::Int(i) => Ok(Either::Left(i as usize)),
							_ => unimplemented!(),
						},
						Err(_) => {
							Err(Simple::custom(span, "Could not parse number!"))
						}
					}
				}
				_ => Err(Simple::custom(span, "Float values are not allowed")),
			},
			Token::Ident(s) => Ok(Either::Right(Ident(s))),
			_ => unreachable!(),
		});

		just(Token::LBracket)
			.then(size.or_not())
			.then(just(Token::RBracket))
			.map(|((_, s), _)| s)
	};

	// Expressions of all kinds.
	let expr = recursive(|expr| {
		let arr_init = type_ident
			.clone()
			.then(arr.clone())
			.then(
				expr.clone()
					.separated_by(just(Token::Comma))
					.delimited_by(just(Token::LParen), just(Token::RParen)),
			)
			.map(|((type_, size), args)| Expr::Array {
				type_: Type::Array(type_, size),
				args,
			});

		let init_list = arr_init.or(expr
			.clone()
			.separated_by(just(Token::Comma))
			.delimited_by(just(Token::LBrace), just(Token::RBrace))
			.map(|v| Expr::InitList(v)));

		let fn_call = init_list.or(filter(|t: &Token| match t {
			Token::Ident(_) => true,
			_ => false,
		})
		.then(
			expr.clone()
				.separated_by(just(Token::Comma))
				.delimited_by(just(Token::LParen), just(Token::RParen)),
		)
		.try_map(|(t, args), span| {
			let str = if let Token::Ident(s) = t {
				s
			} else {
				unreachable!()
			};

			match Ident::parse_name(&str) {
				Ok(i) => Ok(Expr::Fn { ident: i, args }),
				Err(_) => Err(Simple::custom(span, "Invalid identifier")),
			}
		}));

		let member = fn_call.or(filter(|t: &Token| match t {
			Token::Ident(_) => true,
			_ => false,
		})
		.then(
			just(Token::Dot)
				.ignored()
				.then(filter(|t: &Token| match t {
					Token::Ident(_) => true,
					_ => false,
				}))
				.repeated()
				.at_least(1),
		)
		.try_map(|(first, v), span| {
			let mut vec = Vec::with_capacity(v.len() + 1);

			match first {
				Token::Ident(s) => match Ident::parse_name(&s) {
					Ok(i) => vec.push(i),
					Err(_) => {
						return Err(Simple::custom(span, "Invalid identifier"));
					}
				},
				_ => unreachable!(),
			}
			for (_, t) in v.into_iter() {
				match t {
					Token::Ident(s) => match Ident::parse_name(&s) {
						Ok(i) => vec.push(i),
						Err(_) => {
							return Err(Simple::custom(
								span,
								"Invalid identifier",
							));
						}
					},
					_ => unreachable!(),
				}
			}

			Ok(Expr::Member(vec))
		}));

		let val = member.or(filter(|t: &Token| match t {
			Token::Bool(_) => true,
			Token::Num(_, _) => true,
			Token::Ident(_) => true,
			_ => false,
		})
		.try_map(|t, span| match t {
			Token::Bool(b) => Ok(Expr::Lit(Lit::Bool(b))),
			Token::Num(s, t) => match Lit::parse_num(&s, t) {
				Ok(l) => Ok(Expr::Lit(l)),
				Err(_) => Err(Simple::custom(span, "Could not parse number")),
			},
			Token::Ident(s) => match Ident::parse_name(&s) {
				Ok(i) => Ok(Expr::Ident(i)),
				Err(_) => Err(Simple::custom(span, "Invalid identifier")),
			},
			_ => unreachable!(),
		}));

		let atom = val
			.or(expr
				.clone()
				.delimited_by(just(Token::LParen), just(Token::RParen)))
			.boxed();

		// Operators in order of precedence.
		// Note: The reason for the sprinkling of '.boxed()' everywhere is because otherwise there would be so much
		// nesting of generic types that rustc will have a breakdown.
		let postfix = atom
			.then(match_op!(OpType::AddAdd, OpType::SubSub).or_not())
			.map(|(expr, op)| {
				if let Some(op) = op {
					let op = match op {
						Token::Op(o) => o,
						_ => unreachable!(),
					};
					Expr::Postfix(Box::from(expr), op)
				} else {
					expr
				}
			});
		let prefix = match_op!(OpType::AddAdd, OpType::SubSub)
			.or_not()
			.then(postfix)
			.map(|(op, expr)| {
				if let Some(op) = op {
					let op = match op {
						Token::Op(o) => o,
						_ => unreachable!(),
					};
					Expr::Prefix(Box::from(expr), op)
				} else {
					expr
				}
			});
		let flip =
			match_op!(OpType::Flip)
				.or_not()
				.then(prefix)
				.map(|(op, expr)| {
					if let Some(_) = op {
						Expr::Flip(Box::from(expr))
					} else {
						expr
					}
				});
		let not = match_op!(OpType::Not)
			.repeated()
			.then(flip)
			.foldr(|_op, rhs| Expr::Not(Box::new(rhs)));
		let neg = match_op!(OpType::Sub)
			.repeated()
			.then(not)
			.foldr(|_op, rhs| Expr::Neg(Box::new(rhs)));
		let product = binary_expr!(neg, OpType::Mul, OpType::Div, OpType::Rem);
		let sum = binary_expr!(product, OpType::Add, OpType::Sub);
		let shift = binary_expr!(sum, OpType::LShift, OpType::RShift);
		let cpm =
			binary_expr!(shift, OpType::Lt, OpType::Gt, OpType::Le, OpType::Ge);
		let eq = binary_expr!(cpm, OpType::EqEq, OpType::NotEq).boxed();
		let b_and = binary_expr!(eq, OpType::And);
		let b_xor = binary_expr!(b_and, OpType::Xor);
		let b_or = binary_expr!(b_xor, OpType::Or);
		let b_and_and = binary_expr!(b_or, OpType::AndAnd);
		let b_xor_xor = binary_expr!(b_and_and, OpType::XorXor);
		let b_or_or = binary_expr!(b_xor_xor, OpType::OrOr);
		let ternary = b_or_or
			.then(
				just(Token::Question)
					.ignored()
					.then(expr.clone())
					.then_ignore(just(Token::Colon))
					.then(expr)
					.or_not(),
			)
			.map(|(expr, if_else)| {
				if let Some(((_, true_), false_)) = if_else {
					Expr::Ternary {
						cond: Box::from(expr),
						true_: Box::from(true_),
						false_: Box::from(false_),
					}
				} else {
					expr
				}
			});
		let assign = binary_expr!(
			ternary,
			OpType::AddEq,
			OpType::SubEq,
			OpType::MulEq,
			OpType::DivEq,
			OpType::RemEq,
			OpType::AndEq,
			OpType::XorEq,
			OpType::OrEq,
			OpType::LShiftEq,
			OpType::RShiftEq
		);
		assign
	})
	.boxed();

	// Preprocessor directives.
	let preproc = filter(|t: &Token| match t {
		Token::Directive(_) => true,
		_ => false,
	})
	.try_map(|t, span: std::ops::Range<usize>| match t {
		Token::Directive(s) => {
			let (stmt, errors) = preproc_parser().parse_recovery(s);

			if let Some(_) = errors.first() {
				return Err(Simple::custom(
					span,
					"Error parsing preproc directive",
				));
			}

			if let Some(stmt) = stmt {
				Ok(stmt)
			} else {
				Ok(Stmt::Preproc(Preproc::Unsupported))
			}
		}
		_ => unreachable!(),
	});

	// Const qualifier.
	let const_ = just(Token::Const).or_not().map(|t| t.is_some());

	// Variable declaration.
	let var = const_
		.clone()
		.then(var_type_ident)
		.then(ident)
		.then(arr.clone().repeated())
		.then_ignore(just(Token::Eq))
		.then(expr.clone())
		.then_ignore(just(Token::Semi))
		.map(
			|((((is_const, type_ident), ident), size), rhs)| Stmt::VarDecl {
				type_: Type::new(type_ident, size),
				ident,
				value: Some(rhs),
				is_const,
			},
		);
	let var_uninit = const_
		.then(var_type_ident)
		.then(ident)
		.then(arr.clone().repeated())
		.then_ignore(just(Token::Semi))
		.map(|(((is_const, type_ident), ident), size)| Stmt::VarDecl {
			type_: Type::new(type_ident, size),
			ident,
			value: None,
			is_const,
		});

	// Empty statement.
	let empty = just(Token::Semi).map(|_| Stmt::Empty);

	// All statements within a function body.
	let stmt = recursive(|stmt| {
		let break_ = preproc.or(just(Token::Break)
			.then_ignore(just(Token::Semi))
			.to(Stmt::Break));
		let return_ = break_.or(just(Token::Return)
			.ignored()
			.then(expr.clone().or_not())
			.then_ignore(just(Token::Semi))
			.map(|(_, expr)| Stmt::Return(expr)));
		let discard = return_.or(just(Token::Discard)
			.then_ignore(just(Token::Semi))
			.to(Stmt::Discard));

		let var_eq = discard.or(expr
			.clone()
			.then_ignore(just(Token::Semi))
			.try_map(|expr, span| match expr {
				Expr::Binary { left, op, right } => {
					let ident = match *left {
						Expr::Ident(i) => i,
						_ => {
							return Err(Simple::custom(
								span,
								"Expected an identifier",
							))
						}
					};
					match op {
						OpType::AddEq
						| OpType::SubEq
						| OpType::MulEq
						| OpType::DivEq
						| OpType::RemEq
						| OpType::AndEq
						| OpType::XorEq
						| OpType::OrEq
						| OpType::LShiftEq
						| OpType::RShiftEq => {}
						_ => {
							return Err(Simple::custom(
								span,
								"Invalid operator",
							))
						}
					}

					Ok(Stmt::VarEq {
						ident,
						value: right,
						op,
					})
				}
				_ => return Err(Simple::custom(span, "invalid expression")),
			}));

		let var_assign =
			var_eq.or(var.clone()).or(var_uninit.clone()).or(ident
				.then_ignore(just(Token::Eq))
				.then(expr.clone())
				.then_ignore(just(Token::Semi))
				.map(|(ident, rhs)| Stmt::VarAssign { ident, value: rhs }));

		// Function call on its own.
		let fn_call = var_assign.or(ident
			.then(
				expr.clone()
					.separated_by(just(Token::Comma))
					.delimited_by(just(Token::LParen), just(Token::RParen)),
			)
			.then_ignore(just(Token::Semi))
			.map(|(ident, args)| Stmt::FnCall { ident, args }));

		// For statement.
		let for_ = just(Token::For)
			.ignored()
			.then(
				var.clone()
					.or(var_uninit.clone())
					.or(empty.clone())
					.or_not()
					.then(expr.clone().or_not().then_ignore(just(Token::Semi)))
					.then(expr.clone().or_not())
					.delimited_by(just(Token::LParen), just(Token::RParen)),
			)
			.then(
				stmt.clone()
					.repeated()
					.delimited_by(just(Token::LBrace), just(Token::RBrace)),
			)
			.map(|((_, ((var, cond), inc)), stmts)| Stmt::For {
				var: var.map(|s| Box::from(s)),
				cond,
				inc,
				body: stmts,
			});

		// If statement.
		let if_ =
			just(Token::If)
				.ignored()
				.then(
					expr.clone()
						.delimited_by(just(Token::LParen), just(Token::RParen)),
				)
				.then(
					stmt.clone()
						.repeated()
						.delimited_by(just(Token::LBrace), just(Token::RBrace)),
				)
				.then(
					// else ifs
					just(Token::Else)
						.ignored()
						.then_ignore(just(Token::If))
						.then(expr.clone().delimited_by(
							just(Token::LParen),
							just(Token::RParen),
						))
						.then(stmt.clone().repeated().delimited_by(
							just(Token::LBrace),
							just(Token::RBrace),
						))
						.repeated(),
				)
				.then(
					just(Token::Else)
						.ignored()
						.then(stmt.clone().repeated().delimited_by(
							just(Token::LBrace),
							just(Token::RBrace),
						))
						.or_not(),
				)
				.map(|((((_, cond), body), nth), opt): ((_, Vec<_>), _)| {
					Stmt::If {
						cond,
						body,
						else_ifs: nth
							.into_iter()
							.map(|((_, cond), stmts)| (cond, stmts))
							.collect(),
						else_: if let Some(opt) = opt {
							Some(opt.1)
						} else {
							None
						},
					}
				})
				.boxed();

		// Switch statement.
		let switch = just(Token::Switch)
			.ignored()
			.then(
				expr.clone()
					.delimited_by(just(Token::LParen), just(Token::RParen)),
			)
			.then(
				just(Token::Case)
					.ignored()
					.then(expr.clone())
					.then_ignore(just(Token::Colon))
					.then(stmt.clone().repeated())
					.map(|((_, expr), stmt)| (Some(expr), stmt))
					.or(just(Token::Default)
						.ignored()
						.then_ignore(just(Token::Colon))
						.then(stmt.clone().repeated())
						.map(|(_, stmt)| (None, stmt)))
					.repeated()
					.delimited_by(just(Token::LBrace), just(Token::RBrace)),
			)
			.map(|((_, expr), cases)| Stmt::Switch { expr, cases })
			.boxed();

		fn_call.or(if_).or(switch).or(for_).or(empty.clone())
	})
	.boxed();

	// Function parameter.
	let param = type_ident
		.clone()
		.then(ident.clone())
		.map(|(type_, ident)| (Type::Basic(type_), ident));

	// Function declaration.
	let func = type_ident
		.then(ident)
		.then(
			param
				.separated_by(just(Token::Comma))
				.delimited_by(just(Token::LParen), just(Token::RParen)),
		)
		.then(
			stmt.repeated()
				.delimited_by(just(Token::LBrace), just(Token::RBrace)),
		)
		.map(|(((type_ident, ident), params), body)| Stmt::FnDecl {
			type_: Type::Basic(type_ident),
			ident,
			params,
			body,
		});

	// Struct member.
	let member = var_type_ident
		.then(ident)
		.then(arr.repeated())
		.then_ignore(just(Token::Semi))
		.map(|((type_ident, ident), size)| {
			(Type::new(type_ident, size), ident)
		});

	// Struct declaration.
	let struct_ = just(Token::Struct)
		.ignored()
		.then(ident)
		.then(
			member
				.repeated()
				.delimited_by(just(Token::LBrace), just(Token::RBrace)),
		)
		.then_ignore(just(Token::Semi))
		.map(|((_, ident), members)| Stmt::StructDecl { ident, members });

	func.or(var)
		.or(var_uninit)
		.or(struct_)
		.or(empty)
		.or(preproc)
		.repeated()
}

fn preproc_parser() -> impl Parser<char, Stmt, Error = Simple<char>> {
	let version = text::keyword("version")
		.ignored()
		.padded()
		.then(text::digits(10).padded())
		.then(text::ident().padded().or_not())
		.try_map(|((_, v), p), span| {
			let is_core = if let Some(p) = p {
				if p == "core" {
					true
				} else if p == "compatibility" {
					false
				} else {
					return Err(Simple::custom(span, "invalid profile"));
				}
			} else {
				true
			};

			if v != "450" {
				return Err(Simple::custom(span, "invalid version"));
			}

			Ok(Stmt::Preproc(Preproc::Version {
				version: 450,
				is_core,
			}))
		});

	let extension = text::keyword("extension")
		.ignored()
		.padded()
		.then(text::ident().padded())
		.then_ignore(just(':').padded())
		.then(text::ident().padded())
		.try_map(|((_, name), ext), span| {
			let ext = match ext.as_str() {
				"enable" => ExtBehaviour::Enable,
				"disable" => ExtBehaviour::Disable,
				"warn" => ExtBehaviour::Warn,
				"require" => ExtBehaviour::Require,
				_ => return Err(Simple::custom(span, "Invalid behaviour")),
			};

			Ok(Stmt::Preproc(Preproc::Extension {
				name,
				behaviour: ext,
			}))
		});

	let line = text::keyword("line")
		.ignored()
		.padded()
		.then(text::digits(10).padded())
		.then(text::digits(10).padded().or_not())
		.try_map(
			|((_, line), src_str): (((), String), Option<String>), span| {
				let line = match usize::from_str_radix(line.as_str(), 10) {
					Ok(i) => i,
					Err(_) => {
						return Err(Simple::custom(span, "Invalid line number"))
					}
				};

				let src_str = if let Some(src_str) = src_str {
					match usize::from_str_radix(src_str.as_str(), 10) {
						Ok(i) => Some(i),
						Err(_) => {
							return Err(Simple::custom(
								span,
								"Invalid line number",
							))
						}
					}
				} else {
					None
				};

				Ok(Stmt::Preproc(Preproc::Line { line, src_str }))
			},
		);

	let include = text::keyword("include")
		.ignored()
		.padded()
		.then(
			filter(|c: &char| {
				// TODO: Check which characters are actually valid within an include path.
				c.is_ascii_alphanumeric()
					|| c.is_ascii_whitespace()
					|| *c == '.' || *c == '/'
					|| *c == '\\'
			})
			.repeated()
			.delimited_by(just('"'), just('"')),
		)
		.then_ignore(end())
		.map(|(_, v)| Stmt::Preproc(Preproc::Include(v.iter().collect())));

	let error = text::keyword("error")
		.ignored()
		.padded()
		.then(
			filter(|c: &char| {
				// TODO: Check which characters are actually valid within a message.
				c.is_ascii_alphanumeric()
					|| c.is_ascii_punctuation()
					|| c.is_ascii_whitespace()
			})
			.repeated(),
		)
		.map(|(_, v)| Stmt::Preproc(Preproc::Error(v.iter().collect())));

	let pragma = text::keyword("pragma")
		.ignored()
		.padded()
		.then(
			// TODO: Check which characters are actually valid within pragma options.
			filter(|c: &char| {
				c.is_ascii_alphanumeric()
					|| c.is_ascii_punctuation()
					|| c.is_ascii_whitespace()
			})
			.repeated(),
		)
		.map(|(_, v)| Stmt::Preproc(Preproc::Pragma(v.iter().collect())));

	let undef = text::keyword("undef")
		.ignored()
		.padded()
		.then(text::ident().padded())
		.then_ignore(end())
		.map(|(_, symbol)| Stmt::Preproc(Preproc::UnDef(symbol)));

	let ifdef = text::keyword("ifdef")
		.ignored()
		.padded()
		.then(text::ident().padded())
		.then_ignore(end())
		.map(|(_, symbol)| Stmt::Preproc(Preproc::IfDef(symbol)));

	let ifndef = text::keyword("ifdef")
		.ignored()
		.padded()
		.then(text::ident().padded())
		.then_ignore(end())
		.map(|(_, symbol)| Stmt::Preproc(Preproc::IfnDef(symbol)));

	let else_ = text::keyword("else")
		.ignored()
		.padded()
		.then_ignore(end())
		.to(Stmt::Preproc(Preproc::Else));

	let endif = text::keyword("endif")
		.ignored()
		.padded()
		.then_ignore(end())
		.to(Stmt::Preproc(Preproc::EndIf));

	version
		.or(include)
		.or(ifdef)
		.or(ifndef)
		.or(undef)
		.or(else_)
		.or(endif)
		.or(extension)
		.or(line)
		.or(error)
		.or(pragma)
		.or(any()
			.repeated()
			.then_ignore(end())
			.to(Stmt::Preproc(Preproc::Unsupported)))
}
