use chumsky::prelude::*;

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
			for expr in ast {
				print_expr(&expr, 0);
			}
		}
		println!("\r\nerrors: {errors:?}");
	}
}

fn print_expr(expr: &Expr, indent: usize) {
	match expr {
		Expr::Literal(s) => {
			print!(" Lit(\x1b[35m{s}\x1b[0m)")
		}
		Expr::Neg(e) => print_expr(e, indent + 1),
		Expr::Binary { left, op, right } => {
			print!(" (");
			print_expr(left, indent + 1);
			print!(" {op:?}");
			print_expr(right, indent + 1);
			print!(" )");
		}
		Expr::VarDecl {
			type_,
			ident,
			value,
		} => {
			print!(
				"\r\n{:indent$}\x1b[32mVar\x1b[0m(type=\x1b[91m{type_}\x1b[0m ident=\x1b[33m{ident}\x1b[0m) =",
				"",
				indent = indent * 4
			);
			print_expr(value, indent + 1);
		}
		Expr::FnDecl { type_, ident, body } => {
			print!(
				"\r\n{:indent$}\x1b[34mFn\x1b[0m(return=\x1b[91m{type_}\x1b[0m ident=\x1b[33m{ident}\x1b[0m) {{",
				"",
				indent = indent * 4
			);
			for inner in body {
				print_expr(inner, indent + 1);
			}
			print!("\r\n}}")
		}
	}
}

/// CST tokens.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[allow(unused)]
enum Token {
	Invalid,
	Num(String, NumType),
	Bool(bool),
	Ident(String),
	Type(String),
	// Keywords
	If,
	Else,
	For,
	Switch,
	Case,
	Default,
	Break,
	Return,
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
	Star,
	Underscore,
	LParen,
	RParen,
	LBracket,
	RBracket,
	LBrace,
	RBrace,
}

/// The different number types in the CST.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(unused)]
enum NumType {
	Normal,
	Oct,
	Hex,
	Float,
	Double,
}

/// Mathematical and comparison operation symbols.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(unused)]
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
	Not,
}

type Spanned<T> = (T, Span);
type Span = std::ops::Range<usize>;

fn lexer() -> impl Parser<char, Vec<Spanned<Token>>, Error = Simple<char>> {
	let ident = text::ident().map(|s| Token::Ident(s));

	let token = literals()
		.or(punctuation())
		.or(keywords())
		.or(ident)
		.recover_with(skip_then_retry_until([]));

	token.map_with_span(|t, s| (t, s)).padded().repeated()
}

/// Parse punctuation symbols that aren't mathematical/comparison operators.
fn punctuation() -> impl Parser<char, Token, Error = Simple<char>> {
	choice((
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
		//
		just('+').to(Token::Op(OpType::Add)),
		just('-').to(Token::Op(OpType::Sub)),
		just('*').to(Token::Op(OpType::Mul)),
		just('/').to(Token::Op(OpType::Div)),
	))
}

/// Parse keywords.
fn keywords() -> impl Parser<char, Token, Error = Simple<char>> {
	// Split because of limit. 'choice()' is a generic function for performance reasons and it only has 26 generic
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
		text::keyword("struct").to(Token::Struct),
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
fn literals() -> impl Parser<char, Token, Error = Simple<char>> {
	// Unsigned integer suffix.
	let suffix = filter(|c: &char| *c == 'u' || *c == 'U').or_not();

	let zero_valid = just('-')
		.or_not()
		.chain(just('0'))
		.chain::<char, _, _>(suffix)
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Normal));
	let zero_invalid = just('-')
		.or_not()
		.chain(just('0'))
		.chain::<char, _, _>(suffix)
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_alphanumeric())
				.repeated()
				.at_least(1),
		)
		.collect::<String>()
		.map(|_| Token::Invalid);

	let num = just('-')
		.or_not()
		.chain(filter(|c: &char| c.is_ascii_digit() && *c != '0'))
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
		.map(|_| Token::Invalid);

	let num_hex = just('-')
		.or_not()
		.then(just('0'))
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
		.map(|_| Token::Invalid);

	let num_oct = just('-')
		.or_not()
		.chain(just('0'))
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
		.map(|_| Token::Invalid);

	let num_float = just('-')
		.or_not()
		.chain(filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1))
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
		.map(|_| Token::Invalid);

	let num_float_exp = just('-')
		.or_not()
		.chain(filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1))
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
		.map(|_| Token::Invalid);

	let num_float_exp_no_decimal = just('-')
		.or_not()
		.chain(filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1))
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
		.map(|_| Token::Invalid);

	// Double specifier suffix.
	let lf = just('l').then(just('f')).or(just('L').then(just('F')));

	let num_double = just('-')
		.or_not()
		.chain(filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1))
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
		.map(|_| Token::Invalid);

	let num_double_exp = just('-')
		.or_not()
		.chain(filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1))
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
		.map(|_| Token::Invalid);

	let num_double_exp_no_decimal = just('-')
		.or_not()
		.chain(filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1))
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
		.map(|_| Token::Invalid);

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
