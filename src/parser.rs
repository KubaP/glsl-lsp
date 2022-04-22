use chumsky::prelude::*;

pub fn parse(source: &str) {
	let cst = lexer().parse(source);

	println!("{cst:?}");
}

/// CST tokens.
#[derive(Debug, Clone)]
enum Token {
	Num(String, NumType),
	Bool(bool),
	Ident(String),
	// Keywords
	Const,
	// Punctuation
	Eq,
	Semi,
}

/// The different number types in the CST.
#[derive(Debug, Clone, Copy)]
enum NumType {
	Normal,
	Oct,
	Hex,
	Float,
}

fn lexer() -> impl Parser<char, Token, Error = Simple<char>> {
	literals()
}

/// Parse literal values, i.e. numbers and booleans.
fn literals() -> impl Parser<char, Token, Error = Simple<char>> {
	let u_suffix = just('u').or_not().or(just('U').or_not());

	let zero = just('-')
		.or_not()
		.chain(just('0'))
		.chain::<char, _, _>(u_suffix)
		.padded()
		.then_ignore(end())
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Normal));

	let num = just('-')
		.or_not()
		.chain(filter(|c: &char| c.is_ascii_digit() && *c != '0'))
		.chain::<char, _, _>(filter(|c: &char| c.is_ascii_digit()).repeated())
		.chain::<char, _, _>(u_suffix)
		.padded()
		.then_ignore(end())
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Normal));

	let num_hex = just('-')
		.or_not()
		.then(just('0'))
		.then(just('x'))
		.chain::<char, _, _>(
			filter::<_, _, Simple<char>>(|c: &char| c.is_ascii_hexdigit())
				.repeated()
				.at_least(1),
		)
		.chain::<char, _, _>(u_suffix)
		.padded()
		.then_ignore(end())
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Hex));

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
		.chain::<char, _, _>(u_suffix)
		.padded()
		.then_ignore(end())
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Oct));

	let num_float = just('-')
		.or_not()
		.chain(filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1))
		.chain(just('.'))
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1),
		)
		.padded()
		.then_ignore(end())
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Float));

	let num_double_lowercase = just('-')
		.or_not()
		.chain(filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1))
		.chain(just('.'))
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1),
		)
		.chain::<char, _, _>(just('l').chain(just('f')))
		.padded()
		.then_ignore(end())
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Float));

	let num_double_uppercase = just('-')
		.or_not()
		.chain(filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1))
		.chain(just('.'))
		.chain::<char, _, _>(
			filter(|c: &char| c.is_ascii_digit()).repeated().at_least(1),
		)
		.chain::<char, _, _>(just('L').chain(just('F')))
		.padded()
		.then_ignore(end())
		.collect::<String>()
		.map(|s| Token::Num(s, NumType::Float));

	let b_true = text::keyword("true")
		.padded()
		.then_ignore(end())
		.map(|_| Token::Bool(true));
	let b_false = text::keyword("false")
		.padded()
		.then_ignore(end())
		.map(|_| Token::Bool(false));

	zero.or(num_double_lowercase)
		.or(num_double_uppercase)
		.or(num_float)
		.or(num_hex)
		.or(num_oct)
		.or(num)
		.or(b_true)
		.or(b_false)
}
