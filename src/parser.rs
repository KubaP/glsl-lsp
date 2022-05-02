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

fn print_expr(expr: &Expr, indent: usize) {
	match expr {
		Expr::Lit(s) => {
			print!(" Lit(\x1b[35m{s}\x1b[0m)")
		}
		Expr::Ident(s) => print!(" Ident(\x1b[33m{s}\x1b[0m)"),
		Expr::Neg(e) => print_expr(e, indent + 1),
		Expr::Binary { left, op, right } => {
			print!(" (");
			print_expr(left, indent + 1);
			print!(" {op:?}");
			print_expr(right, indent + 1);
			print!(" )");
		}
		Expr::Fn { ident, args } => {
			print!(" \x1b[34m{ident}\x1b[0m(");
			for arg in args {
				print_expr(arg, indent + 1);
			}
			print!(" )");
		}
		Expr::Array { type_, args } => {
			print!(" Arr(type={type_})(");
			for arg in args {
				print_expr(arg, indent + 1);
			}
			print!(" )");
		}
		Expr::InitList(v) => {
			print!(" Init{{");
			for arg in v {
				print_expr(arg, indent + 1);
			}
			print!(" }}");
		}
	}
}

fn print_stmt(stmt: &Stmt, indent: usize) {
	match stmt {
		Stmt::Empty => print!(
			"\r\n{:indent$}(\x1b[97mEmpty\x1b[0m)",
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
				"\r\n{:indent$}\x1b[32mVar\x1b[0m(type={type_} ident=\x1b[33m{ident}\x1b[0m",
				"",
				indent = indent * 4
			);
			if *is_const {
				print!(" \x1b[4mconst\x1b[0m");
			}
			print!(")");
			if let Some(value) = value {
				print!(" =");
				print_expr(value, indent + 1);
			}
		}
		Stmt::FnDecl {
			type_,
			ident,
			params,
			body,
		} => {
			print!(
				"\r\n{:indent$}\x1b[34mFn\x1b[0m(return=\x1b[91m{type_}\x1b[0m ident=\x1b[33m{ident}\x1b[0m, args=[",
				"",
				indent = indent * 4
			);
			for (type_, ident) in params {
				print!(" \x1b[91m{type_}\x1b[0m \x1b[33m{ident}\x1b[0m,");
			}
			print!("]) {{");
			for inner in body {
				print_stmt(inner, indent + 1);
			}
			print!("\r\n}}")
		}
		Stmt::FnCall { ident, args } => {
			print!(
				"\r\n{:indent$}\x1b[34m{ident}\x1b[0m(",
				"",
				indent = indent * 4
			);
			for arg in args {
				print_expr(arg, indent + 1);
			}
			print!(" )");
		}
		Stmt::Preproc(p) => print!(
			"\r\n{:indent$}\x1b[4mPreproc({p})\x1b[0m",
			"",
			indent = indent * 4
		),
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
	Directive(String),
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
pub enum NumType {
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

	let ident = text::ident().map(|s| Token::Ident(s));
	let token = literals()
		.or(punctuation())
		.or(keywords())
		.or(ident)
		.padded();

	directive
		.or(token)
		.map_with_span(|t, s| (t, s))
		.repeated()
		.recover_with(skip_then_retry_until([]))
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
		.map(|_| Token::Invalid);

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
		.map(|_| Token::Invalid);

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
		.map(|_| Token::Invalid);

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
		.map(|_| Token::Invalid);

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
		.map(|_| Token::Invalid);

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
		.map(|_| Token::Invalid);

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
		.map(|_| Token::Invalid);

	// Double specifier suffix.
	let lf = just('l').then(just('f')).or(just('L').then(just('F')));

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
		.map(|_| Token::Invalid);

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
		.map(|_| Token::Invalid);

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

		let val = fn_call.or(filter(|t: &Token| match t {
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

		let atom =
			val.or(expr.delimited_by(just(Token::LParen), just(Token::RParen)));

		let op = filter(|t: &Token| match t {
			Token::Op(op) => match op {
				OpType::Sub => true,
				_ => false,
			},
			_ => false,
		});

		let neg = op
			.repeated()
			.then(atom)
			.foldr(|_op, rhs| Expr::Neg(Box::new(rhs)));

		let op = filter(|t: &Token| match t {
			Token::Op(op) => match op {
				OpType::Mul | OpType::Div => true,
				_ => false,
			},
			_ => false,
		});
		let product = neg
			.clone()
			.then(
				op.map(|t| match t {
					Token::Op(op) => op,
					_ => unreachable!(),
				})
				.then(neg)
				.repeated(),
			)
			.foldl(|lhs, (op, rhs)| Expr::Binary {
				left: Box::from(lhs),
				op,
				right: Box::from(rhs),
			});

		let op = filter(|t: &Token| match t {
			Token::Op(op) => match op {
				OpType::Add | OpType::Sub => true,
				_ => false,
			},
			_ => false,
		});
		let sum = product
			.clone()
			.then(
				op.map(|t| match t {
					Token::Op(op) => op,
					_ => unreachable!(),
				})
				.then(product)
				.repeated(),
			)
			.foldl(|lhs, (op, rhs)| Expr::Binary {
				left: Box::from(lhs),
				op,
				right: Box::from(rhs),
			});

		sum
	});

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
		.then(arr.repeated())
		.then_ignore(just(Token::Semi))
		.map(|(((is_const, type_ident), ident), size)| Stmt::VarDecl {
			type_: Type::new(type_ident, size),
			ident,
			value: None,
			is_const,
		});

	// Function call on its own.
	let fn_call = ident
		.then(
			expr.clone()
				.separated_by(just(Token::Comma))
				.delimited_by(just(Token::LParen), just(Token::RParen)),
		)
		.then_ignore(just(Token::Semi))
		.map(|(ident, args)| Stmt::FnCall { ident, args });

	// Empty statement.
	let empty = just(Token::Semi).map(|_| Stmt::Empty);

	// All statements.
	let stmt = var
		.clone()
		.or(var_uninit.clone())
		.or(fn_call)
		.or(preproc.clone())
		.or(empty.clone());

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

	func.or(var).or(var_uninit).or(empty).or(preproc).repeated()
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
