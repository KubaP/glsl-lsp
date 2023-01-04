//! Behaviour tests for the [`Walker`].
//!
//! Mainly tests to ensure the behaviour of advancing to the next token works correctly, i.e. correctly stepping
//! into macros and switching source streams if conditional compilation is present. You may notice that any
//! specified spans are `(0,0)`; that's because these tests are not checking spans at all.
//!
//! Currently only the `RootTokenStreamProvider` is being tested.

use super::{Macro, RootTokenStreamProvider, Walker};
use crate::{
	lexer::{self, NumType, Token},
	parser::ast::Ident,
	span, GlslVersion,
};

macro_rules! assert_token {
	($walker:expr, $token:expr) => {
		assert_eq!($walker.get().unwrap().0, $token);
	};
}
macro_rules! assert_done {
	($walker:expr) => {
		assert!($walker.is_done());
	};
}
macro_rules! register_obj_macro {
	($walker:expr, $name:expr, $($token:expr),*) => {
		$walker.register_macro($name.into(), span(0, 0), Macro::Object(vec![
			$(($token, span(0, 0)))*
		]));
	};
	($walker:expr, $name:expr) => {
		$walker.register_macro($name.into(), span(0, 0), Macro::Object(vec![]));
	};
}
macro_rules! register_fn_macro {
	($walker:expr, $name:expr, $params:expr, $($token:expr),*) => {
		$walker.register_macro($name.into(), span(0, 0), Macro::Function {
			params: $params,
			body: vec![
				$(
					($token, span(0, 0)),
				)*
			]});
	};
	($walker:expr, $name:expr, $params:expr) => {
		$walker.register_macro($name.into(), span(0, 0), Macro::Function {
			params: $params,
			body: vec![]
		});
	};
}

/// From a source with no conditional compilation.
mod single_source {
	use super::*;
	use crate::SpanEncoding;

	#[test]
	fn no_macro() {
		let tokens = lexer::parse_with_version(
			"int foo 9 /*...*/bar",
			GlslVersion::_450,
		)
		.0;
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(vec![tokens], 10000),
			SpanEncoding::Utf16,
		);
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert_token!(walker, Token::Ident("bar".into()));
		walker.advance();
		assert_done!(walker);
	}

	#[test]
	fn object_macro() {
		// #define BAR bar
		let tokens = lexer::parse_with_version(
			r#"
		int foo 9 /*...*/BAR
		"#,
			GlslVersion::_450,
		)
		.0;
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(vec![tokens], 10000),
			SpanEncoding::Utf16,
		);
		register_obj_macro!(walker, "BAR", Token::Ident("bar".into()));
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert_token!(walker, Token::Ident("bar".into()));
		walker.advance();
		assert_done!(walker);
	}

	#[test]
	fn nested_object_macro() {
		// #define FOO foo
		// #define BAR FOO
		let tokens = lexer::parse_with_version(
			r#"
		int foo 9 /*...*/BAR
		"#,
			GlslVersion::_450,
		)
		.0;
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(vec![tokens], 10000),
			SpanEncoding::Utf16,
		);
		register_obj_macro!(walker, "FOO", Token::Ident("foo".into()));
		register_obj_macro!(walker, "BAR", Token::Ident("FOO".into()));
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_done!(walker);
	}

	#[test]
	fn empty_object_macro() {
		// #define FOO
		let tokens = lexer::parse_with_version(
			r#"
		int foo 9 /*...*/FOO
		"#,
			GlslVersion::_450,
		)
		.0;
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(vec![tokens], 10000),
			SpanEncoding::Utf16,
		);
		register_obj_macro!(walker, "FOO");
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert_done!(walker);
	}

	#[test]
	fn function_macro() {
		// #define BAR(A) A
		let tokens = lexer::parse_with_version(
			r#"
		int foo 9 /*...*/BAR(p)
		"#,
			GlslVersion::_450,
		)
		.0;
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(vec![tokens], 10000),
			SpanEncoding::Utf16,
		);
		register_fn_macro!(
			walker,
			"BAR",
			vec![Ident {
				name: "A".into(),
				span: span(0, 0)
			}],
			Token::Ident("A".into())
		);
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert_token!(walker, Token::Ident("p".into()));
		walker.advance();
		assert!(walker.is_done());
	}

	#[test]
	fn nested_function_macro() {
		// #define FOO(_1) _1
		// #define BAR(A) FOO(A)
		let tokens = lexer::parse_with_version(
			r#"
		int foo 9 /*...*/BAR(p)
		"#,
			GlslVersion::_450,
		)
		.0;
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(vec![tokens], 10000),
			SpanEncoding::Utf16,
		);
		register_fn_macro!(
			walker,
			"FOO",
			vec![Ident {
				name: "_1".into(),
				span: span(0, 0)
			}],
			Token::Ident("_1".into())
		);
		register_fn_macro!(
			walker,
			"BAR",
			vec![Ident {
				name: "A".into(),
				span: span(0, 0)
			}],
			Token::Ident("FOO".into()),
			Token::LParen,
			Token::Ident("A".into()),
			Token::RParen
		);
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert_token!(walker, Token::Ident("p".into()));
		walker.advance();
		assert!(walker.is_done());
	}

	#[test]
	fn empty_function_macro() {
		// #define BAR(A)
		let tokens = lexer::parse_with_version(
			r#"
		int foo 9 /*...*/BAR(p)
		"#,
			GlslVersion::_450,
		)
		.0;
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(vec![tokens], 10000),
			SpanEncoding::Utf16,
		);
		register_fn_macro!(
			walker,
			"BAR",
			vec![Ident {
				name: "A".into(),
				span: span(0, 0)
			}]
		);
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert!(walker.is_done());
	}
}

/// From a source containing conditional compilation.
mod multi_source {
	use super::*;
	use crate::SpanEncoding;

	#[test]
	fn no_macro() {
		let tokens = vec![
			lexer::parse_with_version("int foo 9", GlslVersion::_450).0,
			lexer::parse_with_version("/*...*/bar", GlslVersion::_450).0,
		];
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(tokens, 10000),
			SpanEncoding::Utf16,
		);
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert_token!(walker, Token::Ident("bar".into()));
		walker.advance();
		assert_done!(walker);
	}

	#[test]
	fn object_macro() {
		// #define BAR bar
		let tokens = vec![
			lexer::parse_with_version("int foo 9/*...*/", GlslVersion::_450).0,
			lexer::parse_with_version("BAR", GlslVersion::_450).0,
		];
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(tokens, 10000),
			SpanEncoding::Utf16,
		);
		register_obj_macro!(walker, "BAR", Token::Ident("bar".into()));
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert_token!(walker, Token::Ident("bar".into()));
		walker.advance();
		assert_done!(walker);
	}

	#[test]
	fn nested_object_macro() {
		// #define FOO foo
		// #define BAR FOO
		let tokens = vec![
			lexer::parse_with_version("int foo 9/*...*/", GlslVersion::_450).0,
			lexer::parse_with_version("BAR", GlslVersion::_450).0,
		];
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(tokens, 10000),
			SpanEncoding::Utf16,
		);
		register_obj_macro!(walker, "FOO", Token::Ident("foo".into()));
		register_obj_macro!(walker, "BAR", Token::Ident("FOO".into()));
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_done!(walker);
	}

	#[test]
	fn empty_object_macro() {
		// #define FOO
		let tokens = vec![
			lexer::parse_with_version("int foo 9/*...*/", GlslVersion::_450).0,
			lexer::parse_with_version("FOO", GlslVersion::_450).0,
		];
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(tokens, 10000),
			SpanEncoding::Utf16,
		);
		register_obj_macro!(walker, "FOO");
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert_done!(walker);
	}

	#[test]
	fn function_macro() {
		// #define BAR(A) A
		let tokens = vec![
			lexer::parse_with_version("int foo 9/*...*/", GlslVersion::_450).0,
			lexer::parse_with_version("BAR(p)", GlslVersion::_450).0,
		];
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(tokens, 10000),
			SpanEncoding::Utf16,
		);
		register_fn_macro!(
			walker,
			"BAR",
			vec![Ident {
				name: "A".into(),
				span: span(0, 0)
			}],
			Token::Ident("A".into())
		);
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert_token!(walker, Token::Ident("p".into()));
		walker.advance();
		assert!(walker.is_done());
	}

	#[test]
	fn nested_function_macro() {
		// #define FOO(_1) _1
		// #define BAR(A) FOO(A)
		let tokens = vec![
			lexer::parse_with_version("int foo 9/*...*/", GlslVersion::_450).0,
			lexer::parse_with_version("BAR(p)", GlslVersion::_450).0,
		];
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(tokens, 10000),
			SpanEncoding::Utf16,
		);
		register_fn_macro!(
			walker,
			"FOO",
			vec![Ident {
				name: "_1".into(),
				span: span(0, 0)
			}],
			Token::Ident("_1".into())
		);
		register_fn_macro!(
			walker,
			"BAR",
			vec![Ident {
				name: "A".into(),
				span: span(0, 0)
			}],
			Token::Ident("FOO".into()),
			Token::LParen,
			Token::Ident("A".into()),
			Token::RParen
		);
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert_token!(walker, Token::Ident("p".into()));
		walker.advance();
		assert!(walker.is_done());
	}

	#[test]
	fn empty_function_macro() {
		// #define BAR(A)
		let tokens = vec![
			lexer::parse_with_version("int foo 9/*...*/", GlslVersion::_450).0,
			lexer::parse_with_version("BAR(p)", GlslVersion::_450).0,
		];
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(tokens, 10000),
			SpanEncoding::Utf16,
		);
		register_fn_macro!(
			walker,
			"BAR",
			vec![Ident {
				name: "A".into(),
				span: span(0, 0)
			}]
		);
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert!(walker.is_done());
	}
}

mod function_macros {
	use super::*;
	use crate::SpanEncoding;

	#[test]
	fn interspersed_comments() {
		// #define BAR(A) A
		let tokens = lexer::parse_with_version(
			r#"
		int foo 9 BAR/*...*/(p /*.*/)
		"#,
			GlslVersion::_450,
		)
		.0;
		let mut walker = Walker::new(
			RootTokenStreamProvider::new(vec![tokens], 10000),
			SpanEncoding::Utf16,
		);
		register_fn_macro!(
			walker,
			"BAR",
			vec![Ident {
				name: "A".into(),
				span: span(0, 0)
			}],
			Token::Ident("A".into())
		);
		assert_token!(walker, Token::Ident("int".into()));
		walker.advance();
		assert_token!(walker, Token::Ident("foo".into()));
		walker.advance();
		assert_token!(
			walker,
			Token::Num {
				type_: NumType::Dec,
				num: "9".into(),
				suffix: None
			}
		);
		walker.advance();
		assert_token!(walker, Token::Ident("p".into()));
		walker.advance();
		assert!(walker.is_done());
	}
}
