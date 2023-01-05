//! The evaluator for conditional directive expression.
//!
//! # Behaviour
//! The evaluator internally stores all values as `isize` numbers. Any integer nodes are converted from a `usize`
//! to an `isize`.
//!
//! Whenever an operation requires boolean values, the number is converted to a `bool` through the `num != 0`
//! comparison. Whenever an operation produces a boolean, the boolean is converted immediately to an `isize`
//! through the `b as isize` cast.
//!
//! ## Early returns
//! The evaluator returns `false` early in the following cases:
//! - An integer node could not be converted to a `isize`.
//! - A prefix operator lacks an operand.
//! - A binary operator lacks the right-hand side operand.
//! - Parenthesis lack an expression inside of them.
//! - The left-shift or right-shift operator would shift with overflow.
//!
//! ## Panics
//! By default, all operations overflow in release mode and panic in debug mode. The exception to this rule are the
//! left-shift and right-shift operators; they use checked arithmetic.

use super::{
	ast::{
		conditional::{Expr, ExprTy},
		Ident,
	},
	Macro,
};
use crate::{
	parser::ast::conditional::{BinOpTy, PreOpTy},
	Either3, Span,
};
use std::collections::{HashMap, VecDeque};

/// Evaluates an `#ifdef`/`#ifndef` directive.
pub(super) fn evaluate_def(
	ident: Ident,
	macros: &HashMap<String, (Span, Macro)>,
) -> bool {
	for (macro_ident, _) in macros {
		if macro_ident == &ident.name {
			return true;
		}
	}

	false
}

/// Evaluates an `#if`/`#elif` directive.
pub(super) fn evaluate_expr(
	expr: Expr,
	macros: &HashMap<String, (Span, Macro)>,
) -> bool {
	eval(expr, macros) != 0
}

/// An evaluated value.
#[derive(Debug)]
struct Val {
	v: isize,
	span: Span,
}

fn eval(expr: Expr, macros: &HashMap<String, (Span, Macro)>) -> isize {
	// A number of value `0` is treated as false, whilst any other numeric value is treated as true. Equally, a
	// boolean of value `false` is treated as 0, whilst of value `true` is treated as 1.  The values are stored as
	// integers by default, and converted to/from booleans where necessary.
	const FALSE: isize = 0;

	// Generate a Polish-Notation stack of the expression.
	let mut pn_stack = VecDeque::new();
	let mut stack = VecDeque::new();
	stack.push_front(expr);
	loop {
		let node = stack.pop_front().unwrap();
		match node.ty {
			ExprTy::Num(num) => pn_stack.push_back(Either3::A(Val {
				v: match num.try_into() {
					Ok(n) => n,
					Err(_) => return FALSE,
				},
				span: node.span,
			})),
			ExprTy::Prefix { op, expr } => {
				pn_stack.push_back(Either3::B(op));
				if let Some(expr) = expr {
					stack.push_front(*expr);
				} else {
					return FALSE;
				}
			}
			ExprTy::Binary { left, op, right } => {
				pn_stack.push_back(Either3::C(op));
				if let Some(right) = right {
					stack.push_front(*right);
				} else {
					return FALSE;
				}
				stack.push_front(*left);
			}
			ExprTy::Parens { expr } => {
				if let Some(expr) = expr {
					stack.push_front(*expr);
				} else {
					return FALSE;
				}
			}
			ExprTy::Defined { ident } => {
				let mut found = false;
				for (macro_ident, _) in macros {
					if macro_ident == &ident.name {
						found = true;
						break;
					}
				}
				pn_stack.push_back(Either3::A(Val {
					v: found as isize,
					span: node.span,
				}));
			}
		}

		if stack.is_empty() {
			break;
		}
	}

	// Consume the Polish-Notation stack and evaluate it.
	let mut eval_stack = VecDeque::new();
	loop {
		let v = pn_stack.pop_back().unwrap();
		match v {
			Either3::A(val) => eval_stack.push_back(val),
			Either3::B(pre) => match pre.ty {
				PreOpTy::Neg => {
					let val = eval_stack.pop_back().unwrap();
					eval_stack.push_back(Val {
						v: -val.v,
						span: Span::new(pre.span.start, val.span.end),
					});
				}
				PreOpTy::Flip => {
					let val = eval_stack.pop_back().unwrap();
					eval_stack.push_back(Val {
						v: !val.v,
						span: Span::new(pre.span.start, val.span.end),
					});
				}
				PreOpTy::Not => {
					let val = eval_stack.pop_back().unwrap();
					eval_stack.push_back(Val {
						v: (!(val.v != 0)) as isize,
						span: Span::new(pre.span.start, val.span.end),
					});
				}
			},
			Either3::C(bin) => match bin.ty {
				BinOpTy::Add
				| BinOpTy::Sub
				| BinOpTy::Mul
				| BinOpTy::Div
				| BinOpTy::Rem
				| BinOpTy::And
				| BinOpTy::Or
				| BinOpTy::Xor => {
					let left = eval_stack.pop_back().unwrap();
					let right = eval_stack.pop_back().unwrap();

					let op = match bin.ty {
						BinOpTy::Add => |x, y| x + y,
						BinOpTy::Sub => |x, y| x - y,
						BinOpTy::Mul => |x, y| x * y,
						BinOpTy::Div => |x, y| x / y,
						BinOpTy::Rem => |x, y| x % y,
						BinOpTy::And => |x, y| x & y,
						BinOpTy::Or => |x, y| x | y,
						BinOpTy::Xor => |x, y| x ^ y,
						_ => unreachable!(),
					};
					eval_stack.push_back(Val {
						v: op(left.v, right.v),
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::LShift | BinOpTy::RShift => {
					let left = eval_stack.pop_back().unwrap();
					let right = eval_stack.pop_back().unwrap();

					let op: fn(u32, u32) -> Option<u32> = match bin.ty {
						BinOpTy::LShift => |x, y| x.checked_shl(y),
						BinOpTy::RShift => |x, y| x.checked_shr(y),
						_ => unreachable!(),
					};
					eval_stack.push_back(Val {
						v: match op(left.v as u32, right.v as u32) {
							Some(u) => u as isize,
							None => return FALSE,
						},
						span: Span::new(left.span.start, right.span.end),
					});
				}
				BinOpTy::AndAnd
				| BinOpTy::OrOr
				| BinOpTy::EqEq
				| BinOpTy::NotEq
				| BinOpTy::Gt
				| BinOpTy::Lt
				| BinOpTy::Ge
				| BinOpTy::Le => {
					let left = eval_stack.pop_back().unwrap();
					let right = eval_stack.pop_back().unwrap();

					let op = match bin.ty {
						BinOpTy::AndAnd => |x, y| (x != 0) && (y != 0),
						BinOpTy::OrOr => |x, y| (x != 0) || (y != 0),
						BinOpTy::EqEq => |x, y| x == y,
						BinOpTy::NotEq => |x, y| x != y,
						BinOpTy::Gt => |x, y| x > y,
						BinOpTy::Lt => |x, y| x < y,
						BinOpTy::Ge => |x, y| x >= y,
						BinOpTy::Le => |x, y| x <= y,
						_ => unreachable!(),
					};
					eval_stack.push_back(Val {
						v: op(left.v, right.v) as isize,
						span: Span::new(left.span.start, right.span.end),
					});
				}
			},
		}

		if pn_stack.is_empty() {
			break;
		}
	}

	if eval_stack.len() != 1 {
		unreachable!("After processing the conditional evaluation stack, we are left with more than one value. This should not happen.")
	}

	eval_stack.remove(0).unwrap().v
}

#[cfg(test)]
mod tests {
	//! Behaviour tests for the conditional expression evaluator, and also of the conditional expression
	//! parser and lexer since those are prerequisite steps.

	use crate::{parser::Macro, span};
	use std::collections::HashMap;

	/// Asserts that the source string, once parsed and evaluated, matches the desired result. The source string
	/// must consist of an `#if` or `#elif` conditional directive only.
	macro_rules! assert_eval {
		($macros:expr, $src:expr, $result:expr) => {
			let mut tokens = crate::lexer::parse_with_version(
				$src,
				crate::GlslVersion::_450,
			)
			.0;
			match tokens.remove(0) {
				(crate::lexer::Token::Directive(d), _) => {
					match d {
						crate::lexer::preprocessor::TokenStream::If {
							tokens,
							..
						}
						| crate::lexer::preprocessor::TokenStream::ElseIf {
							tokens,
							..
						} => {
							let (expr, _, _) = crate::parser::conditional_expression::cond_parser(
								tokens, &$macros, crate::SpanEncoding::Utf16,
							);
							assert_eq!(
								super::eval(expr.unwrap(), &$macros),
								$result
							);
						}
						_ => panic!(),
					}
				}
				_ => panic!(),
			}
		};
		($src:expr, $result:expr) => {
			let mut tokens = crate::lexer::parse_with_version(
				$src,
				crate::GlslVersion::_450,
			)
			.0;
			match tokens.remove(0) {
				(crate::lexer::Token::Directive(d), _) => match d {
					crate::lexer::preprocessor::TokenStream::If {
						tokens,
						..
					}
					| crate::lexer::preprocessor::TokenStream::ElseIf {
						tokens,
						..
					} => {
						let (expr, _, _) =
							crate::parser::conditional_expression::cond_parser(
								tokens,
								&HashMap::new(),
								crate::SpanEncoding::Utf16,
							);
						assert_eq!(
							super::eval(expr.unwrap(), &HashMap::new()),
							$result
						);
					}
					_ => panic!(),
				},
				_ => panic!(),
			}
		};
	}

	#[test]
	fn single_value() {
		assert_eval!("#if 0", 0);
		assert_eval!("#if 1", 1);
		assert_eval!("#if 50", 50);
		assert_eval!("#if -100", -100);
		assert_eval!("#if undefined", 0);
	}

	#[test]
	fn pre() {
		assert_eval!("#if -5", -5);
		assert_eval!("#if ~1", -2);
		assert_eval!("#if !0", 1);
		assert_eval!("#if !1", 0);
	}

	#[test]
	fn defined() {
		let mut macros = HashMap::new();
		macros.insert("FOO".into(), (span(0, 0), Macro::Object(vec![])));
		assert_eval!(macros, "#if defined BAR", 0);
		assert_eval!(macros, "#if defined FOO", 1);
		assert_eval!(macros, "#if defined ( FOO )", 1);
	}

	#[test]
	fn binary() {
		assert_eval!("#if 5 + 6", 11);
		assert_eval!("#if 5 - 5", 0);
		assert_eval!("#if 5 * 5 - 25", 0);
		assert_eval!("#if 5 * 5 - 25 - 0", 0);
		assert_eval!("#if 16 / 16 - 1", 0);
		assert_eval!("#if 2 - 1 - 1", 0);
		assert_eval!("#if 2 - 1 - 0", 1);
		assert_eval!("#if 5 * 4 / 2 - 10 + 10 - 9", 1);
		assert_eval!("#if 6 - 7 * 2 + 2 - 0", -6);
		assert_eval!("#if 100 < 0", 0);
		assert_eval!("#if 100 == 100", 1);
		assert_eval!("#if 0 != 1", 1);
		assert_eval!("#if 5 <= 5", 1);
		assert_eval!("#if 3 >= 3", 1);
		assert_eval!("#if 5 & 12", 4);
		assert_eval!("#if 5 | 12", 13);
		assert_eval!("#if 5 ^ 12", 9);
		assert_eval!("#if 300 >> 1", 150);
		assert_eval!("#if 300 << 1", 600);
	}

	#[test]
	fn paren() {
		assert_eval!("#if (1)", 1);
		assert_eval!("#if (1 - 2)", -1);
		assert_eval!("#if 5 * (7 - 4)", 15);
		assert_eval!("#if 5 * 7 - 0 / (7 - 6) * 2 - 1", 34);
		assert_eval!("#if (6 > 3) + 1", 2);
		assert_eval!("#if (4 == 4) && 6", 1);
		assert_eval!("#if (6 == 0) || (5 == 5)", 1);
	}
}
