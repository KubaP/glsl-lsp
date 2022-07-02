#![allow(unused)]
use crate::{
	ast::{Either, Expr, Ident, Lit},
	lexer::{lexer, Op, Token},
	parser::Walker,
	span::{span, Span, Spanned},
};
use std::{collections::VecDeque, iter::Peekable, slice::Iter};

pub fn expr_parser(walker: &mut Walker) -> Option<Expr> {
	let start_position = match walker.peek() {
		Some((_, span)) => span.start,
		None => return None,
	};
	let mut parser = ShuntingYard {
		stack: VecDeque::new(),
		operators: VecDeque::new(),
		groups: VecDeque::new(),
		start_position,
	};
	parser.parse(walker);
	parser.create_ast()
}

/*
Useful links related to expression parsing:

https://petermalmgren.com/three-rust-parsers/
	- recursive descent parser

https://wcipeg.com/wiki/Shunting_yard_algorithm
	- shunting yard overview & algorithm extensions

https://erikeidt.github.io/The-Double-E-Method
	- stateful shunting yard for unary support

https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
https://matklad.github.io/2020/04/15/from-pratt-to-dijkstra.html
	- two parter, first writing a pratt parser, and then refactoring into a shunting yard parser with a slightly
	  different approach
*/

#[derive(Debug, PartialEq)]
enum Group {
	/// A bracket group, `(...)`.
	///
	/// *Note:* Whilst there is currently no real use to storing bracket groups in the AST, keeping track of this
	/// in the shunting yard is necessary to correctly deal with lists within bracket groups, so this should never
	/// be removed.
	Bracket,
	/// An index operator `[...]`. `bool` notes whether there is an expression within the `[...]` brackets.
	Index(bool),
	/// A function call `fn(...)`.
	Fn(usize),
	/// An initializer list `{...}`.
	Init(usize),
	/// An array constructor `type[...](...)`.
	ArrInit(usize),
	/// A comma-seperated list **outside** of function calls, array constructors and initializer lists `..., ...`.
	///
	/// # Invariants
	/// This only exists if the surrounding `Group` is not of type `Group::Fn|Init|ArrInit|List`. (You can't have
	/// a list within a list since there are no delimiters, and commas within the other groups won't create an
	/// inner list group).
	List(usize),
}

struct ShuntingYard {
	/// The final output stack in RPN.
	stack: VecDeque<Either<Spanned<Expr>, Spanned<Op>>>,
	/// Temporary stack to hold operators.
	operators: VecDeque<Spanned<Op>>,
	/// Temporary stack to hold expression groups. The top-most entry is the group being currently parsed.
	///
	/// - `1` - The starting position of this group, e.g. `>fn(...` or `>{...`.
	/// - `2` - The starting position of the inner contents of this group, e.g. `fn(>...` or `{>...`.
	groups: VecDeque<(Group, usize, usize)>,
	/// The start position of the first span in this expression.
	start_position: usize,
}

impl ShuntingYard {
	/// Pushes an operator onto the stack, potentially popping any operators which have a greater precedence than
	/// the operator being pushed.
	fn push_operator(&mut self, op: Spanned<Op>) {
		while self.operators.back().is_some() {
			let (back, _) = self.operators.back().unwrap();

			if *back == Op::BracketStart
				|| *back == Op::IndexStart
				|| *back == Op::FnStart
				|| *back == Op::InitStart
			{
				// Group delimiter start operators always have the highest precedence, so we don't need to check
				// further.
				break;
			}

			let (op, _) = op;

			// This is done to make `ObjAccess` right-associative.
			if op == Op::ObjAccess && *back == Op::ObjAccess {
				let moved_op = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved_op));
				break;
			}

			if op.precedence() < back.precedence() {
				let moved_op = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved_op));
			} else {
				// If the precedence is greater, we aren't going to be moving any operators to the stack anymore,
				// so we can exit the loop.
				break;
			}
		}
		self.operators.push_back(op);
	}

	/// # Invariants
	/// Assumes that `self.group.back()` is of type [`Group::Bracket`].
	///
	/// `span_end` is the position which marks the end of this parenthesis group.
	fn collapse_bracket(&mut self, span_end: usize, invalidate: bool) {
		let (group, group_start, _) = self.groups.pop_back().unwrap();

		if let Group::Bracket = group {
			while self.operators.back().is_some() {
				let (op, span) = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op {
						Op::FnStart => println!("Mismatch between operator stack (Op::FnStart) and group stack (Group::Bracket)!"),
						Op::IndexStart => println!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Bracket)!"),
						Op::InitStart => println!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Bracket)!"),
						Op::ArrInitStart => println!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Bracket)!"),
						_ => {}
					}
				}

				if op == Op::BracketStart {
					self.stack.push_back(Either::Right((
						Op::Paren,
						Span {
							start: span.start,
							end: span_end,
						},
					)));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right((op, span)));
				}
			}

			if invalidate {
				self.invalidate_range(group_start, span_end, false);
			}
		} else {
			unreachable!()
		}
	}

	/// # Invariants
	/// Assumes that `self.group.back()` is of type [`Group::Fn`].
	///
	/// `span_end` is the position which marks the end of this function call.
	fn collapse_fn(&mut self, span_end: usize, invalidate: bool) {
		let (group, group_start, _) = self.groups.pop_back().unwrap();

		if let Group::Fn(count) = group {
			while self.operators.back().is_some() {
				let (op, span) = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op {
						Op::BracketStart => println!("Mismatch between operator stack (Op::BracketStart) and group stack (Group::Fn)!"),
						Op::IndexStart => println!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Fn)!"),
						Op::InitStart => println!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Fn)!"),
						Op::ArrInitStart => println!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Fn)!"),
						_ => {}
					}
				}

				if op == Op::FnStart {
					// The first expression will always be the `Expr::Ident` containing the function identifier,
					// hence the `count + 1`.
					self.stack.push_back(Either::Right((
						Op::FnCall(count + 1),
						Span {
							start: span.start,
							end: span_end,
						},
					)));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right((op, span)));
				}
			}

			if invalidate {
				self.invalidate_range(group_start, span_end, false);
			}
		} else {
			unreachable!()
		}
	}

	/// # Invariants
	/// Assumes that `self.group.back()` is of type [`Group::Index`].
	///
	/// `span_end` is the position which marks the end of this index operator.
	fn collapse_index(&mut self, span_end: usize, invalidate: bool) {
		let (group, group_start, _) = self.groups.pop_back().unwrap();

		if let Group::Index(contains_i) = group {
			while self.operators.back().is_some() {
				let (op, span) = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op {
						Op::BracketStart => println!("Mismatch between operator stack (Op::BracketStart) and group stack (Group::Index)!"),
						Op::FnStart => println!("Mismatch between operator stack (Op::FnStart) and group stack (Group::Index)!"),
						Op::InitStart => println!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Index)!"),
						Op::ArrInitStart => println!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Index)!"),
						_ => {}
					}
				}

				if op == Op::IndexStart {
					self.stack.push_back(Either::Right((
						Op::Index(contains_i),
						Span {
							start: span.start,
							end: span_end,
						},
					)));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right((op, span)));
				}
			}

			if invalidate {
				self.invalidate_range(group_start, span_end, true);
			}
		} else {
			unreachable!()
		}
	}

	/// # Invariants
	/// Assumes that `self.group.back()` is of type [`Group::Init`].
	fn collapse_init(&mut self, span_end: usize, invalidate: bool) {
		let (group, group_start, _) = self.groups.pop_back().unwrap();

		if let Group::Init(count) = group {
			while self.operators.back().is_some() {
				let (op, span) = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op {
						Op::BracketStart => println!("Mismatch between operator stack (Op::BracketStart) and group stack (Group::Init)!"),
						Op::IndexStart => println!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Init)!"),
						Op::FnStart => println!("Mismatch between operator stack (Op::FnStart) and group stack (Group::Init)!"),
						Op::ArrInitStart => println!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Init)!"),
						_ => {}
					}
				}

				if op == Op::InitStart {
					self.stack.push_back(Either::Right((
						Op::Init(count),
						Span {
							start: span.start,
							end: span_end,
						},
					)));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right((op, span)));
				}
			}

			if invalidate {
				self.invalidate_range(group_start, span_end, false);
			}
		} else {
			unreachable!()
		}
	}

	/// # Invariants
	/// Assumes that `self.group.back()` is of type [`Group::ArrInit`].
	fn collapse_arr_init(&mut self, span_end: usize, invalidate: bool) {
		let (group, group_start, _) = self.groups.pop_back().unwrap();

		if let Group::ArrInit(count) = group {
			while self.operators.back().is_some() {
				let (op, span) = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op {
						Op::BracketStart => println!("Mismatch between operator stack (Op::BracketStart) and group stack (Group::ArrInit)!"),
						Op::IndexStart => println!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::ArrInit)!"),
						Op::FnStart => println!("Mismatch between operator stack (Op::FnStart) and group stack (Group::ArrInit)!"),
						Op::InitStart => println!("Mismatch between operator stack (Op::InitStart) and group stack (Group::ArrInit)!"),
						_ => {}
					}
				}

				if op == Op::ArrInitStart {
					// The first expression will always be the `Expr::Index` containing the identifier/item and the
					// array index, hence the `count + 1`.
					self.stack.push_back(Either::Right((
						Op::ArrInit(count + 1, true),
						Span {
							start: span.start,
							end: span_end,
						},
					)));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right((op, span)));
				}
			}

			if invalidate {
				self.invalidate_range(group_start, span_end, false);
			}
		} else {
			unreachable!()
		}
	}

	/// # Invariants
	/// Assumes that `self.group.back()` is of type [`Group::List`].
	fn collapse_list(&mut self, span_end: usize, invalidate: bool) {
		let (group, group_start, _) = self.groups.pop_back().unwrap();

		if let Group::List(count) = group {
			let mut start_span = self.start_position;
			while self.operators.back().is_some() {
				let (op, span) = self.operators.back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op {
						Op::FnStart => println!("Mismatch between operator stack (Op::FnStart) and group stack (Group::List)!"),
						Op::InitStart => println!("Mismatch between operator stack (Op::InitStart) and group stack (Group::List)!"),
						Op::ArrInitStart => println!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::List)!"),
						_ => {}
					}
				}

				// Lists don't have a starting delimiter, so we consume until we encounter another group-start
				// delimiter (and if there are none, we just end up consuming the rest of the operator stack).
				// Since lists cannnot exist within a `Group::Fn|Init|ArrInit`, we don't check for those start
				// delimiters.
				if *op == Op::BracketStart || *op == Op::IndexStart {
					start_span = span.start;
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					let moved_op = self.operators.pop_back().unwrap();
					self.stack.push_back(Either::Right(moved_op));
				}
			}

			self.stack.push_back(Either::Right((
				Op::List(count),
				Span {
					start: start_span,
					end: span_end,
				},
			)));

			if invalidate {
				self.invalidate_range(group_start, span_end, false);
			}
		} else {
			unreachable!()
		}
	}

	/// Invalidates the stack between the given start and end positions.
	fn invalidate_range(
		&mut self,
		start_pos: usize,
		end_pos: usize,
		invalidating_index: bool,
	) {
		while self.stack.back().is_some() {
			let span = match self.stack.back().unwrap() {
				Either::Left((_, s)) => s,
				Either::Right((_, s)) => s,
			};

			if span.starts_at_or_after(start_pos) {
				self.stack.pop_back();
			} else {
				break;
			}
		}

		self.stack.push_back(Either::Left((
			Expr::Incomplete,
			Span {
				start: start_pos,
				end: end_pos,
			},
		)));

		// Index groups are a bit different than other groups, so we must treat them differently; hence the extra
		// bool parameter in this function.
		//
		// With all other groups, the start span includes all of the relevant expression nodes like so:
		//
		//  func( 1, 2
		// ^     ^
		//
		// However, the index start span only starts at the beginning of the `[` bracket. This is because the
		// expression before the index can be arbitrary like so, (this is because unlike the other groups, the
		// index group is a postfix operator):
		//
		//  obj.fun() [ 0 ]
		//           ^ ^     : current span
		// ^           ^     : ideal span, pretty much impossible to keep track of
		//
		// If we just placed an `Expr::Incomplete` in such a case, we'd get a stack which looks something like:
		//  <SOME_EXPR> <INCOMPLETE>
		// which in turn would not result in a singular `Expr` node once collapsed down.
		//
		// Hence, what we must do is something like this instead:
		//  <SOME_EXPR> <INCOMPLETE> <INDEX>
		// which will collapse into a singular `Expr` node.
		if invalidating_index {
			self.stack.push_back(Either::Right((
				Op::Index(true),
				Span {
					start: start_pos,
					end: end_pos,
				},
			)));
		}
	}

	/// Registers the end of a bracket, function call or array constructor group, popping any operators until the
	/// start of the group is reached.
	fn end_bracket_fn(&mut self, end_span: Span) -> Result<(), ()> {
		let (current_group, _, current_group_inner_start) =
			match self.groups.back() {
				Some(t) => t,
				None => {
					// Since we have no groups, that means we have a lonely `)`. This means we want to stop parsing
					// further tokens.
					println!("Found a `)` delimiter without a starting `(` delimiter!");
					return Err(());
				}
			};

		match current_group {
			Group::Bracket | Group::Fn(_) | Group::ArrInit(_) => {}
			_ => {
				// The current group is not a bracket/function/array constructor group, so we need to check whether
				// there is one at all.
				let mut exists_paren = false;
				for (group, _, _) in self.groups.iter() {
					match group {
						Group::Bracket | Group::Fn(_) | Group::ArrInit(_) => {
							exists_paren = true;
							break;
						}
						_ => {}
					}
				}

				if exists_paren {
					// We have at least one other group to close before we can close the bracket/function/array
					// constructor group.
					'inner: loop {
						let current_group = match self.groups.back() {
							Some((g, _, _)) => g,
							// PERF: Since we've already checked that there is a `Group::Index`, we know this will
							// never return `None` before we break out of the loop.
							None => break 'inner,
						};

						match current_group {
							Group::Init(_) => {
								println!(
									"Unclosed `}}` initializer list found!"
								);
								self.collapse_init(
									end_span.end_at_previous().end,
									true,
								);
							}
							Group::Index(_) => {
								println!("Unclosed `]` index operator found!");
								self.collapse_index(
									end_span.end_at_previous().end,
									true,
								)
							}
							Group::List(_) => self.collapse_list(
								end_span.end_at_previous().end,
								false,
							),
							Group::Bracket
							| Group::Fn(_)
							| Group::ArrInit(_) => break 'inner,
						}
					}
				} else {
					// Since we don't have an bracket/function/array constructor group at all, that means we have a
					// lonely `)`. This makes the entire expression up to the previous group start delimiter
					// incomplete.
					println!(
					"Found a `)` delimiter without a starting `(` delimiter!"
				);

					// We remove operators until we hit a start delimiter.
					'invalidate: while self.operators.back().is_some() {
						let (op, _) = self.operators.back().unwrap();

						if *op == Op::IndexStart || *op == Op::InitStart {
							break 'invalidate;
						} else {
							self.operators.pop_back();
						}
					}

					'invalidate_2: while self.stack.back().is_some() {
						let span = match self.stack.back().unwrap() {
							Either::Left((_, s)) => s,
							Either::Right((_, s)) => s,
						};

						if span.starts_at_or_after(*current_group_inner_start) {
							self.stack.pop_back();
						} else {
							break 'invalidate_2;
						}
					}

					self.stack.push_back(Either::Left((
						Expr::Incomplete,
						Span {
							start: *current_group_inner_start,
							end: end_span.end,
						},
					)));
					return Ok(());
				}
			}
		}

		match self.groups.back().unwrap().0 {
			Group::Bracket => self.collapse_bracket(end_span.end, false),
			Group::Fn(_) => self.collapse_fn(end_span.end, false),
			Group::ArrInit(_) => self.collapse_arr_init(end_span.end, false),
			// Either the inner-most group is already a parenthesis-delimited group, or we've closed all inner
			// groups and are now at a parenthesis-delimited group, hence this branch will never occur.
			_ => unreachable!(),
		}
		Ok(())
	}

	/// Registers the end of an index operator group, popping any operators until the start of the index group is
	/// reached.
	///
	/// `end_span` is a span which ends at the end of this index operator. (The start value is irrelevant).
	fn end_index(&mut self, end_span: Span) -> Result<(), ()> {
		let (current_group, _, current_group_inner_start) =
			match self.groups.back() {
				Some(t) => t,
				None => {
					// Since we have no groups, that means we have a lonely `]`. This means we want to stop parsing
					// further tokens.
					println!("Found a `]` delimiter without a starting `[` delimiter!");
					return Err(());
				}
			};

		if std::mem::discriminant(current_group)
			!= std::mem::discriminant(&Group::Index(false))
		{
			// The current group is not an index group, so we need to check whether there is one at all.
			let mut exists_index = false;
			for (group, _, _) in self.groups.iter() {
				if let Group::Index(_) = group {
					exists_index = true;
					break;
				}
			}

			if exists_index {
				// We have at least one other group to close before we can close the index group.
				'inner: loop {
					let current_group = match self.groups.back() {
						Some((g, _, _)) => g,
						// PERF: Since we've already checked that there is a `Group::Index`, we know this will
						// never return `None` before we break out of the loop.
						None => break 'inner,
					};

					match current_group {
						Group::Bracket => {
							println!("Unclosed `)` parenthesis found!");
							self.collapse_bracket(
								end_span.end_at_previous().end,
								true,
							);
						}
						Group::Fn(_) => {
							println!("Unclosed `)` function call found!");
							self.collapse_fn(
								end_span.end_at_previous().end,
								true,
							);
						}
						Group::Init(_) => {
							println!("Unclosed `}}` initializer list found!");
							self.collapse_init(
								end_span.end_at_previous().end,
								true,
							);
						}
						Group::ArrInit(_) => {
							println!("Unclosed `)` array constructor found!");
							self.collapse_arr_init(
								end_span.end_at_previous().end,
								true,
							);
						}
						Group::List(_) => self.collapse_list(
							end_span.end_at_previous().end,
							false,
						),
						Group::Index(_) => break 'inner,
					}
				}
			} else {
				// Since we don't have an index group at all, that means we have a lonely `]`. This makes the
				// entire expression up to the previous group start delimiter incomplete.
				println!(
					"Found a `]` delimiter without a starting `[` delimiter!"
				);

				// We remove operators until we hit a start delimiter.
				'invalidate: while self.operators.back().is_some() {
					let (op, _) = self.operators.back().unwrap();

					if *op == Op::BracketStart
						|| *op == Op::FnStart || *op == Op::InitStart
						|| *op == Op::ArrInitStart
					{
						break 'invalidate;
					} else {
						self.operators.pop_back();
					}
				}

				'invalidate_2: while self.stack.back().is_some() {
					let span = match self.stack.back().unwrap() {
						Either::Left((_, s)) => s,
						Either::Right((_, s)) => s,
					};

					if span.starts_at_or_after(*current_group_inner_start) {
						self.stack.pop_back();
					} else {
						break 'invalidate_2;
					}
				}

				self.stack.push_back(Either::Left((
					Expr::Incomplete,
					Span {
						start: *current_group_inner_start,
						end: end_span.end,
					},
				)));
				return Ok(());
			}
		}

		self.collapse_index(end_span.end, false);
		Ok(())
	}

	/// Registers the end of an initializer list group, popping any operators until the start of the group is
	/// reached.
	fn end_init(&mut self, end_span: Span) -> Result<(), ()> {
		let (current_group, _, current_group_inner_start) =
			match self.groups.back() {
				Some(t) => t,
				None => {
					// Since we have no groups, that means we have a lonely `}`. This means we want to stop parsing
					// further tokens.
					print!("Found a `}}` delimiter without a starting `{{` delimiter!");
					return Err(());
				}
			};

		if std::mem::discriminant(current_group)
			!= std::mem::discriminant(&Group::Init(0))
		{
			// The current group is not an initializer group, so we need to check whether there is one at all.
			let mut exists_init = false;
			for (group, _, _) in self.groups.iter() {
				if let Group::Init(_) = group {
					exists_init = true;
					break;
				}
			}

			if exists_init {
				// We have at least one other group to close before we can close the initializer group.
				'inner: loop {
					let current_group = match self.groups.back() {
						Some((g, _, _)) => g,
						// PERF: Since we've already checked that there is a `Group::Index`, we know this will
						// never return `None` before we break out of the loop.
						None => break 'inner,
					};

					match current_group {
						Group::Bracket => {
							println!("Unclosed `)` parenthesis found!");
							self.collapse_bracket(
								end_span.end_at_previous().end,
								true,
							);
						}
						Group::Index(_) => {
							println!("Unclosed `]` index operator found!");
							self.collapse_index(
								end_span.end_at_previous().end,
								true,
							);
						}
						Group::Fn(_) => {
							println!("Unclosed `)` function call found!");
							self.collapse_fn(
								end_span.end_at_previous().end,
								true,
							);
						}
						Group::ArrInit(_) => {
							println!("Unclosed `)` array constructor found!");
							self.collapse_arr_init(
								end_span.end_at_previous().end,
								true,
							);
						}
						// See `List` documentation.
						Group::List(_) => unreachable!(),
						Group::Init(_) => break 'inner,
					}
				}
			} else {
				// Since we don't have an initializer group at all, that means we have a lonely `}`. This makes the
				// entire expression up to the previous group start delimiter incomplete.
				println!(
					"Found a `}}` delimiter without a starting `{{` delimiter!"
				);

				// We remove operators until we hit a start delimiter.
				'invalidate: while self.operators.back().is_some() {
					let (op, _) = self.operators.back().unwrap();

					if *op == Op::BracketStart
						|| *op == Op::FnStart || *op == Op::IndexStart
						|| *op == Op::ArrInitStart
					{
						break 'invalidate;
					} else {
						self.operators.pop_back();
					}
				}

				'invalidate_2: while self.stack.back().is_some() {
					let span = match self.stack.back().unwrap() {
						Either::Left((_, s)) => s,
						Either::Right((_, s)) => s,
					};

					if span.starts_at_or_after(*current_group_inner_start) {
						self.stack.pop_back();
					} else {
						break 'invalidate_2;
					}
				}

				self.stack.push_back(Either::Left((
					Expr::Incomplete,
					Span {
						start: *current_group_inner_start,
						end: end_span.end,
					},
				)));
				return Ok(());
			}
		}

		self.collapse_init(end_span.end, false);
		Ok(())
	}

	/// Registers the end of a sub-expression, popping any operators until the start of the group (or expression)
	/// is reached.
	fn end_comma(&mut self) {
		if let Some((current_group, _, current_group_delim_end)) =
			self.groups.back_mut()
		{
			match current_group {
				Group::Fn(_) | Group::Init(_) | Group::ArrInit(_) => {
					// We want to move all existing operators up to the function call, initializer list, or array
					// constructor start delimiter to the stack, to clear it for the next expression.
					while self.operators.back().is_some() {
						let (back, _) = self.operators.back().unwrap();
						if *back == Op::FnStart
							|| *back == Op::InitStart || *back
							== Op::ArrInitStart
						{
							break;
						}

						let moved_op = self.operators.pop_back().unwrap();
						self.stack.push_back(Either::Right(moved_op));
					}
				}
				Group::List(count) => {
					// We want to move all existing operators up to the bracket or index start delimiter, or to the
					// beginning of the expression. We don't push a new list group since we are already within a
					// list group, and it accepts a variable amount of arguments.
					while self.operators.back().is_some() {
						let (back, _) = self.operators.back().unwrap();
						if *back == Op::BracketStart || *back == Op::IndexStart
						{
							break;
						}

						let moved_op = self.operators.pop_back().unwrap();
						self.stack.push_back(Either::Right(moved_op));
					}
				}
				Group::Bracket | Group::Index(_) => {
					// Same as the branch above, but we do push a new list group. Since list groups don't have a
					// start delimiter, we can only do it now that we've encountered a comma within these two
					// groups.
					while self.operators.back().is_some() {
						let (back, _) = self.operators.back().unwrap();
						if *back == Op::BracketStart || *back == Op::IndexStart
						{
							break;
						}

						let moved_op = self.operators.pop_back().unwrap();
						self.stack.push_back(Either::Right(moved_op));
					}
					let start = *current_group_delim_end;
					self.groups.push_back((Group::List(1), start, start));
				}
			}
		} else {
			// Since we are outside of any group, we can just push all the operators to the stack to clear it for
			// the next expression. We also push a new list group. Since list groups don't have a start delimiter,
			// we can only do it now that we've encountered a comma in an otherwise ungrouped expression.
			while self.operators.back().is_some() {
				let moved_op = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved_op));
			}
			self.groups.push_back((
				Group::List(1),
				self.start_position,
				self.start_position,
			));
		}
	}

	/// Increases the arity of the current function.
	fn increase_arity(&mut self) {
		if let Some((current_group, _, _)) = self.groups.back_mut() {
			match current_group {
				Group::Fn(count)
				| Group::Init(count)
				| Group::ArrInit(count)
				| Group::List(count) => {
					*count += 1;
				}
				_ => {}
			}
		}
		// TODO: Should this be unreachable?
		println!("Found an incomplete function call, initializer list, array constructor or general list expression!");
	}

	/// Returns whether we have just started to parse a function, i.e. `..fn(`
	fn just_started_fn(&self) -> bool {
		if let Some((current_group, _, _)) = self.groups.back() {
			match current_group {
				Group::Fn(count) => *count == 0,
				_ => false,
			}
		} else {
			false
		}
	}

	/// Returns whether we have just started to parse an initializer list, i.e. `..{``
	fn just_started_init(&self) -> bool {
		if let Some((current_group, _, _)) = self.groups.back() {
			match current_group {
				Group::Init(count) => *count == 0,
				_ => false,
			}
		} else {
			false
		}
	}

	/// Returns whether we are currently in an initializer list parsing group.
	fn is_in_init(&self) -> bool {
		if let Some((current_group, _, _)) = self.groups.back() {
			match current_group {
				Group::Init(_) => true,
				_ => false,
			}
		} else {
			false
		}
	}

	/// Parses a list of tokens. Populates the internal `stack` with a RPN output.
	fn parse(&mut self, walker: &mut Walker) {
		#[derive(PartialEq)]
		enum State {
			/// We are looking for either a) a prefix operator, b) an atom, c) bracket group start, d) function
			/// call group start, e) initializer list group start.
			Operand,
			/// We are looking for either a) a postfix operator, b) an index operator start or end, c) a binary
			/// operator, d) bracket group end, e) function call group end, f) initializer list group end, g) a
			/// comma, h) end of expression.
			AfterOperand,
		}
		let mut state = State::Operand;

		#[derive(PartialEq)]
		enum Start {
			/// Nothing.
			None,
			/// We have found an `ident`; we can start a function call assuming we find `(` next.
			Fn,
			/// We have found an `Expr::Index`; we can start an array constructor assuming we find `(` next.
			ArrInit,
			/// We have found a `[`. If the next token is a `]` we have an empty index operator.
			EmptyIndex,
		}
		let mut can_start = Start::None;
		// The start position of a potential delimiter, i.e. an `Ident` which may become a function call or an
		// array constructor.
		let mut possible_delim_start = 0;

		// Whether to increase the arity on the next iteration. If set to `true`, on the next iteration, if we have
		// a valid State::Operand, we increase the arity and reset the flag back to `false`.
		let mut increase_arity = false;

		'main: while !walker.is_done() {
			let (token, span) = match walker.peek() {
				Some(t) => t,
				// Return if we reach the end of the token list.
				None => break,
			};

			match token {
				Token::Num { .. } | Token::Bool(_)
					if state == State::Operand =>
				{
					// We switch state since after an atom, we are expecting an operator, i.e.
					// `..10 + 5` instead of `..10 5`.
					self.stack.push_back(match Lit::parse(token) {
						Ok(l) => Either::Left((Expr::Lit(l), *span)),
						Err(_) => Either::Left((Expr::Invalid, *span)),
					});
					state = State::AfterOperand;

					can_start = Start::None;

					if increase_arity {
						self.increase_arity();
						increase_arity = false;
					}
				}
				Token::Ident(s) if state == State::Operand => {
					// We switch state since after an atom, we are expecting an operator, i.e.
					// `..ident + i` instead of `..ident i`.
					self.stack.push_back(match Ident::parse_any(s) {
						Ok(i) => Either::Left((Expr::Ident(i), *span)),
						Err(_) => Either::Left((Expr::Invalid, *span)),
					});
					state = State::AfterOperand;

					// After an identifier, we may start a function call.
					can_start = Start::Fn;
					possible_delim_start = span.start;

					if increase_arity {
						self.increase_arity();
						increase_arity = false;
					}
				}
				Token::Num { .. } | Token::Bool(_) | Token::Ident(_)
					if state == State::AfterOperand =>
				{
					// This is an error, e.g. `..1 1` instead of `..1 + 1`.
					println!("Expected a postfix, index or binary operator, or the end of expression, found an atom instead!");
					return;
				}
				Token::Op(op) if state == State::Operand => {
					match op {
						// If the operator is a valid prefix operator, we can move it to the stack. We don't switch
						// state since after a prefix operator, we are still looking for an operand atom.
						Op::Sub => self.push_operator((Op::Neg, *span)),
						Op::Not => self.push_operator((Op::Not, *span)),
						Op::Flip => self.push_operator((Op::Flip, *span)),
						Op::AddAdd => {
							self.push_operator((Op::AddAddPre, *span))
						}
						Op::SubSub => {
							self.push_operator((Op::SubSubPre, *span))
						}
						_ => {
							// This is an error, e.g. `..*1` instead of `..-1`.
							println!("Expected an atom or a prefix operator, found a non-prefix operator instead!");
							return;
						}
					}

					can_start = Start::None;

					if increase_arity {
						self.increase_arity();
						increase_arity = false;
					}
				}
				Token::Op(op) if state == State::AfterOperand => {
					match op {
						Op::Flip | Op::Not => {
							// These operators cannot be directly after an atom.
							println!("Expected a postfix, index or binary operator, found a prefix operator instead!");
							return;
						}
						// These operators are postfix operators. We don't switch state since after a postfix operator,
						// we are still looking for a binary operator or the end of expression, i.e.
						// `..i++ - i` rather than `..i++ i`.
						Op::AddAdd => {
							self.push_operator((Op::AddAddPost, *span));
						}
						Op::SubSub => {
							self.push_operator((Op::SubSubPost, *span));
						}
						// Any other operators can be part of a binary expression. We switch state since after a binary
						// operator we are expecting an operand.
						_ => {
							self.push_operator((*op, *span));
							state = State::Operand;
						}
					}

					can_start = Start::None;
				}
				Token::LParen if state == State::Operand => {
					// We don't switch state since after a `(`, we are expecting an operand, i.e.
					// `..+ (1 *` rather than `..+ (*`.

					// First increment the arity, since we are creating a new group.
					if increase_arity {
						self.increase_arity();
						increase_arity = false;
					}

					self.operators.push_back((Op::BracketStart, *span));
					self.groups.push_back((
						Group::Bracket,
						span.start,
						span.end,
					));

					can_start = Start::None;
				}
				Token::LParen if state == State::AfterOperand => {
					if can_start == Start::Fn {
						// We have `ident(` which makes this a function call.
						self.operators.push_back((Op::FnStart, *span));
						self.groups.push_back((
							Group::Fn(0),
							possible_delim_start,
							span.end,
						));

						// We switch state since after a `(` we are expecting an operand, i.e.
						// `fn( 1..` rather than`fn( +..`.1
						state = State::Operand;

						// We unset the flag, since this flag is only used to detect the `ident` -> `(` token
						// chain.
						can_start = Start::None;

						increase_arity = true;
					} else if can_start == Start::ArrInit {
						// We have `something[something](` which makes this an array constructor.
						self.operators.push_back((Op::ArrInitStart, *span));
						self.groups.push_back((
							Group::ArrInit(0),
							possible_delim_start,
							span.end,
						));

						// We switch state since after a `(` we are expecting an operand, i.e.
						// `int[]( 1,..` rather than`int[]( +1,..`.
						state = State::Operand;

						// We unset the flag, since this flag is only used to detect the `..]` -> `(` token chain.
						can_start = Start::None;

						increase_arity = true;
					} else {
						// This is an error. e.g. `..1 (` instead of `..1 + (`.
						println!("Expected an operator or the end of expression, found `(` instead!");
						return;
					}
				}
				Token::RParen if state == State::AfterOperand => {
					// We don't switch state since after a `)`, we are expecting an operator, i.e.
					// `..) + 5` rather than `..) 5`.
					match self.end_bracket_fn(*span) {
						Ok(_) => {}
						Err(_) => break 'main,
					}

					can_start = Start::None;
				}
				Token::RParen if state == State::Operand => {
					if self.just_started_fn() {
						// This is valid, i.e. `fn()`.
						match self.end_bracket_fn(*span) {
							Ok(_) => {}
							Err(_) => break 'main,
						}

						// We switch state since after a function call we are expecting an operator, i.e.
						// `..fn() + 5` rather than `..fn() 5`.
						state = State::AfterOperand;

						increase_arity = false;

						can_start = Start::None;
					} else {
						// This is an error, e.g. `..+ )` instead of `..+ 1)`,
						// or `fn(..,)` instead of `fn(.., 1)`.
						println!("Expected an atom or a prefix operator, found `)` instead!");
						return;
					}
				}
				Token::LBracket if state == State::AfterOperand => {
					// We switch state since after a `[`, we are expecting an operand, i.e.
					// `i[5 +..` rather than `i[+..`.
					self.operators.push_back((Op::IndexStart, *span));
					self.groups.push_back((
						Group::Index(true),
						span.start,
						span.end,
					));
					state = State::Operand;

					can_start = Start::EmptyIndex;
				}
				Token::LBracket if state == State::Operand => {
					// This is an error, e.g. `..+ [` instead of `..+ i[`.
					println!("Expected an atom or a prefix operator, found `[` instead!");
					return;
				}
				Token::RBracket if state == State::AfterOperand => {
					// We don't switch state since after a `]`, we are expecting an operator, i.e.
					// `..] + 5` instead of `..] 5`.
					match self.end_index(*span) {
						Ok(_) => {}
						Err(_) => break 'main,
					}

					// After an index `]` we may have an array constructor.
					can_start = Start::ArrInit;
				}
				Token::RBracket if state == State::Operand => {
					if can_start == Start::EmptyIndex {
						// We switch state since after a `]`, we are expecting an operator, i.e.
						// `..[] + 5` rather than `..[] 5`.

						match self.groups.back_mut() {
							Some((g, _, _)) => match g {
								Group::Index(contains_i) => *contains_i = false,
								_ => unreachable!(),
							},
							None => unreachable!(),
						}

						match self.end_index(*span) {
							Ok(_) => {}
							Err(_) => break 'main,
						}
						state = State::AfterOperand;

						// After an index `]` we may have an array constructor.
						can_start = Start::ArrInit;
					} else {
						// This is an error, e.g. `..+ ]` instead of `..+ 1]`.
						println!("Expected an atom or a prefix operator, found `]` instead!");
						return;
					}
				}
				Token::LBrace if state == State::Operand => {
					// We don't switch state since after a `{`, we are expecting an operand, i.e.
					// `..+ {1,` rather than `..+ {,`.

					// First increase the arity, since we are creating a new group with its own arity.
					if increase_arity {
						self.increase_arity();
						increase_arity = false;
					}

					self.operators.push_back((Op::InitStart, *span));
					self.groups.push_back((
						Group::Init(0),
						span.start,
						span.end,
					));

					increase_arity = true;

					can_start = Start::None;
				}
				Token::LBrace if state == State::AfterOperand => {
					// This is an error, e.g. `.. {` instead of `.. + {`.
					println!("Expected an operator or the end of expression, found `{{` instead!");
					return;
				}
				Token::RBrace if state == State::AfterOperand => {
					// We don't switch state since after a `}}`, we are expecting an operator, i.e.
					// `..}, {..` rather than `..} {..`.
					match self.end_init(*span) {
						Ok(_) => {}
						Err(_) => break 'main,
					}

					can_start = Start::None;
				}
				Token::RBrace if state == State::Operand => {
					if self.just_started_init() || self.is_in_init() {
						// This is valid, i.e. `{}`, or `{1, }`.
						match self.end_init(*span) {
							Ok(_) => {}
							Err(_) => break 'main,
						}

						// We switch state since after an init list we are expecting an operator, i.e.
						// `..}, {..` rather than `..} {..`.
						state = State::AfterOperand;

						increase_arity = false;

						can_start = Start::None;
					} else {
						// This is an error, e.g. `..+ }` instead of `..+ 1}`.
						println!("Expected an atom or a prefix operator, found `}}` instead!");
						return;
					}
				}
				Token::Comma if state == State::AfterOperand => {
					// We switch state since after a comma (which delineates an expression), we're effectively
					// starting a new expression which must start with an operand, i.e.
					// `.., 5 + 6` instead of `.., + 6`.
					self.end_comma();
					state = State::Operand;

					can_start = Start::None;

					increase_arity = true;
				}
				Token::Comma if state == State::Operand => {
					// This is an error, e.g. `..+ ,` instead of `..+ 1,`.
					println!("Expected an atom or a prefix operator, found `,` instead!");
					return;
				}
				Token::Dot if state == State::AfterOperand => {
					// We switch state since after an object access we are execting an operand, i.e.
					// `ident.something` rather than `ident. +`.
					self.push_operator((Op::ObjAccess, *span));
					state = State::Operand;

					can_start = Start::None;
				}
				Token::Dot if state == State::Operand => {
					// This is an error, e.g. `ident.+` instead of `ident.something`.
					println!("Expected an atom or a prefix operator, found `.` instead!");
					return;
				}
				_ => {
					// We have a token that's not allowed to be part of an expression.
					println!("Unexpected token found: {token:?}");
					break 'main;
				}
			}

			walker.advance();
		}

		// FIXME: This should be -1 I think?
		let end_position = walker.cursor;

		// Close any open groups.
		while self.groups.back().is_some() {
			let (group, _, _) = self.groups.back().unwrap();
			println!("Found an unclosed: {group:?}");

			// Reasoning about what gets invalidated and what doesn't: will it potentially produce semantic errors
			//
			// Brackets - no matter where the closing parenthesis is located, it won't change whether the
			// 	 expression type checks or not.
			// Index - depending on where the closing bracket is placed, it can change whether the expression
			// 	 type checks or not.
			// Fn - depending on where the closing parenthesis is, it can change the number of arguments.
			// Init - same as above.
			// ArrInit - same as above.
			// List - a perfectly valid top-level grouping structure.
			match group {
				Group::Bracket => self.collapse_bracket(end_position, false),
				Group::Index(_) => self.collapse_index(end_position, true),
				Group::Fn(_) => self.collapse_fn(end_position, true),
				Group::Init(_) => self.collapse_init(end_position, true),
				Group::ArrInit(_) => self.collapse_arr_init(end_position, true),
				Group::List(_) => self.collapse_list(end_position, false),
				_ => {}
			}
		}

		// If there is an open group, then all of the operators will have been already moved as part of the
		// collapsing functions. However, if we didn't need to close any groups, we may have leftover operators
		// which still need moving.
		while let Some(op) = self.operators.pop_back() {
			self.stack.push_back(Either::Right(op));
		}
	}

	/// Converts the internal RPN stack into a singular `Expr` node, which contains the entire expression.
	fn create_ast(&mut self) -> Option<Expr> {
		let mut stack = VecDeque::new();

		// We have "parsed" the token stream and we immediately hit a token which cannot be part of an expression.
		// Hence, there is no expression to return at all.
		if self.stack.len() == 0 {
			return None;
		}

		// Consume the stack from the front. If we have an expression, we move it to the back of a temporary stack.
		// If we have an operator, we take the x-most expressions from the back of the temporary stack, process
		// them in accordance to the operator type, and then push the result onto the back of the temporary stack.
		while let Some(e) = self.stack.pop_front() {
			match e {
				Either::Left(e) => stack.push_back(e),
				Either::Right((op, _)) => match op {
					Op::AddAddPre => {
						let (expr, _) = stack.pop_back().unwrap();
						stack.push_back((
							Expr::Prefix(Box::from(expr), Op::Add),
							Span::empty(),
						));
					}
					Op::SubSubPre => {
						let (expr, _) = stack.pop_back().unwrap();
						stack.push_back((
							Expr::Prefix(Box::from(expr), Op::Sub),
							Span::empty(),
						));
					}
					Op::AddAddPost => {
						let (expr, _) = stack.pop_back().unwrap();
						stack.push_back((
							Expr::Postfix(Box::from(expr), Op::Add),
							Span::empty(),
						));
					}
					Op::SubSubPost => {
						let (expr, _) = stack.pop_back().unwrap();
						stack.push_back((
							Expr::Postfix(Box::from(expr), Op::Sub),
							Span::empty(),
						));
					}
					Op::Neg => {
						let (expr, _) = stack.pop_back().unwrap();
						stack.push_back((
							Expr::Neg(Box::from(expr)),
							Span::empty(),
						));
					}
					Op::Flip => {
						let (expr, _) = stack.pop_back().unwrap();
						stack.push_back((
							Expr::Flip(Box::from(expr)),
							Span::empty(),
						));
					}
					Op::Not => {
						let (expr, _) = stack.pop_back().unwrap();
						stack.push_back((
							Expr::Not(Box::from(expr)),
							Span::empty(),
						));
					}
					Op::Index(contains_i) => {
						let i = if contains_i {
							Some(Box::from(stack.pop_back().unwrap().0))
						} else {
							None
						};
						let (expr, _) = stack.pop_back().unwrap();
						stack.push_back((
							Expr::Index {
								item: Box::from(expr),
								i,
							},
							Span::empty(),
						));
					}
					Op::ObjAccess => {
						let (access, _) = stack.pop_back().unwrap();
						let (obj, _) = stack.pop_back().unwrap();
						stack.push_back((
							Expr::ObjAccess {
								obj: Box::from(obj),
								access: Box::from(access),
							},
							Span::empty(),
						));
					}
					Op::Paren => {
						let (expr, _) = stack.pop_back().unwrap();
						stack.push_back((
							Expr::Paren(Box::from(expr)),
							Span::empty(),
						));
					}
					Op::FnCall(count) => {
						let mut args = VecDeque::new();
						for _ in 0..count {
							args.push_front(stack.pop_back().unwrap().0);
						}

						// Get the identifier (which is the first expression).
						let ident = if let Expr::Ident(i) =
							args.pop_front().unwrap()
						{
							i
						} else {
							panic!("The first expression of a function call operator is not an identifier!");
						};

						stack.push_back((
							Expr::Fn {
								ident,
								args: args.into(),
							},
							Span::empty(),
						));
					}
					Op::ArrInit(count, _) => {
						let mut args = VecDeque::new();
						for _ in 0..count {
							args.push_front(stack.pop_back().unwrap().0);
						}

						// Get the index operator (which is the first expression).
						let arr = args.pop_front().unwrap();
						match arr {
							Expr::Index { .. } => {}
							_ => {
								panic!("The first expression of an array constructor operator is not an `Expr::Index`!");
							}
						}

						stack.push_back((
							Expr::ArrInit {
								arr: Box::from(arr),
								args: args.into(),
							},
							Span::empty(),
						));
					}
					Op::Init(count) => {
						let mut args = Vec::new();
						for _ in 0..count {
							args.push(stack.pop_back().unwrap().0);
						}
						args.reverse();

						stack.push_back((Expr::InitList(args), Span::empty()));
					}
					Op::List(count) => {
						let mut args = Vec::new();
						for _ in 0..count {
							args.push(stack.pop_back().unwrap().0);
						}
						args.reverse();

						stack.push_back((Expr::List(args), Span::empty()));
					}
					Op::Add
					| Op::Sub
					| Op::Mul
					| Op::Div
					| Op::Rem
					| Op::And
					| Op::Or
					| Op::Xor
					| Op::LShift
					| Op::RShift
					| Op::EqEq
					| Op::NotEq
					| Op::Gt
					| Op::Lt
					| Op::Ge
					| Op::Le
					| Op::AndAnd
					| Op::OrOr
					| Op::XorXor
					| Op::AddEq
					| Op::SubEq
					| Op::MulEq
					| Op::DivEq
					| Op::RemEq
					| Op::AndEq
					| Op::OrEq
					| Op::XorEq
					| Op::LShiftEq
					| Op::RShiftEq => {
						let (right, _) = stack.pop_back().unwrap();
						let (left, _) = stack.pop_back().unwrap();
						stack.push_back((
							Expr::Binary {
								left: Box::from(left),
								op,
								right: Box::from(right),
							},
							Span::empty(),
						));
					}
					_ => {
						panic!("Invalid operator {op} in shunting yard stack. This operator should never be present in the final RPN output stack.");
					}
				},
			}
		}

		#[cfg(debug_assertions)]
		if stack.len() != 1 {
			panic!("After processing the shunting yard output stack, we are left with more than one expression. This should not happen.");
		}

		// Return the one root expression.
		Some(stack.pop_back().unwrap().0)
	}
}

#[rustfmt::skip]
impl Op {
	/// Returns the precedence of the operator.
	fn precedence(&self) -> u8 {
		match self {
			Self::ObjAccess => 33,
			Self::AddAddPost | Self::SubSubPost => 31,
			Self::AddAddPre
			| Self::SubSubPre
			| Self::Neg
			| Self::Flip
			| Self::Not => 29,
			Self::Mul | Self::Div | Self::Rem => 27,
			Self::Add | Self::Sub => 25,
			Self::LShift | Self::RShift => 23,
			Self::Lt | Self::Gt | Self::Le | Self::Ge => 21,
			Self::EqEq | Self::NotEq => 19,
			Self::And => 17,
			Self::Xor => 15,
			Self::Or => 13,
			Self::AndAnd => 11,
			Self::XorXor => 9,
			Self::OrOr => 7,
			// TODO: Ternary
			Self::AddEq
			| Self::SubEq
			| Self::MulEq
			| Self::DivEq
			| Self::RemEq
			| Self::AndEq
			| Self::XorEq
			| Self::OrEq
			| Self::LShiftEq
			| Self::RShiftEq => 3,
			// These two should always be converted to the *Pre or *Post versions in the shunting yard.
			Self::AddAdd | Self::SubSub => panic!("OpType::AddAdd | OpType::SubSub do not have precedence values because they should never be passed into this function. Something has gone wrong!"),
			// These are never directly checked for precedence, but rather have special branches.
			Self::BracketStart
			| Self::Paren 
			| Self::FnStart 
			| Self::FnCall(_) 
			| Self::IndexStart 
			| Self::Index(_) 
			| Self::InitStart 
			| Self::Init(_) 
			| Self::ArrInitStart 
			| Self::ArrInit(_,_)
			| Self::List(_) => {
				panic!("The operator {self:?} does not have a precedence value because it should never be passed into this function. Something has gone wrong!")
			},
		}
	}
}

// Purely used for debugging the parsed expressions.
impl std::fmt::Display for ShuntingYard {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for node in self.stack.iter() {
			match node {
				Either::Left((e, _)) => write!(f, "{e} ")?,
				Either::Right((op, _)) => write!(f, "{op} ")?,
			}
		}
		Ok(())
	}
}

impl std::fmt::Display for Op {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			// Maths
			Self::Add => write!(f, "+"),
			Self::Sub => write!(f, "-"),
			Self::Mul => write!(f, "*"),
			Self::Div => write!(f, "/"),
			Self::Rem => write!(f, "%"),
			Self::And => write!(f, "&"),
			Self::Or => write!(f, "|"),
			Self::Xor => write!(f, "^"),
			Self::LShift => write!(f, "<<"),
			Self::RShift => write!(f, ">>"),
			Self::AddEq => write!(f, "+="),
			Self::SubEq => write!(f, "-="),
			Self::MulEq => write!(f, "*="),
			Self::DivEq => write!(f, "/="),
			Self::RemEq => write!(f, "%="),
			Self::AndEq => write!(f, "&="),
			Self::OrEq => write!(f, "|="),
			Self::XorEq => write!(f, "^="),
			Self::LShiftEq => write!(f, "<<="),
			Self::RShiftEq => write!(f, ">>="),
			Self::Flip => write!(f, "~"),
			Self::AddAdd => write!(f, "NOP"),
			Self::SubSub => write!(f, "NOP"),
			//
			// Comparison
			Self::EqEq => write!(f, "=="),
			Self::NotEq => write!(f, "!="),
			Self::Gt => write!(f, ">"),
			Self::Lt => write!(f, "<"),
			Self::Ge => write!(f, ">="),
			Self::Le => write!(f, "<="),
			Self::AndAnd => write!(f, "&&"),
			Self::OrOr => write!(f, "||"),
			Self::XorXor => write!(f, "^^"),
			Self::Not => write!(f, "!"),
			//
			// Shunting Yard
			Self::Neg => write!(f, "neg"),
			Self::AddAddPre => write!(f, "++pre"),
			Self::AddAddPost => write!(f, "++post"),
			Self::SubSubPre => write!(f, "--pre"),
			Self::SubSubPost => write!(f, "--post"),
			Self::BracketStart
			| Self::FnStart
			| Self::IndexStart
			| Self::InitStart
			| Self::ArrInitStart => {
				write!(f, "")
			}
			Self::Paren => write!(f, ""),
			Self::Index(true) => write!(f, "index"),
			Self::Index(false) => write!(f, "empty_index"),
			Self::ObjAccess => write!(f, "access"),
			Self::FnCall(count) => write!(f, "FN:{count}"),
			Self::Init(count) => write!(f, "INIT:{count}"),
			Self::ArrInit(count, bool) => write!(f, "ARR_INIT:{count}:{bool}"),
			Self::List(count) => write!(f, "LIST:{count}"),
		}
	}
}

/// Asserts the expression output of the `expr_parser()` matches the right hand side.
macro_rules! assert_expr {
	($source:expr, $rest: expr) => {
		let mut walker = Walker {
			cst: lexer($source),
			cursor: 0,
		};
		assert_eq!(expr_parser(&mut walker).unwrap(), $rest);
	};
}

#[test]
#[rustfmt::skip]
fn binaries() {
	// Single operator
	assert_expr!("5 + 1",
		Expr::Binary {
			left: Box::from(Expr::Lit(Lit::Int(5))),
			op: Op::Add,
			right: Box::from(Expr::Lit(Lit::Int(1)))
		}
	);
	assert_expr!("ident * 100.4",
		Expr::Binary {
			left: Box::from(Expr::Ident(Ident("ident".into()))),
			op: Op::Mul,
			right: Box::from(Expr::Lit(Lit::Float(100.4)))
		}
	);
	assert_expr!("30 << 8u",
		Expr::Binary {
			left: Box::from(Expr::Lit(Lit::Int(30))),
			op: Op::LShift,
			right: Box::from(Expr::Lit(Lit::UInt(8)))
		}
	);

	// Multiple operators
	assert_expr!("5 + 1 / 3",
		Expr::Binary {
			left: Box::from(Expr::Lit(Lit::Int(5))),
			op: Op::Add,
			right: Box::from(Expr::Binary {
				left: Box::from(Expr::Lit(Lit::Int(1))),
				op: Op::Div,
				right: Box::from(Expr::Lit(Lit::Int(3)))
			})
		}
	);
	assert_expr!("5 * 4 * 3", Expr::Binary {
		left: Box::from(Expr::Lit(Lit::Int(5))),
		op: Op::Mul,
		right: Box::from(Expr::Binary {
			left: Box::from(Expr::Lit(Lit::Int(4))),
			op:Op::Mul,
			right: Box::from(Expr::Lit(Lit::Int(3)))
		})
	});
	assert_expr!("5 + 1 / 3 * i",
		Expr::Binary {
			left: Box::from(Expr::Lit(Lit::Int(5))),
			op: Op::Add,
			right: Box::from(Expr::Binary {
				left: Box::from(Expr::Lit(Lit::Int(1))),
				op: Op::Div,
				right: Box::from(Expr::Binary {
					left: Box::from(Expr::Lit(Lit::Int(3))),
					op: Op::Mul,
					right: Box::from(Expr::Ident(Ident("i".into())))
				})
			})
		}
	);
	assert_expr!("5 + 1 == true * i",
		Expr::Binary {
			left: Box::from(Expr::Binary {
				left: Box::from(Expr::Lit(Lit::Int(5))),
				op: Op::Add,
				right: Box::from(Expr::Lit(Lit::Int(1)))
			}),
			op: Op::EqEq,
			right: Box::from(Expr::Binary {
				left: Box::from(Expr::Lit(Lit::Bool(true))),
				op: Op::Mul,
				right: Box::from(Expr::Ident(Ident("i".into())))
			})
		}
	);
}

#[test]
#[rustfmt::skip]
fn brackets() {
	assert_expr!("(5 + 1) * 8",
		Expr::Binary {
			left: Box::from(Expr::Paren(Box::from(Expr::Binary {
				left: Box::from(Expr::Lit(Lit::Int(5))),
				op: Op::Add,
				right: Box::from(Expr::Lit(Lit::Int(1))),
			}))),
			op: Op::Mul,
			right: Box::from(Expr::Lit(Lit::Int(8)))
		}
	);
	assert_expr!("((5 + 1) < 100) * 8",
		Expr::Binary {
			left: Box::from(Expr::Paren(Box::from(Expr::Binary {
				left: Box::from(Expr::Paren(Box::from(Expr::Binary {
					left: Box::from(Expr::Lit(Lit::Int(5))),
					op: Op::Add,
					right: Box::from(Expr::Lit(Lit::Int(1))),
				}))),
				op: Op::Lt,
				right: Box::from(Expr::Lit(Lit::Int(100))),
			}))),
			op: Op::Mul,
			right: Box::from(Expr::Lit(Lit::Int(8)))
		}
	);
}

#[test]
#[rustfmt::skip]
fn unaries() {
	// Single operator
	assert_expr!("-5", Expr::Neg(Box::from(Expr::Lit(Lit::Int(5)))));
	assert_expr!("~5", Expr::Flip(Box::from(Expr::Lit(Lit::Int(5)))));
	assert_expr!("!5", Expr::Not(Box::from(Expr::Lit(Lit::Int(5)))));
	assert_expr!("++5", Expr::Prefix(Box::from(Expr::Lit(Lit::Int(5))), Op::Add));
	assert_expr!("--5", Expr::Prefix(Box::from(Expr::Lit(Lit::Int(5))), Op::Sub));
	assert_expr!("5++", Expr::Postfix(Box::from(Expr::Lit(Lit::Int(5))), Op::Add));
	assert_expr!("5--", Expr::Postfix(Box::from(Expr::Lit(Lit::Int(5))), Op::Sub));
	
	// Multiple operators
	assert_expr!("- -5",
		Expr::Neg(Box::from(
			Expr::Neg(Box::from(Expr::Lit(Lit::Int(5))))
		))
	);
	assert_expr!("- - -5",
		Expr::Neg(Box::from(
			Expr::Neg(Box::from(
				Expr::Neg(Box::from(Expr::Lit(Lit::Int(5))))
			))
		))
	);
	assert_expr!("!!5",
		Expr::Not(Box::from(
			Expr::Not(Box::from(Expr::Lit(Lit::Int(5))))
		))
	);
	assert_expr!("++++5",
		Expr::Prefix(
			Box::from(
				Expr::Prefix(
					Box::from(Expr::Lit(Lit::Int(5))),
					Op::Add
				)
			),
			Op::Add
		)
	);
	assert_expr!("--5++",
		Expr::Prefix(
			Box::from(Expr::Postfix(
				Box::from(Expr::Lit(Lit::Int(5))),
				Op::Add
			)),
			Op::Sub
		)
	);
}

#[test]
#[rustfmt::skip]
fn fn_calls() {
	assert_expr!("fn()",
		Expr::Fn { ident: Ident("fn".into()), args: vec![] }
	);
	assert_expr!("fu_nc(1)",
		Expr::Fn { ident: Ident("fu_nc".into()), args: vec![Expr::Lit(Lit::Int(1))] }
	);
	assert_expr!("fn(5 + 1, i << 6)",
		Expr::Fn { ident: Ident("fn".into()), args: vec![
			Expr::Binary {
				left: Box::from(Expr::Lit(Lit::Int(5))),
				op: Op::Add,
				right: Box::from(Expr::Lit(Lit::Int(1))),
			},
			Expr::Binary {
				left: Box::from(Expr::Ident(Ident("i".into()))),
				op: Op::LShift,
				right: Box::from(Expr::Lit(Lit::Int(6))),
			},
		]}
	);
	assert_expr!("fn(fn())",
		Expr::Fn { ident: Ident("fn".into()), args: vec![
			Expr::Fn { ident: Ident("fn".into()), args: vec![] }
		]}
	);
	assert_expr!("fn1(5, fn2(0))", Expr::Fn {
		ident: Ident("fn1".into()),
		args: vec![
			Expr::Lit(Lit::Int(5)),
			Expr::Fn {
				ident: Ident("fn2".into()),
				args: vec![Expr::Lit(Lit::Int(0))]
			}
		]
	});
	assert_expr!("fn1(5, fn2(fn3()))", Expr::Fn {
		ident: Ident("fn1".into()),
		args: vec![
			Expr::Lit(Lit::Int(5)),
			Expr::Fn {
				ident: Ident("fn2".into()),
				args: vec![Expr::Fn {
					ident: Ident("fn3".into()),
					args: vec![]
				}]
			}
		]
	});
}

#[test]
#[rustfmt::skip]
fn obj_access() {
	assert_expr!("ident.something", Expr::ObjAccess {
		obj: Box::from(Expr::Ident(Ident("ident".into()))),
		access: Box::from(Expr::Ident(Ident("something".into())))
	});
	/* assert_expr!("a.b.c", Expr::ObjAccess {
		obj: Box::from(Expr::Ident(Ident("a".into()))),
		access: Box::from(Expr::ObjAccess {
			obj: Box::from(Expr::Ident(Ident("b".into()))),
			access: Box::from(Expr::Ident(Ident("c".into())))
		})
	}); */
	assert_expr!("a.b.c", Expr::ObjAccess {
		obj: Box::from(Expr::ObjAccess {
			obj: Box::from(Expr::Ident(Ident("a".into()))),
			access: Box::from(Expr::Ident(Ident("b".into())))
		}),
		access: Box::from(Expr::Ident(Ident("c".into())))
	});
	assert_expr!("fn().x", Expr::ObjAccess {
		obj: Box::from(Expr::Fn {
			ident: Ident("fn".into()),
			args: vec![]
		}),
		access: Box::from(Expr::Ident(Ident("x".into())))
	});
}

#[test]
#[rustfmt::skip]
fn indexes() {
	// Single-dimensional indexes
	assert_expr!("i[0]", Expr::Index {
		item: Box::from(Expr::Ident(Ident("i".into()))),
		i: Some(Box::from(Expr::Lit(Lit::Int(0))))
	});
	assert_expr!("s[z+1]", Expr::Index {
		item: Box::from(Expr::Ident(Ident("s".into()))),
		i: Some(Box::from(Expr::Binary {
			left: Box::from(Expr::Ident(Ident("z".into()))),
			op: Op::Add,
			right: Box::from(Expr::Lit(Lit::Int(1)))
		}))
	});
	assert_expr!("i[y[5]]", Expr::Index {
		item: Box::from(Expr::Ident(Ident("i".into()))),
		i: Some(Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("y".into()))),
			i: Some(Box::from(Expr::Lit(Lit::Int(5))))
		}))
	});
	assert_expr!("i[y[z[1+2]]]", Expr::Index {
		item: Box::from(Expr::Ident(Ident("i".into()))),
		i: Some(Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("y".into()))),
			i: Some(Box::from(Expr::Index {
				item: Box::from(Expr::Ident(Ident("z".into()))),
				i: Some(Box::from(Expr::Binary {
					left: Box::from(Expr::Lit(Lit::Int(1))),
					op: Op::Add,
					right: Box::from(Expr::Lit(Lit::Int(2))),
				}))
			}))
		}))
	});

	// Multi-dimensional indexes
	assert_expr!("i[5][2]", Expr::Index {
		item: Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("i".into()))),
			i: Some(Box::from(Expr::Lit(Lit::Int(5))))
		}),
		i: Some(Box::from(Expr::Lit(Lit::Int(2))))
	});
	assert_expr!("i[5][2][size]", Expr::Index {
		item: Box::from(Expr::Index {
			item: Box::from(Expr::Index {
				item: Box::from(Expr::Ident(Ident("i".into()))),
				i: Some(Box::from(Expr::Lit(Lit::Int(5))))
			}),
			i: Some(Box::from(Expr::Lit(Lit::Int(2))))
		}),
		i: Some(Box::from(Expr::Ident(Ident("size".into()))))
	});

	// Empty indexes
	assert_expr!("int[]", Expr::Index {
		item: Box::from(Expr::Ident(Ident("int".into()))),
		i: None
	});
	assert_expr!("int[i[]]", Expr::Index {
		item: Box::from(Expr::Ident(Ident("int".into()))),
		i: Some(Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("i".into()))),
			i: None
		}))
	});
	assert_expr!("i[][]", Expr::Index {
		item: Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("i".into()))),
			i: None
		}),
		i: None
	});
	assert_expr!("i[5][2][]", Expr::Index {
		item: Box::from(Expr::Index {
			item: Box::from(Expr::Index {
				item: Box::from(Expr::Ident(Ident("i".into()))),
				i: Some(Box::from(Expr::Lit(Lit::Int(5))))
			}),
			i: Some(Box::from(Expr::Lit(Lit::Int(2))))
		}),
		i: None
	});
}

#[test]
#[rustfmt::skip]
fn arr_constructors() {
	assert_expr!("int[1](2)", Expr::ArrInit {
		arr: Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("int".into()))),
			i: Some(Box::from(Expr::Lit(Lit::Int(1))))
		}),
		args: vec![
			Expr::Lit(Lit::Int(2))
		]
	});
	assert_expr!("int[size](2, false, 5.0)", Expr::ArrInit {
		arr: Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("int".into()))),
			i: Some(Box::from(Expr::Ident(Ident("size".into()))))
		}),
		args: vec![
			Expr::Lit(Lit::Int(2)),
			Expr::Lit(Lit::Bool(false)),
			Expr::Lit(Lit::Float(5.0)),
		]
	});
	assert_expr!("int[1+5](2)", Expr::ArrInit {
		arr: Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("int".into()))),
			i: Some(Box::from(Expr::Binary {
				left: Box::from(Expr::Lit(Lit::Int(1))),
				op: Op::Add,
				right: Box::from(Expr::Lit(Lit::Int(5)))
			}))
		}),
		args: vec![
			Expr::Lit(Lit::Int(2))
		]
	});

	assert_expr!("vec3[](2)", Expr::ArrInit {
		arr: Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("vec3".into()))),
			i: None
		}),
		args: vec![
			Expr::Lit(Lit::Int(2))
		]
	});
}

#[test]
#[rustfmt::skip]
fn initializers() {
	assert_expr!("{1}", Expr::InitList(vec![Expr::Lit(Lit::Int(1))]));
	assert_expr!("{1,}", Expr::InitList(vec![Expr::Lit(Lit::Int(1))]));
	assert_expr!("{1, true, i}", Expr::InitList(vec![
		Expr::Lit(Lit::Int(1)),
		Expr::Lit(Lit::Bool(true)),
		Expr::Ident(Ident("i".into()))
	]));
	assert_expr!("{2.0, {1, s}}", Expr::InitList(vec![
		Expr::Lit(Lit::Float(2.0)),
		Expr::InitList(vec![
			Expr::Lit(Lit::Int(1)),
			Expr::Ident(Ident("s".into()))
		])
	]));
}

#[test]
#[rustfmt::skip]
fn lists() {
	// Note: Lists cannot exist within function calls, array constructors or initializer lists. Hence the absence
	// of those from this test.
	assert_expr!("a, b", Expr::List(vec![
		Expr::Ident(Ident("a".into())),
		Expr::Ident(Ident("b".into()))
	]));
	assert_expr!("a, b, c", Expr::List(vec![
		Expr::Ident(Ident("a".into())),
		Expr::Ident(Ident("b".into())),
		Expr::Ident(Ident("c".into()))
	]));
	assert_expr!("i[a, b]", Expr::Index {
		item: Box::from(Expr::Ident(Ident("i".into()))),
		i: Some(Box::from(Expr::List(vec![
			Expr::Ident(Ident("a".into())),
			Expr::Ident(Ident("b".into()))
		])))
	});
	assert_expr!("(a, b)", Expr::Paren(Box::from(Expr::List(vec![
		Expr::Ident(Ident("a".into())),
		Expr::Ident(Ident("b".into()))
	]))));	
}

#[test]
#[rustfmt::skip]
fn complex() {
	assert_expr!("func(i[9], foo-- -6)", Expr::Fn {
		ident: Ident("func".into()),
		args: vec![
			Expr::Index {
				item: Box::from(Expr::Ident(Ident("i".into()))),
				i: Some(Box::from(Expr::Lit(Lit::Int(9)))),
			},
			Expr::Binary {
				left: Box::from(
					Expr::Postfix(Box::from(Expr::Ident(Ident("foo".into()))), Op::Sub)
				),
				op: Op::Sub,
				right: Box::from(Expr::Lit(Lit::Int(6)))
			}
		]
	});
	assert_expr!("true << i[func((1 + 1) * 5.0)]", Expr::Binary {
		left: Box::from(Expr::Lit(Lit::Bool(true))),
		op: Op::LShift,
		right: Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("i".into()))),
			i: Some(Box::from(Expr::Fn {
				ident: Ident("func".into()),
				args: vec![
					Expr::Binary {
						left: Box::from(Expr::Paren(Box::from(Expr::Binary {
							left: Box::from(Expr::Lit(Lit::Int(1))),
							op: Op::Add,
							right: Box::from(Expr::Lit(Lit::Int(1))),
						}))),
						op: Op::Mul,
						right: Box::from(Expr::Lit(Lit::Float(5.0)))
					}
				]
			}))
		})
	});
	assert_expr!("{1.0, true, func(i[0], 100u)}", Expr::InitList(vec![
		Expr::Lit(Lit::Float(1.0)),
		Expr::Lit(Lit::Bool(true)),
		Expr::Fn {
			ident: Ident("func".into()),
			args: vec![
				Expr::Index {
					item: Box::from(Expr::Ident(Ident("i".into()))),
					i: Some(Box::from(Expr::Lit(Lit::Int(0))))
				},
				Expr::Lit(Lit::UInt(100))
			]
		}
	]));
	assert_expr!("mat2[]({vec2(1, 2), vec2(3, 4)})", Expr::ArrInit {
		arr: Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("mat2".into()))),
			i: None
		}),
		args: vec![Expr::InitList(vec![
			Expr::Fn {
				ident: Ident("vec2".into()),
				args: vec![
					Expr::Lit(Lit::Int(1)),
					Expr::Lit(Lit::Int(2)),
				]
			},
			Expr::Fn {
				ident: Ident("vec2".into()),
				args: vec![
					Expr::Lit((Lit::Int(3))),
					Expr::Lit((Lit::Int(4))),
				]
			}
		])]
	});
}

#[test]
#[rustfmt::skip]
fn incomplete() {
	/* assert_expr!("i+5]", Expr::Binary {
		left: Box::from(Expr::Ident(Ident("i".into()))),
		op: Op::Add,
		right: Box::from(Expr::Lit(Lit::Int(5)))
	}); */
	assert_expr!("i[(5+1]", Expr::Index {
		item: Box::from(Expr::Ident(Ident("i".into()))),
		i: Some(Box::from(Expr::Incomplete))
	});
	assert_expr!("i[fn((5+1]", Expr::Index {
		item: Box::from(Expr::Ident(Ident("i".into()))),
		i: Some(Box::from(Expr::Incomplete))
	});
	assert_expr!("(i+5])", Expr::Paren(Box::from(Expr::Incomplete)));
	assert_expr!("fn(1])", Expr::Fn {
		ident: Ident("fn".into()),
		args: vec![Expr::Incomplete]
	});
	assert_expr!("int[3](i])", Expr::ArrInit {
		arr: Box::from(Expr::Index {
			item: Box::from(Expr::Ident(Ident("int".into()))),
			i: Some(Box::from(Expr::Lit(Lit::Int(3))))
		}),
		args: vec![Expr::Incomplete]
	});
	
	// Outer unclosed delimiters.
	assert_expr!("(i+x", Expr::Paren(Box::from(Expr::Binary {
		left: Box::from(Expr::Ident(Ident("i".into()))),
		op: Op::Add,
		right: Box::from(Expr::Ident(Ident("x".into())))
	})));
	assert_expr!("i[5+1", Expr::Index {
		item: Box::from(Expr::Ident(Ident("i".into()))),
		i: Some(Box::from(Expr::Incomplete))
	});
	assert_expr!("fn(5+1", Expr::Incomplete);
	assert_expr!("{5, 1", Expr::Incomplete);
	assert_expr!("int[5](1, 2", Expr::Incomplete);
	assert_expr!("a, b, c", Expr::List(vec![
		Expr::Ident(Ident("a".into())),
		Expr::Ident(Ident("b".into())),
		Expr::Ident(Ident("c".into()))
	]));
}
