use crate::{
	ast::{Expr, ExprTy, Ident, Lit, Op},
	lexer::{OpTy, Token},
	parser::Walker,
	span::{span, Span},
	Either,
};
use std::collections::VecDeque;

#[derive(Debug, PartialEq, Eq)]
pub enum Mode {
	Default,
	DisallowTopLevelList,
	BreakAtEq,
}

/// Tries to parse an expression beginning at the current position.
pub fn expr_parser(walker: &mut Walker, mode: Mode) -> Option<Expr> {
	let start_position = match walker.peek() {
		Some((_, span)) => span.start,
		None => return None,
	};
	let mut parser = ShuntingYard {
		stack: VecDeque::new(),
		operators: VecDeque::new(),
		groups: VecDeque::new(),
		start_position,
		mode,
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

/// An open grouping of items.
#[derive(Debug, PartialEq)]
enum Group {
	/// A parenthesis group `(...)`.
	///
	/// *Note:* Whilst there may currently be no real use to storing parenthesis groups in the AST, keeping track
	/// of this in the shunting yard is necessary to correctly deal with lists within parenthesis, so this should
	/// never be removed.
	Paren,
	/// An index operator `[...]`. `bool` notes whether there is an item within the `[...]` brackets.
	Index(bool),
	/// A function call `fn(...)`.
	Fn(usize),
	/// An initializer list `{...}`.
	Init(usize),
	/// An array constructor `type[...](...)`.
	ArrInit(usize),
	/// A comma-seperated list **outside** of function calls, initializer lists and array constructors.
	///
	/// # Invariants
	/// This only exists if the outer `Group` is not of type `Group::Fn|Init|ArrInit|List`. (You can't have
	/// a list within a list since there are no delimiters, and commas within the other groups won't create an
	/// inner list but rather increase the arity).
	List(usize),
}

type Item = Either<Expr, Op>;

struct ShuntingYard {
	/// The final output stack in RPN.
	stack: VecDeque<Item>,
	/// Temporary stack to hold operators.
	operators: VecDeque<Op>,
	/// Temporary stack to hold item groups. The back-most entry is the group being currently parsed.
	///
	/// The two `usize` values represent the start and end positions of the opening delimiter, i.e.
	/// ```text
	///   func( a ...      { a ...
	///  ^     ^          ^ ^  
	/// ```
	groups: VecDeque<(Group, usize, usize)>,
	/// The start position of the first item in this expression.
	start_position: usize,
	mode: Mode,
}

impl ShuntingYard {
	/// Pushes an operator onto the stack, potentially popping any operators which have a greater precedence than
	/// the operator being pushed.
	fn push_operator(&mut self, op: Op) {
		while self.operators.back().is_some() {
			let back = self.operators.back().unwrap();

			if back.ty == OpTy::BracketStart
				|| back.ty == OpTy::IndexStart
				|| back.ty == OpTy::FnStart
				|| back.ty == OpTy::InitStart
			{
				// Group delimiter start operators always have the highest precedence, so we don't need to check
				// further.
				break;
			}
			// This is done to make `ObjAccess` right-associative.
			if op.ty == OpTy::ObjAccess && back.ty == OpTy::ObjAccess {
				let moved = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved));
				break;
			}

			if op.ty.precedence() < back.ty.precedence() {
				let moved = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved));
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

		if let Group::Paren = group {
			while self.operators.back().is_some() {
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::FnStart => println!("Mismatch between operator stack (Op::FnStart) and group stack (Group::Bracket)!"),
						OpTy::IndexStart => println!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Bracket)!"),
						OpTy::InitStart => println!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Bracket)!"),
						OpTy::ArrInitStart => println!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Bracket)!"),
						_ => {}
					}
				}

				if op.ty == OpTy::BracketStart {
					self.stack.push_back(Either::Right(Op {
						ty: OpTy::Paren,
						span: span(group_start, span_end),
					}));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right(op));
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
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::BracketStart => println!("Mismatch between operator stack (Op::BracketStart) and group stack (Group::Fn)!"),
						OpTy::IndexStart => println!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Fn)!"),
						OpTy::InitStart => println!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Fn)!"),
						OpTy::ArrInitStart => println!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Fn)!"),
						_ => {}
					}
				}

				if op.ty == OpTy::FnStart {
					// The first expression will always be the `Expr::Ident` containing the function identifier,
					// hence the `count + 1`.
					self.stack.push_back(Either::Right(Op {
						ty: OpTy::FnCall(count + 1),
						span: span(group_start, span_end),
					}));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right(op));
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
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op .ty{
						OpTy::BracketStart => println!("Mismatch between operator stack (Op::BracketStart) and group stack (Group::Index)!"),
						OpTy::FnStart => println!("Mismatch between operator stack (Op::FnStart) and group stack (Group::Index)!"),
						OpTy::InitStart => println!("Mismatch between operator stack (Op::InitStart) and group stack (Group::Index)!"),
						OpTy::ArrInitStart => println!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Index)!"),
						_ => {}
					}
				}

				if op.ty == OpTy::IndexStart {
					self.stack.push_back(Either::Right(Op {
						ty: OpTy::Index(contains_i),
						span: span(group_start, span_end),
					}));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right(op));
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
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::BracketStart => println!("Mismatch between operator stack (Op::BracketStart) and group stack (Group::Init)!"),
						OpTy::IndexStart => println!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::Init)!"),
						OpTy::FnStart => println!("Mismatch between operator stack (Op::FnStart) and group stack (Group::Init)!"),
						OpTy::ArrInitStart => println!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::Init)!"),
						_ => {}
					}
				}

				if op.ty == OpTy::InitStart {
					self.stack.push_back(Either::Right(Op {
						ty: OpTy::Init(count),
						span: span(group_start, span_end),
					}));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right(op));
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
				let op = self.operators.pop_back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::BracketStart => println!("Mismatch between operator stack (Op::BracketStart) and group stack (Group::ArrInit)!"),
						OpTy::IndexStart => println!("Mismatch between operator stack (Op::IndexStart) and group stack (Group::ArrInit)!"),
						OpTy::FnStart => println!("Mismatch between operator stack (Op::FnStart) and group stack (Group::ArrInit)!"),
						OpTy::InitStart => println!("Mismatch between operator stack (Op::InitStart) and group stack (Group::ArrInit)!"),
						_ => {}
					}
				}

				if op.ty == OpTy::ArrInitStart {
					// The first expression will always be the `Expr::Index` containing the identifier/item and the
					// array index, hence the `count + 1`.
					self.stack.push_back(Either::Right(Op {
						ty: OpTy::ArrInit(count + 1),
						span: span(group_start, span_end),
					}));
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					self.stack.push_back(Either::Right(op));
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
				let op = self.operators.back().unwrap();

				#[cfg(debug_assertions)]
				{
					match op.ty {
						OpTy::FnStart => println!("Mismatch between operator stack (Op::FnStart) and group stack (Group::List)!"),
						OpTy::InitStart => println!("Mismatch between operator stack (Op::InitStart) and group stack (Group::List)!"),
						OpTy::ArrInitStart => println!("Mismatch between operator stack (Op::ArrInitStart) and group stack (Group::List)!"),
						_ => {}
					}
				}

				// Lists don't have a starting delimiter, so we consume until we encounter another group-start
				// delimiter (and if there are none, we just end up consuming the rest of the operator stack).
				// Since lists cannnot exist within a `Group::Fn|Init|ArrInit`, we don't check for those start
				// delimiters.
				if op.ty == OpTy::BracketStart || op.ty == OpTy::IndexStart {
					start_span = op.span.end;
					break;
				} else {
					// Any other operators get moved, since we are moving everything until we hit the start
					// delimiter.
					let moved = self.operators.pop_back().unwrap();
					self.stack.push_back(Either::Right(moved));
				}
			}

			self.stack.push_back(Either::Right(Op {
				ty: OpTy::List(count),
				span: span(start_span, span_end),
			}));

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
				Either::Left(e) => &e.span,
				Either::Right(op) => &op.span,
			};

			if span.starts_at_or_after(start_pos) {
				self.stack.pop_back();
			} else {
				break;
			}
		}

		self.stack.push_back(Either::Left(Expr {
			ty: ExprTy::Incomplete,
			span: span(start_pos, end_pos),
		}));

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
			self.stack.push_back(Either::Right(Op {
				ty: OpTy::Index(true),
				span: span(start_pos, end_pos),
			}));
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
			Group::Paren | Group::Fn(_) | Group::ArrInit(_) => {}
			_ => {
				// The current group is not a bracket/function/array constructor group, so we need to check whether
				// there is one at all.
				let mut exists_paren = false;
				for (group, _, _) in self.groups.iter() {
					match group {
						Group::Paren | Group::Fn(_) | Group::ArrInit(_) => {
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
							Group::Paren | Group::Fn(_) | Group::ArrInit(_) => {
								break 'inner
							}
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
						let op = self.operators.back().unwrap();

						if op.ty == OpTy::IndexStart || op.ty == OpTy::InitStart
						{
							break 'invalidate;
						} else {
							self.operators.pop_back();
						}
					}

					'invalidate_2: while self.stack.back().is_some() {
						let span = match self.stack.back().unwrap() {
							Either::Left(e) => &e.span,
							Either::Right(op) => &op.span,
						};

						if span.starts_at_or_after(*current_group_inner_start) {
							self.stack.pop_back();
						} else {
							break 'invalidate_2;
						}
					}

					self.stack.push_back(Either::Left(Expr {
						ty: ExprTy::Incomplete,
						span: span(*current_group_inner_start, end_span.end),
					}));
					return Ok(());
				}
			}
		}

		match self.groups.back().unwrap().0 {
			Group::Paren => self.collapse_bracket(end_span.end, false),
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
						Group::Paren => {
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
					let op = self.operators.back().unwrap();

					if op.ty == OpTy::BracketStart
						|| op.ty == OpTy::FnStart
						|| op.ty == OpTy::InitStart
						|| op.ty == OpTy::ArrInitStart
					{
						break 'invalidate;
					} else {
						self.operators.pop_back();
					}
				}

				'invalidate_2: while self.stack.back().is_some() {
					let span = match self.stack.back().unwrap() {
						Either::Left(e) => &e.span,
						Either::Right(op) => &op.span,
					};

					if span.starts_at_or_after(*current_group_inner_start) {
						self.stack.pop_back();
					} else {
						break 'invalidate_2;
					}
				}

				self.stack.push_back(Either::Left(Expr {
					ty: ExprTy::Incomplete,
					span: span(*current_group_inner_start, end_span.end),
				}));
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
						Group::Paren => {
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
					let op = self.operators.back().unwrap();

					if op.ty == OpTy::BracketStart
						|| op.ty == OpTy::FnStart
						|| op.ty == OpTy::IndexStart
						|| op.ty == OpTy::ArrInitStart
					{
						break 'invalidate;
					} else {
						self.operators.pop_back();
					}
				}

				'invalidate_2: while self.stack.back().is_some() {
					let span = match self.stack.back().unwrap() {
						Either::Left(e) => &e.span,
						Either::Right(op) => &op.span,
					};

					if span.starts_at_or_after(*current_group_inner_start) {
						self.stack.pop_back();
					} else {
						break 'invalidate_2;
					}
				}

				self.stack.push_back(Either::Left(Expr {
					ty: ExprTy::Incomplete,
					span: span(*current_group_inner_start, end_span.end),
				}));
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
						let back = self.operators.back().unwrap();
						if back.ty == OpTy::FnStart
							|| back.ty == OpTy::InitStart
							|| back.ty == OpTy::ArrInitStart
						{
							break;
						}

						let moved = self.operators.pop_back().unwrap();
						self.stack.push_back(Either::Right(moved));
					}
				}
				Group::List(_) => {
					// We want to move all existing operators up to the bracket or index start delimiter, or to the
					// beginning of the expression. We don't push a new list group since we are already within a
					// list group, and it accepts a variable amount of arguments.
					while self.operators.back().is_some() {
						let back = self.operators.back().unwrap();
						if back.ty == OpTy::BracketStart
							|| back.ty == OpTy::IndexStart
						{
							break;
						}

						let moved = self.operators.pop_back().unwrap();
						self.stack.push_back(Either::Right(moved));
					}
				}
				Group::Paren | Group::Index(_) => {
					// Same as the branch above, but we do push a new list group. Since list groups don't have a
					// start delimiter, we can only do it now that we've encountered a comma within these two
					// groups.
					while self.operators.back().is_some() {
						let back = self.operators.back().unwrap();
						if back.ty == OpTy::BracketStart
							|| back.ty == OpTy::IndexStart
						{
							break;
						}

						let moved = self.operators.pop_back().unwrap();
						self.stack.push_back(Either::Right(moved));
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
				let moved = self.operators.pop_back().unwrap();
				self.stack.push_back(Either::Right(moved));
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
						Ok(l) => Either::Left(Expr {
							ty: ExprTy::Lit(l),
							span: *span,
						}),
						Err(_) => Either::Left(Expr {
							ty: ExprTy::Invalid,
							span: *span,
						}),
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
					self.stack.push_back(Either::Left(Expr {
						ty: ExprTy::Ident(Ident {
							name: s.clone(),
							span: *span,
						}),
						span: *span,
					}));
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
					break 'main;
				}
				Token::Op(op) if state == State::Operand => {
					if self.mode == Mode::BreakAtEq && *op == OpTy::Eq {
						break 'main;
					}

					match op {
						// If the operator is a valid prefix operator, we can move it to the stack. We don't switch
						// state since after a prefix operator, we are still looking for an operand atom.
						OpTy::Sub => self.push_operator(Op {
							ty: OpTy::Neg,
							span: *span,
						}),
						OpTy::Not => self.push_operator(Op {
							ty: OpTy::Not,
							span: *span,
						}),
						OpTy::Flip => self.push_operator(Op {
							ty: OpTy::Flip,
							span: *span,
						}),
						OpTy::AddAdd => self.push_operator(Op {
							ty: OpTy::AddAddPre,
							span: *span,
						}),
						OpTy::SubSub => self.push_operator(Op {
							ty: OpTy::SubSubPre,
							span: *span,
						}),
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
					if self.mode == Mode::BreakAtEq && *op == OpTy::Eq {
						break 'main;
					}

					match op {
						OpTy::Flip | OpTy::Not => {
							// These operators cannot be directly after an atom.
							println!("Expected a postfix, index or binary operator, found a prefix operator instead!");
							return;
						}
						// These operators are postfix operators. We don't switch state since after a postfix operator,
						// we are still looking for a binary operator or the end of expression, i.e.
						// `..i++ - i` rather than `..i++ i`.
						OpTy::AddAdd => {
							self.push_operator(Op {
								ty: OpTy::AddAddPost,
								span: *span,
							});
						}
						OpTy::SubSub => {
							self.push_operator(Op {
								ty: OpTy::SubSubPost,
								span: *span,
							});
						}
						// Any other operators can be part of a binary expression. We switch state since after a binary
						// operator we are expecting an operand.
						_ => {
							self.push_operator(Op {
								ty: *op,
								span: *span,
							});
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

					self.operators.push_back(Op {
						ty: OpTy::BracketStart,
						span: *span,
					});
					self.groups.push_back((Group::Paren, span.start, span.end));

					can_start = Start::None;
				}
				Token::LParen if state == State::AfterOperand => {
					if can_start == Start::Fn {
						// We have `ident(` which makes this a function call.
						self.operators.push_back(Op {
							ty: OpTy::FnStart,
							span: *span,
						});
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
						self.operators.push_back(Op {
							ty: OpTy::ArrInitStart,
							span: *span,
						});
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
					self.operators.push_back(Op {
						ty: OpTy::IndexStart,
						span: *span,
					});
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
					}

					self.operators.push_back(Op {
						ty: OpTy::InitStart,
						span: *span,
					});
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
					if self.mode == Mode::DisallowTopLevelList
						&& self.groups.is_empty()
					{
						println!("Found a `,` outside of a group, with `Mode::DisallowTopLevelList`!");
						break 'main;
					}

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
					self.push_operator(Op {
						ty: OpTy::ObjAccess,
						span: *span,
					});
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

		// The end position of this expression will be the end position of the last parsed item.
		let end_position = match self.stack.back().unwrap() {
			Either::Left(e) => e.span.end,
			Either::Right(op) => op.span.end,
		};

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
				Group::Paren => self.collapse_bracket(end_position, false),
				Group::Index(_) => self.collapse_index(end_position, true),
				Group::Fn(_) => self.collapse_fn(end_position, true),
				Group::Init(_) => self.collapse_init(end_position, true),
				Group::ArrInit(_) => self.collapse_arr_init(end_position, true),
				Group::List(_) => self.collapse_list(end_position, false),
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
		while let Some(item) = self.stack.pop_front() {
			match item {
				Either::Left(e) => stack.push_back(e),
				Either::Right(op) => match op.ty {
					OpTy::AddAddPre => {
						let expr = stack.pop_back().unwrap();
						let span = span(op.span.start, expr.span.end);
						stack.push_back(Expr {
							ty: ExprTy::Prefix {
								expr: Box::from(expr),
								op: Op {
									ty: OpTy::Add,
									span: op.span,
								},
							},
							span,
						});
					}
					OpTy::SubSubPre => {
						let expr = stack.pop_back().unwrap();
						let span = span(op.span.start, expr.span.end);
						stack.push_back(Expr {
							ty: ExprTy::Prefix {
								expr: Box::from(expr),
								op: Op {
									ty: OpTy::Sub,
									span: op.span,
								},
							},
							span,
						});
					}
					OpTy::AddAddPost => {
						let expr = stack.pop_back().unwrap();
						let span = span(expr.span.start, op.span.end);
						stack.push_back(Expr {
							ty: ExprTy::Postfix {
								expr: Box::from(expr),
								op: Op {
									ty: OpTy::Add,
									span: op.span,
								},
							},
							span,
						});
					}
					OpTy::SubSubPost => {
						let expr = stack.pop_back().unwrap();
						let span = span(expr.span.start, op.span.end);
						stack.push_back(Expr {
							ty: ExprTy::Postfix {
								expr: Box::from(expr),
								op: Op {
									ty: OpTy::Sub,
									span: op.span,
								},
							},
							span,
						});
					}
					OpTy::Neg => {
						let expr = stack.pop_back().unwrap();
						let span = span(op.span.start, expr.span.end);
						stack.push_back(Expr {
							ty: ExprTy::Prefix {
								expr: Box::from(expr),
								op: Op {
									ty: OpTy::Neg,
									span: op.span,
								},
							},
							span,
						});
					}
					OpTy::Flip => {
						let expr = stack.pop_back().unwrap();
						let span = span(op.span.start, expr.span.end);
						stack.push_back(Expr {
							ty: ExprTy::Prefix {
								expr: Box::from(expr),
								op: Op {
									ty: OpTy::Flip,
									span: op.span,
								},
							},
							span,
						});
					}
					OpTy::Not => {
						let expr = stack.pop_back().unwrap();
						let span = span(op.span.start, expr.span.end);
						stack.push_back(Expr {
							ty: ExprTy::Prefix {
								expr: Box::from(expr),
								op: Op {
									ty: OpTy::Not,
									span: op.span,
								},
							},
							span,
						});
					}
					OpTy::Paren => {
						// Note: the span for `Op::Paren` is from the start of the `(` to the end of the `)`.
						let expr = stack.pop_back().unwrap();
						let l_span = op.span.first_char();
						let r_span = op.span.last_char();
						stack.push_back(Expr {
							ty: ExprTy::Paren {
								expr: Box::from(expr),
								left: l_span,
								right: r_span,
							},
							span: op.span,
						});
					}
					OpTy::Index(contains_i) => {
						// Note: the span for `Op::Index` is from the start of the `[` to the end of the `]`.
						let i = if contains_i {
							Some(Box::from(stack.pop_back().unwrap()))
						} else {
							None
						};
						let expr = stack.pop_back().unwrap();
						let span = span(expr.span.start, op.span.end);
						stack.push_back(Expr {
							ty: ExprTy::Index {
								item: Box::from(expr),
								i,
								op: op.span,
							},
							span,
						});
					}
					OpTy::ObjAccess => {
						let access = stack.pop_back().unwrap();
						let obj = stack.pop_back().unwrap();
						let span = span(obj.span.start, access.span.end);
						stack.push_back(Expr {
							ty: ExprTy::ObjAccess {
								obj: Box::from(obj),
								leaf: Box::from(access),
							},
							span,
						});
					}
					OpTy::FnCall(count) => {
						// Note: the span for `Op::FnCall` is from the start of the identifier `fn(` to the end of
						// the `)`.
						let mut args = VecDeque::new();
						for _ in 0..count {
							args.push_front(stack.pop_back().unwrap());
						}
						// Get the identifier (which is the first expression).
						let ident = match args.pop_front().unwrap().ty {
							ExprTy::Ident(i) => i,
							_ => panic!("The first expression of a function call operator is not an identifier!")
						};
						stack.push_back(Expr {
							ty: ExprTy::Fn {
								ident,
								args: args.into(),
							},
							span: op.span,
						});
					}
					OpTy::Init(count) => {
						// Note: the span for `Op::Init` is from the start of the `{` to the end of the `}`.
						let mut args = Vec::new();
						for _ in 0..count {
							args.push(stack.pop_back().unwrap());
						}
						args.reverse();
						stack.push_back(Expr {
							ty: ExprTy::Init(args),
							span: op.span,
						});
					}
					OpTy::ArrInit(count) => {
						let mut args = VecDeque::new();
						for _ in 0..count {
							args.push_front(stack.pop_back().unwrap());
						}
						// Get the index operator (which is the first expression).
						let arr = args.pop_front().unwrap();
						match arr.ty {
							ExprTy::Index { .. } => {}
							_ => {
								panic!("The first expression of an array constructor operator is not an `Expr::Index`!");
							}
						}
						stack.push_back(Expr {
							ty: ExprTy::ArrInit {
								arr: Box::from(arr),
								args: args.into(),
							},
							span: op.span,
						});
					}
					OpTy::List(count) => {
						let mut args = Vec::new();
						for _ in 0..count {
							args.push(stack.pop_back().unwrap());
						}
						args.reverse();
						stack.push_back(Expr {
							ty: ExprTy::List(args),
							span: op.span,
						});
					}
					OpTy::Add
					| OpTy::Sub
					| OpTy::Mul
					| OpTy::Div
					| OpTy::Rem
					| OpTy::And
					| OpTy::Or
					| OpTy::Xor
					| OpTy::LShift
					| OpTy::RShift
					| OpTy::EqEq
					| OpTy::NotEq
					| OpTy::Gt
					| OpTy::Lt
					| OpTy::Ge
					| OpTy::Le
					| OpTy::AndAnd
					| OpTy::OrOr
					| OpTy::XorXor
					| OpTy::Eq
					| OpTy::AddEq
					| OpTy::SubEq
					| OpTy::MulEq
					| OpTy::DivEq
					| OpTy::RemEq
					| OpTy::AndEq
					| OpTy::OrEq
					| OpTy::XorEq
					| OpTy::LShiftEq
					| OpTy::RShiftEq => {
						let right = stack.pop_back().unwrap();
						let left = stack.pop_back().unwrap();
						let span = span(left.span.start, right.span.end);
						stack.push_back(Expr {
							ty: ExprTy::Binary {
								left: Box::from(left),
								op,
								right: Box::from(right),
							},
							span,
						});
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
		Some(stack.pop_back().unwrap())
	}
}

#[rustfmt::skip]
impl OpTy {
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
			Self::Eq
			| Self::AddEq
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
			| Self::ArrInit(_)
			| Self::List(_) => {
				panic!("The operator {self:?} does not have a precedence value because it should never be passed into this function. Something has gone wrong!")
			},
		}
	}
}

// Purely used for debugging the parsed expressions.
impl std::fmt::Display for ShuntingYard {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for item in self.stack.iter() {
			match item {
				Either::Left(e) => write!(f, "{e} ")?,
				Either::Right(op) => write!(f, "{op} ")?,
			}
		}
		Ok(())
	}
}

impl std::fmt::Display for Op {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self.ty {
			// Maths
			OpTy::Add => write!(f, "+"),
			OpTy::Sub => write!(f, "-"),
			OpTy::Mul => write!(f, "*"),
			OpTy::Div => write!(f, "/"),
			OpTy::Rem => write!(f, "%"),
			OpTy::And => write!(f, "&"),
			OpTy::Or => write!(f, "|"),
			OpTy::Xor => write!(f, "^"),
			OpTy::LShift => write!(f, "<<"),
			OpTy::RShift => write!(f, ">>"),
			OpTy::Eq => write!(f, "="),
			OpTy::AddEq => write!(f, "+="),
			OpTy::SubEq => write!(f, "-="),
			OpTy::MulEq => write!(f, "*="),
			OpTy::DivEq => write!(f, "/="),
			OpTy::RemEq => write!(f, "%="),
			OpTy::AndEq => write!(f, "&="),
			OpTy::OrEq => write!(f, "|="),
			OpTy::XorEq => write!(f, "^="),
			OpTy::LShiftEq => write!(f, "<<="),
			OpTy::RShiftEq => write!(f, ">>="),
			OpTy::Neg => write!(f, "neg"),
			OpTy::Flip => write!(f, "~"),
			OpTy::AddAdd => write!(f, "NOP"),
			OpTy::SubSub => write!(f, "NOP"),
			//
			// Comparison
			OpTy::EqEq => write!(f, "=="),
			OpTy::NotEq => write!(f, "!="),
			OpTy::Gt => write!(f, ">"),
			OpTy::Lt => write!(f, "<"),
			OpTy::Ge => write!(f, ">="),
			OpTy::Le => write!(f, "<="),
			OpTy::AndAnd => write!(f, "&&"),
			OpTy::OrOr => write!(f, "||"),
			OpTy::XorXor => write!(f, "^^"),
			OpTy::Not => write!(f, "!"),
			//
			// Shunting Yard
			OpTy::AddAddPre => write!(f, "++pre"),
			OpTy::AddAddPost => write!(f, "++post"),
			OpTy::SubSubPre => write!(f, "--pre"),
			OpTy::SubSubPost => write!(f, "--post"),
			OpTy::BracketStart
			| OpTy::FnStart
			| OpTy::IndexStart
			| OpTy::InitStart
			| OpTy::ArrInitStart => {
				write!(f, "")
			}
			OpTy::Paren => write!(f, ""),
			OpTy::Index(true) => write!(f, "index"),
			OpTy::Index(false) => write!(f, "empty_index"),
			OpTy::ObjAccess => write!(f, "access"),
			OpTy::FnCall(count) => write!(f, "FN:{count}"),
			OpTy::Init(count) => write!(f, "INIT:{count}"),
			OpTy::ArrInit(count) => write!(f, "ARR_INIT:{count}"),
			OpTy::List(count) => write!(f, "LIST:{count}"),
		}
	}
}

#[cfg(test)]
use crate::lexer::lexer;

/// Asserts the expression output of the `expr_parser()` matches the right hand side; ignores spans.
#[cfg(test)]
macro_rules! assert_expr {
	($source:expr, $rest:expr) => {
		let mut walker = Walker {
			cst: lexer($source),
			cursor: 0,
		};
		assert_eq!(expr_parser(&mut walker, Mode::Default).unwrap(), $rest);
	};
}

#[test]
#[rustfmt::skip]
fn binaries() {
	// Single operator
	assert_expr!("5 + 1", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
			op: Op{ty: OpTy::Add, span: span(2, 3)},
			right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)})
		},
		span: span(0, 5)
	});
	assert_expr!("ident * 100.4", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "ident".into(), span: span(0, 5)}), span: span(0, 5)}),
			op: Op{ty: OpTy::Mul, span: span(6, 7)},
			right: Box::from(Expr{ty: ExprTy::Lit(Lit::Float(100.4)), span: span(8, 13)})
		},
		span: span(0, 13)
	});
	assert_expr!("30 << 8u", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(30)), span: span(0, 2)}),
			op: Op{ty: OpTy::LShift, span: span(3, 5)},
			right: Box::from(Expr{ty: ExprTy::Lit(Lit::UInt(8)), span: span(6, 8)})
		},
		span: span(0, 8),
	});

	// Multiple operators
	assert_expr!("5 + 1 / 3", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
			op: Op{ty: OpTy::Add, span: span(2, 3)},
			right: Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)}),
					op: Op{ty: OpTy::Div, span: span(6, 7)},
					right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(3)), span: span(8, 9)})
				},
				span: span(4, 9),
			})
		},
		span: span(0, 9),
	});
	assert_expr!("5 * 4 * 3", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
			op: Op{ty: OpTy::Mul, span: span(2, 3)},
			right: Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(4)), span: span(4, 5)}),
					op: Op{ty: OpTy::Mul, span: span(6, 7)},
					right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(3)), span: span(8, 9)})
				},
				span: span(4, 9),
			})
		},
		span: span(0, 9),
	});
	assert_expr!("5 + 1 / 3 * i", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
			op: Op{ty: OpTy::Add, span: span(2, 3)},
			right: Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)}),
					op: Op{ty: OpTy::Div, span: span(6, 7)},
					right: Box::from(Expr {
						ty: ExprTy::Binary {
							left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(3)), span: span(8, 9)}),
							op: Op{ty: OpTy::Mul, span: span(10, 11)},
							right: Box::from(Expr{ty:ExprTy::Ident(Ident{name: "i".into(), span: span(12, 13)}), span: span(12, 13)})
						},
						span: span(8, 13)
					})
				},
				span: span(4, 13),
			})
		},
		span: span(0, 13),
	});
	assert_expr!("5 + 1 == true * i", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
					op: Op{ty: OpTy::Add, span: span(2, 3)},
					right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)})
				},
				span: span(0, 5),
			}),
			op: Op{ty: OpTy::EqEq, span: span(6, 8)},
			right: Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Lit(Lit::Bool(true)), span: span(9, 13)}),
					op: Op{ty: OpTy::Mul, span: span(14, 15)},
					right: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(16, 17)}), span: span(16, 17)})
				},
				span: span(9, 17),
			})
		},
		span: span(0, 17)
	});
}

#[test]
#[rustfmt::skip]
fn brackets() {
	assert_expr!("(5 + 1) * 8", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{
				ty: ExprTy::Paren {
					expr: Box::from(Expr{
						ty: ExprTy::Binary {
							left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(1, 2)}),
							op: Op{ty: OpTy::Add, span: span(3, 4)},
							right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(5, 6)}),
						},
						span: span(1, 6),
					}),
					left: span(0, 1),
					right: span(6, 7),
				},
				span: span(0, 7),
			}),
			op: Op{ty: OpTy::Mul, span: span(8, 9)},
			right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(8)), span: span(10, 11)})
		},
		span: span(0, 11),
	});
	assert_expr!("((5 + 1) < 100) * 8", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr {
				ty: ExprTy::Paren {
					expr: Box::from(Expr {
						ty: ExprTy::Binary {
							left: Box::from(Expr {
								ty: ExprTy::Paren {
									expr: Box::from(Expr {
										ty: ExprTy::Binary {
											left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)}),
											op: Op{ty: OpTy::Add, span: span(4, 5)},
											right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(6, 7)}),
										},
										span: span(2, 7),
									}),
									left: span(1, 2),
									right: span(7, 8),
								},
								span: span(1, 8),
							}),
							op: Op{ty: OpTy::Lt, span: span(9, 10)},
							right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(100)), span: span(11, 14)}),
						},
						span: span(1, 14),
					}),
					left: span(0, 1),
					right: span(14, 15),
				},
				span: span(0, 15),
			}),
			op: Op{ty: OpTy::Mul, span: span(16, 17)},
			right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(8)), span: span(18, 19)})
		},
		span: span(0, 19),
	});
}

#[test]
#[rustfmt::skip]
fn unaries() {
	// Single operator
	assert_expr!("-5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(1, 2)}),
			op: Op{ty: OpTy::Neg, span: span(0, 1)},
		},
		span: span(0, 2),
	});
	assert_expr!("~5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(1, 2)}),
			op: Op{ty: OpTy::Flip, span: span(0, 1)},
		},
		span: span(0, 2),
	});
	assert_expr!("!5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(1, 2)}),
			op: Op{ty: OpTy::Not, span: span(0, 1)},
		},
		span: span(0, 2),
	});
	assert_expr!("++5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)}),
			op: Op{ty: OpTy::Add, span: span(0, 2)},
		},
		span: span(0, 3),
	});
	assert_expr!("--5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)}),
			op: Op{ty: OpTy::Sub, span: span(0, 2)},
		},
		span: span(0, 3),
	});
	assert_expr!("5++", Expr {
		ty: ExprTy::Postfix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
			op: Op{ty: OpTy::Add, span: span(1, 3)},
		},
		span: span(0, 3),
	});
	assert_expr!("5--", Expr {
		ty: ExprTy::Postfix {
			expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(0, 1)}),
			op: Op{ty: OpTy::Sub, span: span(1, 3)},
		},
		span: span(0, 3),
	});

	// Multiple operators
	assert_expr!("- -5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{
				ty: ExprTy::Prefix {
					expr: Box::from(Expr{ty:ExprTy::Lit(Lit::Int(5)), span: span(3, 4)}),
					op: Op{ty: OpTy::Neg, span: span(2, 3)},
				},
				span: span(2, 4),
			}),
			op: Op{ty: OpTy::Neg, span: span(0, 1)},
		},
		span: span(0, 4),
	});
	assert_expr!("- - -5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{
				ty: ExprTy::Prefix {
					expr: Box::from(Expr {
						ty: ExprTy::Prefix {
							expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(5, 6)}),
							op: Op{ty: OpTy::Neg, span: span(4, 5)},
						},
						span: span(4, 6),
					}),
					op: Op{ty: OpTy::Neg, span: span(2, 3)},
				},
				span: span(2, 6),
			}),
			op: Op{ty: OpTy::Neg, span: span(0, 1)},
		},
		span: span(0, 6),
	});
	assert_expr!("!!5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr{
				ty: ExprTy::Prefix {
					expr: Box::from(Expr{ty:ExprTy::Lit(Lit::Int(5)), span: span(2, 3)}),
					op: Op{ty: OpTy::Not, span: span(1, 2)},
				},
				span: span(1, 3),
			}),
			op: Op{ty: OpTy::Not, span: span(0, 1)},
		},
		span: span(0, 3),
	});
	assert_expr!("++++5", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr {
				ty: ExprTy::Prefix {
					expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(4, 5)}),
					op: Op{ty: OpTy::Add, span: span(2, 4)},
				},
				span: span(2, 5),
			}),
			op: Op{ty: OpTy::Add, span: span(0, 2)},
		},
		span: span(0, 5),
	});
	assert_expr!("++5--", Expr {
		ty: ExprTy::Prefix {
			expr: Box::from(Expr {
				ty: ExprTy::Postfix {
					expr: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)}),
					op: Op{ty: OpTy::Sub, span: span(3, 5)},
				},
				span: span(2, 5),
			}),
			op: Op{ty: OpTy::Add, span: span(0, 2)},
		},
		span: span(0, 5),
	});
}

#[test]
#[rustfmt::skip]
fn fn_calls() {
	assert_expr!("fn()", Expr {
		ty: ExprTy::Fn{ident: Ident{name: "fn".into(), span: span(0, 2)}, args: vec![]},
		span: span(0, 4),
	});
	assert_expr!("fu_nc(1)", Expr {
		ty: ExprTy::Fn{ident: Ident{name: "fu_nc".into(), span: span(0, 5)}, args: vec![
			Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(6, 7)},
		]},
		span: span(0, 8),
	});
	assert_expr!("fn(5 + 1, i << 6)", Expr {
		ty: ExprTy::Fn {
			ident: Ident{name: "fn".into(), span: span(0, 2)},
			args: vec![
				Expr {
					ty: ExprTy::Binary {
						left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(3, 4)}),
						right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(7, 8)}),
						op: Op{ty: OpTy::Add, span: span(5, 6)},
					},
					span: span(3, 8),
				},
				Expr {
					ty: ExprTy::Binary {
						left: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(10, 11)}), span: span(10, 11)}),
						right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(6)), span: span(15, 16)}),
						op: Op{ty: OpTy::LShift, span: span(12, 14)},
					},
					span: span(10, 16),
				}
			]
		},
		span: span(0, 17),
	});
	assert_expr!("fn(fn())", Expr {
		ty: ExprTy::Fn{ident: Ident{name: "fn".into(), span: span(0, 2)}, args: vec![Expr {
			ty: ExprTy::Fn{ident: Ident{name: "fn".into(), span: span(3, 5)}, args: vec![]},
			span: span(3, 7),
		}]},
		span: span(0, 8),
	});
	assert_expr!("fn1(5, fn2(0))", Expr {
		ty: ExprTy::Fn {
			ident: Ident{name: "fn1".into(), span: span(0, 3)},
			args: vec![
				Expr {
					ty: ExprTy::Lit(Lit::Int(5)),
					span: span(4, 5),
				},
				Expr {
					ty: ExprTy::Fn{ident: Ident{name: "fn2".into(), span: span(7, 10)}, args: vec![Expr {
						ty: ExprTy::Lit(Lit::Int(0)),
						span: span(11, 12),
					}]},
					span: span(7, 13),
				}
			]
		},
		span: span(0, 14),
	});
	assert_expr!("fn1(5, fn2(fn3()))", Expr {
		ty: ExprTy::Fn {
			ident: Ident{name: "fn1".into(), span: span(0, 3)},
			args: vec![
				Expr {
					ty: ExprTy::Lit(Lit::Int(5)),
					span: span(4, 5),
				},
				Expr {
					ty: ExprTy::Fn{ident: Ident{name: "fn2".into(), span: span(7, 10)}, args: vec![Expr {
						ty: ExprTy::Fn{ident: Ident{name: "fn3".into(), span: span(11, 14)}, args: vec![]},
						span: span(11, 16),
					}]},
					span: span(7, 17),
				}
			]
		},
		span: span(0, 18),
	});
}

#[test]
#[rustfmt::skip]
fn obj_access() {
	assert_expr!("ident.something", Expr {
		ty: ExprTy::ObjAccess {
			obj: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "ident".into(), span: span(0, 5)}), span: span(0, 5)}),
			leaf: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "something".into(), span: span(6, 15)}), span: span(6, 15)}),
		},
		span: span(0, 15),
	});
	/* assert_expr!("a.b.c", Expr::ObjAccess {
		obj: Box::from(Expr::Ident(Ident("a".into()))),
		access: Box::from(Expr::ObjAccess {
			obj: Box::from(Expr::Ident(Ident("b".into()))),
			access: Box::from(Expr::Ident(Ident("c".into())))
		})
	}); */
	assert_expr!("a.b.c", Expr {
		ty: ExprTy::ObjAccess {
			obj: Box::from(Expr {
				ty: ExprTy::ObjAccess {
					obj: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "a".into(), span: span(0, 1)}), span: span(0, 1)}),
					leaf: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "b".into(), span: span(2, 3)}), span: span(2, 3)}),
				},
				span: span(0, 3),
			}),
			leaf: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "c".into(), span: span(4, 5)}), span: span(4, 5)}),
		},
		span: span(0, 5),
	});
	assert_expr!("fn().x", Expr {
		ty: ExprTy::ObjAccess {
			obj: Box::from(Expr{ty: ExprTy::Fn{ident: Ident{name: "fn".into(), span: span(0, 2)}, args: vec![]}, span: span(0, 4)}),
			leaf: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "x".into(), span: span(5, 6)}), span: span(5, 6)}),
		},
		span: span(0, 6),
	});
}

#[test]
#[rustfmt::skip]
fn indexes() {
	// Single-dimensional indexes
	assert_expr!("i[0]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span:span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(0)), span: span(2, 3)})),
			op: span(1, 4),
		},
		span: span(0, 4),
	});
	assert_expr!("s[z+1]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "s".into(), span:span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "z".into(), span: span(2, 3)}), span: span(2, 3)}),
					op: Op{ty: OpTy::Add, span: span(3, 4)},
					right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)}),
				},
				span: span(2, 5),
			})),
			op: span(1, 6)
		},
		span: span(0, 6),
	});
	assert_expr!("i[y[5]]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span:span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "y".into(), span:span(2, 3)}), span: span(2, 3)}),
					i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(4, 5)})),
					op: span(3, 6),
				},
				span: span(2, 6),
			})),
			op: span(1, 7)
		},
		span: span(0, 7),
	});
	assert_expr!("i[y[z[1+2]]]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span:span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "y".into(), span:span(2, 3)}), span: span(2, 3)}),
					i: Some(Box::from(Expr {
						ty: ExprTy::Index {
							item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "z".into(), span:span(4, 5)}), span: span(4, 5)}),
							i: Some(Box::from(Expr {
								ty: ExprTy::Binary {
									left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(6, 7)}),
									op: Op{ty: OpTy::Add, span: span(7, 8)},
									right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(8, 9)}),
								},
								span: span(6, 9),
							})),
							op: span(5, 10),
						},
						span: span(4, 10),
					})),
					op: span(3, 11),
				},
				span: span(2, 11),
			})),
			op: span(1, 12)
		},
		span: span(0, 12),
	});

	// Multi-dimensional indexes
	assert_expr!("i[5][2]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
					i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)})),
					op: span(1, 4),
				},
				span: span(0, 4),
			}),
			i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(5, 6)})),
			op: span(4, 7),
		},
		span: span(0, 7),
	});
	assert_expr!("i[5][2][size]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr {
						ty: ExprTy::Index {
							item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
							i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)})),
							op: span(1, 4),
						},
						span: span(0, 4),
					}),
					i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(5, 6)})),
					op: span(4, 7),
				},
				span: span(0, 7),
			}),
			i: Some(Box::from(Expr{ty: ExprTy::Ident(Ident{name: "size".into(), span: span(8, 12)}), span: span(8, 12)})),
			op: span(7, 13),
		},
		span: span(0, 13),
	});

	// Empty indexes
	assert_expr!("i[]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span:span(0, 1)}), span: span(0, 1)}),
			i: None,
			op: span(1, 3),
		},
		span: span(0, 3),
	});
	assert_expr!("int[i[]]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "int".into(), span:span(0, 3)}), span: span(0, 3)}),
			i: Some(Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span:span(4, 5)}), span: span(4, 5)}),
					i: None,
					op: span(5, 7),
				},
				span: span(4, 7),
			})),
			op: span(3, 8)
		},
		span: span(0, 8),
	});
	assert_expr!("i[][]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
					i: None,
					op: span(1, 3),
				},
				span: span(0, 3),
			}),
			i: None,
			op: span(3, 5),
		},
		span: span(0, 5),
	});
	assert_expr!("i[5][2][]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr {
						ty: ExprTy::Index {
							item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
							i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(2, 3)})),
							op: span(1, 4),
						},
						span: span(0, 4),
					}),
					i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(5, 6)})),
					op: span(4, 7),
				},
				span: span(0, 7),
			}),
			i: None,
			op: span(7, 9),
		},
		span: span(0, 9),
	});
}

#[test]
#[rustfmt::skip]
fn arr_constructors() {
	assert_expr!("int[1](2)", Expr {
		ty: ExprTy::ArrInit {
			arr: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "int".into(), span: span(0, 3)}), span: span(0, 3)}),
					i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)})),
					op: span(3, 6),
				},
				span: span(0, 6),
			}),
			args: vec![Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(7, 8)}],
		},
		span: span(0, 9),
	});
	// FIXME: This test fails because the `delim_start` gets reset by the `size` identifier. We need a way of
	// storing delim starters that can be nested; maybe with the identifier itself or something?
	/* assert_expr!("int[size](2, false, 5.0)", Expr {
		ty: ExprTy::ArrInit {
			arr: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "int".into(), span: span(0, 3)}), span: span(0, 3)}),
					i: Some(Box::from(Expr{ty: ExprTy::Ident(Ident{name: "size".into(), span: span(4, 8)}), span: span(4, 8)})),
					op: span(3, 9),
				},
				span: span(0, 9),
			}),
			args: vec![
				Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(10, 11)},
				Expr{ty: ExprTy::Lit(Lit::Bool(false)), span: span(13, 18)},
				Expr{ty: ExprTy::Lit(Lit::Float(5.0)), span: span(20, 23)}
			],
		},
		span: span(0, 24),
	}); */
	assert_expr!("int[1+5](2)", Expr {
		ty: ExprTy::ArrInit {
			arr: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "int".into(), span: span(0, 3)}), span: span(0, 3)}),
					i: Some(Box::from(Expr {
						ty: ExprTy::Binary {
							left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(4, 5)}),
							op: Op{ty: OpTy::Add, span: span(5, 6)},
							right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(5)), span: span(6, 7)}),
						},
						span: span(4, 7),
					})),
					op: span(3, 8),
				},
				span: span(0, 8),
			}),
			args: vec![Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(9, 10)}],
		},
		span: span(0, 11),
	});
	assert_expr!("vec3[](2)", Expr {
		ty: ExprTy::ArrInit {
			arr: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "vec3".into(), span: span(0, 4)}), span: span(0, 4)}),
					i: None,
					op: span(4, 6),
				},
				span: span(0, 6),
			}),
			args: vec![Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(7, 8)}],
		},
		span: span(0, 9),
	});
}

#[test]
#[rustfmt::skip]
fn initializers() {
	assert_expr!("{1}", Expr {
		ty: ExprTy::Init(vec![
			Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(1, 2)},
		]),
		span: span(0, 3),
	});
	assert_expr!("{1,}", Expr {
		ty: ExprTy::Init(vec![
			Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(1, 2)},
		]),
		span: span(0, 4),
	});
	assert_expr!("{1, true, i}", Expr {
		ty: ExprTy::Init(vec![
			Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(1, 2)},
			Expr{ty: ExprTy::Lit(Lit::Bool(true)), span: span(4, 8)},
			Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(10, 11)}), span: span(10, 11)},
		]),
		span: span(0, 12),
	});
	assert_expr!("{2.0, {1, s}}", Expr {
		ty: ExprTy::Init(vec![
			Expr{ty: ExprTy::Lit(Lit::Float(2.0)), span: span(1, 4)},
			Expr {
				ty: ExprTy::Init(vec![
					Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(7, 8)},
					Expr{ty: ExprTy::Ident(Ident{name: "s".into(), span: span(10, 11)}), span: span(10, 11)},
				]),
				span: span(6, 12),
			}
		]),
		span: span(0, 13),
	});
}

#[test]
#[rustfmt::skip]
fn lists() {
	// Note: Lists cannot exist within function calls, array constructors or initializer lists. Hence the absence
	// of those from this test.
	assert_expr!("a, b", Expr {
		ty: ExprTy::List(vec![
			Expr{ty: ExprTy::Ident(Ident{name: "a".into(), span: span(0, 1)}), span: span(0, 1)},
			Expr{ty: ExprTy::Ident(Ident{name: "b".into(), span: span(3, 4)}), span: span(3, 4)},
		]),
		span: span(0, 4),
	});
	assert_expr!("a, b, c", Expr {
		ty: ExprTy::List(vec![
			Expr{ty: ExprTy::Ident(Ident{name: "a".into(), span: span(0, 1)}), span: span(0, 1)},
			Expr{ty: ExprTy::Ident(Ident{name: "b".into(), span: span(3, 4)}), span: span(3, 4)},
			Expr{ty: ExprTy::Ident(Ident{name: "c".into(), span: span(6, 7)}), span: span(6, 7)},
		]),
		span: span(0, 7),
	});
	assert_expr!("i[a, b]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr {
				ty: ExprTy::List(vec![
					Expr{ty: ExprTy::Ident(Ident{name: "a".into(), span: span(2, 3)}), span: span(2, 3)},
					Expr{ty: ExprTy::Ident(Ident{name: "b".into(), span: span(5, 6)}), span: span(5, 6)},
				]),
				span: span(2, 6),
			})),
			op: span(1, 7),
		},
		span: span(0, 7),
	});
	assert_expr!("(a, b)", Expr {
		ty: ExprTy::Paren {
			expr: Box::from(Expr {
				ty: ExprTy::List(vec![
					Expr{ty: ExprTy::Ident(Ident{name: "a".into(), span: span(1, 2)}), span: span(1, 2)},
					Expr{ty: ExprTy::Ident(Ident{name: "b".into(), span: span(4, 5)}), span: span(4, 5)},
				]),
				span: span(1, 5),
			}),
			left: span(0, 1),
			right: span(5, 6),
		},
		span: span(0, 6),
	});
}

#[test]
#[rustfmt::skip]
fn complex() {
	assert_expr!("func(i[9], foo-- -6)", Expr {
		ty: ExprTy::Fn {
			ident: Ident{name: "func".into(), span: span(0, 4)},
			args: vec![
				Expr {
					ty: ExprTy::Index {
						item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(5, 6)}), span: span(5, 6)}),
						i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(9)), span: span(7, 8)})),
						op: span(6, 9),
					},
					span: span(5, 9),
				},
				Expr {
					ty: ExprTy::Binary {
						left: Box::from(Expr {
							ty: ExprTy::Postfix {
								expr: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "foo".into(), span: span(11, 14)}), span: span(11, 14)}),
								op: Op{ty: OpTy::Sub, span: span(14, 16)},
							},
							span: span(11, 16),
						}),
						op: Op{ty: OpTy::Sub, span: span(17, 18)},
						right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(6)), span: span(18, 19)}),
					},
					span: span(11, 19),
				}
				
			]
		},
		span: span(0, 20),
	});
	assert_expr!("true << i[func((1 + 2) * 5.0)]", Expr {
		ty: ExprTy::Binary {
			left: Box::from(Expr{ty: ExprTy::Lit(Lit::Bool(true)), span: span(0, 4)}),
			op: Op{ty: OpTy::LShift, span: span(5, 7)},
			right: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(8, 9)}), span: span(8, 9)}),
					i: Some(Box::from(Expr {
						ty: ExprTy::Fn {
							ident: Ident{name: "func".into(), span: span(10, 14)},
							args: vec![
								Expr {
									ty: ExprTy::Binary {
										left: Box::from(Expr {
											ty: ExprTy::Paren {
												expr: Box::from(Expr {
													ty: ExprTy::Binary {
														left: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(16, 17)}),
														op: Op{ty: OpTy::Add, span: span(18, 19)},
														right: Box::from(Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(20, 21)}),
													},
													span: span(16, 21),
												}),
												left: span(15, 16),
												right: span(21, 22),
											},
											span: span(15, 22),
										}),
										op: Op{ty: OpTy::Mul, span: span(23, 24)},
										right: Box::from(Expr{ty: ExprTy::Lit(Lit::Float(5.0)), span: span(25, 28)}),
									},
									span: span(15, 28),
								}
							],
						},
						span: span(10, 29),
					})),
					op: span(9, 30),
				},
				span: span(8, 30),
			}),
		},
		span: span(0, 30),
	});
	assert_expr!("{1.0, true, func(i[0], 100u)}", Expr {
		ty: ExprTy::Init(vec![
			Expr{ty: ExprTy::Lit(Lit::Float(1.0)), span: span(1, 4)},
			Expr{ty: ExprTy::Lit(Lit::Bool(true)), span: span(6, 10)},
			Expr {
				ty: ExprTy::Fn {
					ident: Ident{name: "func".into(), span: span(12, 16)},
					args: vec![
						Expr {
							ty: ExprTy::Index {
								item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(17, 18)}), span: span(17, 18)}),
								i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(0)), span: span(19, 20)})),
								op: span(18, 21),
							},
							span: span(17, 21),
						},
						Expr{ty: ExprTy::Lit(Lit::UInt(100)), span: span(23, 27)},
					]
				},
				span: span(12, 28),
			}
		]),
		span: span(0, 29),
	});
	assert_expr!("mat2[]({vec2(1, 2), vec2(3, 4)})", Expr {
		ty: ExprTy::ArrInit {
			arr: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "mat2".into(), span: span(0, 4)}), span: span(0, 4)}),
					i: None,
					op: span(4, 6),
				},
				span: span(0, 6),
			}),
			args: vec![Expr {
				ty: ExprTy::Init(vec![
					Expr {
						ty: ExprTy::Fn {
							ident: Ident{name: "vec2".into(), span: span(8, 12)},
							args: vec![
								Expr{ty: ExprTy::Lit(Lit::Int(1)), span: span(13, 14)},
								Expr{ty: ExprTy::Lit(Lit::Int(2)), span: span(16, 17)},
							],
						},
						span: span(8, 18),
					},
					Expr {
						ty: ExprTy::Fn {
							ident: Ident{name: "vec2".into(), span: span(20, 24)},
							args: vec![
								Expr{ty: ExprTy::Lit(Lit::Int(3)), span: span(25, 26)},
								Expr{ty: ExprTy::Lit(Lit::Int(4)), span: span(28, 29)},
							],
						},
						span: span(20, 30),
					},
				]),
				span: span(7, 31),
			}],
		},
		span: span(0, 32),
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
	assert_expr!("i[(5+1]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr{ty: ExprTy::Incomplete, span: span(2, 6)})),
			op: span(1, 7),
		},
		span: span(0, 7),
	});
	assert_expr!("i[fn((5+1]", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr{ty: ExprTy::Incomplete, span: span(2, 9)})),
			op: span(1, 10),
		},
		span: span(0, 10),
	});
	assert_expr!("(i+5])", Expr {
		ty: ExprTy::Paren {
			expr: Box::from(Expr{ty: ExprTy::Incomplete, span: span(1, 5)}),
			left: span(0, 1),
			right: span(5, 6),
		},
		span: span(0, 6),
	});
	assert_expr!("fn(1])", Expr {
		ty: ExprTy::Fn {
			ident: Ident{name: "fn".into(), span: span(0, 2)},
			args: vec![Expr{ty: ExprTy::Incomplete, span: span(3, 5)}]
		},
		span: span(0, 6),
	});
	assert_expr!("int[3](i])", Expr {
		ty: ExprTy::ArrInit {
			arr: Box::from(Expr {
				ty: ExprTy::Index {
					item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "int".into(), span: span(0, 3)}), span: span(0, 3)}),
					i: Some(Box::from(Expr{ty: ExprTy::Lit(Lit::Int(3)), span: span(4, 5)})),
					op: span(3, 6),
				},
				span: span(0, 6),
			}),
			args: vec![Expr{ty: ExprTy::Incomplete, span: span(7, 9)}],
		},
		span: span(0, 10),
	});

	// Outer unclosed delimiters.
	// FIXME: The `right` span should be 4, 4 but it is 4,3 because the `create_ast()` method gets the last char. I
	// guess the paren operator should hold this information.
	/* assert_expr!("(i+x", Expr {
		ty: ExprTy::Paren {
			expr: Box::from(Expr {
				ty: ExprTy::Binary {
					left: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(1, 2)}), span: span(1, 2)}),
					op: Op{ty: OpTy::Add, span: span(2, 3)},
					right: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "x".into(), span: span(3, 4)}), span: span(3, 4)}),
				},
				span: span(1, 4),
			}),
			left: span(0, 1),
			right: span(4, 4),
		},
		span: span(0, 4),
	}); */
	assert_expr!("i[5+1", Expr {
		ty: ExprTy::Index {
			item: Box::from(Expr{ty: ExprTy::Ident(Ident{name: "i".into(), span: span(0, 1)}), span: span(0, 1)}),
			i: Some(Box::from(Expr{ty: ExprTy::Incomplete, span: span(1, 5)})),
			op: span(1, 5),
		},
		span: span(0, 5),
	});
	assert_expr!("fn(5+1", Expr{ty: ExprTy::Incomplete, span: span(0, 6)});
	assert_expr!("{5, 1", Expr{ty: ExprTy::Incomplete, span: span(0, 5)});
	assert_expr!("int[5](1, 2", Expr{ty: ExprTy::Incomplete, span: span(0, 11)});
}
