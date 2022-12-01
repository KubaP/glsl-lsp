//! Types and functionality related to the parser.
//!
//! This module contains the structs and enums used to represent the AST, and the
//! [`parse_from_str()`]/[`parse_from_token_stream()`] functions that return a [`TokenTree`], which can be used to
//! parse the tokens into an abstract syntax tree ([`ParseResult`]). The [`ast`] submodule contains the AST types
//! themselves. There is also the [`SyntaxToken`] type used to represent syntax highlighting spans.

pub mod ast;
mod conditional_expression;
mod expression;
mod printing;
mod syntax;
#[cfg(test)]
mod walker_tests;

pub use syntax::*;

use crate::{
	diag::{
		ExprDiag, PreprocConditionalDiag, PreprocDefineDiag, PreprocExtDiag,
		PreprocLineDiag, PreprocVersionDiag, Semantic, StmtDiag, Syntax,
	},
	lexer::{
		preprocessor::{
			ExtensionToken, LineToken, TokenStream as PreprocStream,
			VersionToken,
		},
		OpTy, Token, TokenStream,
	},
	parser::conditional_expression::cond_parser,
	Either, GlslVersion, Span, Spanned,
};
use ast::*;
use expression::{expr_parser, Mode};
use std::collections::{HashMap, HashSet};

/// The result of a parsed GLSL source string.
///
/// - `0` - The abstract syntax tree. By nature of this tree being parsed after conditional compilation has been
///   applied, it will not contain any conditional compilation preprocessor directives.
/// - `1` - Any syntax diagnostics created during parsing.
/// - `2` - Any semantic diagnostics created during parsing, (this will only contain semantic diagnostics related
///   to macros and macro expansion).
/// - `3` - Syntax highlighting tokens.
pub type ParseResult = (
	Vec<Node>,
	Vec<Syntax>,
	Vec<Semantic>,
	Vec<Spanned<SyntaxToken>>,
);

/// An error type for the first step of the parsing operations.
#[derive(Debug)]
pub enum ParseErr {
	/// The token stream from the lexer is from an unsupported GLSL version.
	UnsupportedVersion(GlslVersion),
}

/// An error type for the second step of the parsing operations, (after conditional compilation has been applied).
#[derive(Debug)]
pub enum TreeParseErr {
	/// This number doesn't map to a conditional branch.
	InvalidNum(usize),
	/// This number has a dependent number that was not specified in the key.
	InvalidChain(usize),
	/// This tree contains no conditional compilation branches.
	NoConditionalBranches,
}

/// Parses a GLSL source string into a tree of tokens that can be then parsed into an abstract syntax tree.
///
/// This parser returns a [`TokenTree`] rather than the AST itself; this is required to support conditional
/// compilation. Because conditional compilation is enabled through the preprocessor, there are no rules as to
/// where the parser can branch - a conditional branch could be introduced in the middle of a variable declaration
/// for instance. This makes it effectively impossible to represent all branches of a source string within a single
/// AST without greatly overcomplicating the entire parser, multiple ASTs are needed to represent all the
/// conditional permutations.
///
/// The [`TokenTree`] struct allows you to pick which conditional compilation permutations to enable, and then
/// parse the source string with those conditions to produce a [`ParseResult`]. Each permutation of all possible
/// ASTs can be accessed with a key that describes which of the conditional options is selected. The example below
/// illustrates this:
/// ```c
///                         // Ordered by appearance    Ordered by nesting
///                         //  0 (root)
/// foo                     //  │                        
///                         //  │                        
/// #ifdef ...              //  │  1                     0-0
///     AAA                 //  │  │                     │
///                         //  │  │                     │
///         #ifdef ...      //  │  │  2                  │    0-0
///             50          //  │  │  │                  │    │
///         #else           //  │  │  3                  │    0-1
///             60          //  │  │  │                  │    │
///         #endif          //  │  │  ┴                  │    ┴
///                         //  │  │                     │
///     BBB                 //  │  │                     │
/// #elif ...               //  │  4                     0-1
///     CCC                 //  │  │                     │
/// #else                   //  │  5                     0-2
///     DDD                 //  │  │                     │
/// #endif                  //  │  ┴                     ┴
///                         //  │                        
/// #ifdef ...              //  │  6                     1-0
///     EEE                 //  │  │                     │
///                         //  │  │                     │
///         #ifdef ...      //  │  │  7                  │    0-0
///             100         //  │  │  │                  │    │
///         #endif          //  │  │  ┴                  │    ┴
/// #endif                  //  │  ┴                     ┴
///                         //  │                        
/// bar                     //  │                        
///                         //  ┴                        
/// ```
/// There is always a root token stream which has no conditional branches enabled. This can be accessed through the
/// [`root()`](TokenTree::root) method. There are two ways of controlling which conditions are enabled, by order of
/// appearance or by order of nesting.
///
/// ## Order by appearance
/// Each encountered condition (an `ifdef`/`ifndef`/`if`/`elif`/`else` directive) is given an incrementing number.
/// You pass a slice of numbers that denote which conditions to enable into the
/// [`parse_by_order_of_appearance()`](TokenTree::parse_by_order_of_appearance) method.
///
/// Some examples to visualise:
/// - `[1, 3]` will produce: `foo AAA 60 BBB bar`.
/// - `[4]` will produce: `foo CCC bar`.
/// - `[6, 7]` will produce: `foo EEE 100 bar`.
/// - `[1, 2, 6, 7]` will produce: `foo AAA 50 BBB EEE 100 bar`.
///
/// ## Order by nesting (Not implemented yet)
/// Each encountered group of conditions (an `ifdef`/`ifndef`/`if` - `elif`/`else` - `endif`) creates a newly
/// nested group. Within each group the individual conditions are numbered by order of appearance from 0. You pass
/// slices of numbers that denote which conditions to enable into the
/// [`parse_by_order_of_nesting()`](TokenTree::parse_by_order_of_nesting) method.
///
/// Some examples to visualise:
/// - `[[0-0, 0-1]]` will produce: `foo AAA 60 BBB bar`.
/// - `[[0-1]]` will produce: `foo CCC bar`.
/// - `[[1-0, 0-0]]` will produce: `foo EEE 100 bar`.
/// - `[[0-0, 0-0], [1-0, 0-0]]` will produce: `foo AAA 50 BBB EEE 100 bar`.
///
/// ## Invalid permutations
/// If you pass a key which doesn't form a valid permutation, the parsing functions will return an error.
///
/// # Examples
/// Parse a simple GLSL expression:
/// ```rust
/// # use glast::parser::parse_from_str;
/// let src = r#"
/// ##version 450 core
/// int i = 5.0 + 1;
/// "#;
/// let trees = parse_from_str(&src).unwrap();
/// let (ast, _, _, _) = trees.root(false); // We don't care about extra
///                                         // syntax highlighting information
/// ```
///
/// # Further reading
/// See the documentation of the [`TokenTree`] struct for a more in-depth explanation about why this seemingly
/// roundabout method is necessary.
pub fn parse_from_str(source: &str) -> Result<TokenTree, ParseErr> {
	let (token_stream, metadata) = crate::lexer::parse_from_str(source);
	parse_from_token_stream(token_stream, metadata)
}

/// Parses a token stream into a tree of tokens that can be then parsed into an abstract syntax tree.
///
/// For an explanation of how this function works, see the documentation for the [`parse_from_str()`] function.
pub fn parse_from_token_stream(
	mut token_stream: TokenStream,
	metadata: crate::lexer::Metadata,
) -> Result<TokenTree, ParseErr> {
	// Check the GLSL version as detected by the lexer.
	if metadata.version == GlslVersion::Unsupported && !token_stream.is_empty()
	{
		return Err(ParseErr::UnsupportedVersion(metadata.version));
	}

	// Skip tree generation if there are no conditional compilation blocks, or if the token stream is empty.
	if !metadata.contains_conditional_compilation || token_stream.is_empty() {
		let span = if !token_stream.is_empty() {
			Span::new(
				token_stream.first().unwrap().1.start,
				token_stream.last().unwrap().1.end,
			)
		} else {
			Span::new(0, 0)
		};
		return Ok(TokenTree {
			arena: vec![token_stream],
			tree: vec![TreeNode {
				parent: None,
				children: vec![Either::Left(0)],
				span,
			}],
			order_by_appearance: vec![],
			syntax_diags: vec![],
			contains_conditional_compilation: false,
		});
	}

	// Below is a simple arena-based tree structure. Here is an example of how the source would be represented in
	// the tree:
	//
	// foo
	// #ifdef T
	//   AAA
	//     #ifdef Z
	//       90
	//
	//     #endif
	//   BBB
	// #else
	//   EEE
	// #endif
	// bar
	// baz
	//
	// Tree representation:
	//
	// Node(                                   0
	//     Tokens[foo],                        |
	//     Conditional{                        |
	//         if: Node(                       |  1
	//             Tokens[AAA],                |  |
	//             Conditional{                |  |
	//                 if: Node(               |  |  2
	//                     Tokens[90],         |  |  |
	//                 ),                      |  |  |
	//             },                          |  |
	//             Tokens[BBB],                |  |
	//         ),                              |  |
	//         else: Node(                     |  3
	//             Tokens[EEE],                |  |
	//         )                               |  |
	//     },                                  |
	//     Tokens[bar, baz],                   |
	// )
	//
	// order-by-appearance: [(0, [0]), (1, [0]), (2, [1, 0]), (3, [0])]

	let token_stream_end = token_stream.last().unwrap().1.end;

	let mut arena = Vec::new();
	let mut tree = vec![TreeNode {
		parent: None,
		children: Vec::new(),
		span: Span::new(0, 0),
	}];
	// A vector which creates a mapping between `order-of-appearance` -> `(node ID, parent IDs)`. The parent node
	// IDs are tracked so that in the `parse_by_order_of_appearance()` method we can validate whether the key is
	// valid.
	let mut order_by_appearance = vec![(0, vec![0])];
	let mut syntax_diags = Vec::new();

	// The current grouping of tokens. This is pushed into the arena whenever we encounter a branch that creates a
	// new tree node.
	let mut current_tokens = Vec::with_capacity(100);
	// The stack representing the IDs of currently nested nodes. The first ID always refers to the root node.
	// Invariant: Any time this is `pop()`ed a length check is made to ensure that `[0]` is always valid.
	let mut stack: Vec<NodeId> = vec![0];

	fn top(stack: &[NodeId]) -> NodeId {
		*stack.last().unwrap()
	}

	// We consume all of the tokens from the beginning.
	loop {
		let (token, token_span) = if !token_stream.is_empty() {
			token_stream.remove(0)
		} else {
			break;
		};

		use crate::lexer::preprocessor::ConditionToken;

		match token {
			Token::Directive(d) => match d {
				PreprocStream::IfDef { kw, mut tokens } => {
					let mut syntax_tokens = vec![
						(SyntaxToken::Directive, token_span.first_char()),
						(SyntaxToken::Directive, kw),
					];

					// We are expecting an identifier as the first token.
					let ident = if tokens.is_empty() {
						syntax_diags.push(Syntax::PreprocConditional(
							PreprocConditionalDiag::ExpectedNameAfterIfDef(
								kw.next_single_width(),
							),
						));
						None
					} else {
						let (token, span) = tokens.remove(0);
						match token {
							ConditionToken::Ident(str) => {
								syntax_tokens.push((SyntaxToken::Ident, span));
								Some(Ident { name: str, span })
							}
							_ => {
								syntax_diags.push(Syntax::PreprocConditional(
									PreprocConditionalDiag::ExpectedNameAfterIfDef(
										span.next_single_width(),
									),
								));
								None
							}
						}
					};

					// Check for any trailing tokens.
					if !tokens.is_empty() {
						let start = tokens.first().unwrap().1.start;
						let end = tokens.last().unwrap().1.end;
						syntax_diags.push(Syntax::PreprocTrailingTokens(
							Span::new(start, end),
						));
						for (_, span) in tokens {
							syntax_tokens.push((SyntaxToken::Invalid, span));
						}
					}

					// Finish the current token group.
					let idx = arena.len();
					arena.push(std::mem::take(&mut current_tokens));
					tree.get_mut(top(&stack))
						.unwrap()
						.children
						.push(Either::Left(idx));

					// Create a new condition block, and a new node for the `ifdef` condition.
					let idx = tree.len();
					tree.push(TreeNode {
						parent: Some(top(&stack)),
						children: Vec::new(),
						span: token_span,
					});
					tree.get_mut(top(&stack)).unwrap().children.push(
						Either::Right(ConditionBlock {
							conditions: vec![(
								Conditional {
									span: token_span,
									ty: ConditionalTy::IfDef { ident },
								},
								idx,
								syntax_tokens,
							)],
							end: None,
						}),
					);
					order_by_appearance.push((idx, stack.clone()));
					stack.push(idx);
				}
				PreprocStream::IfNotDef { kw, mut tokens } => {
					let mut syntax_tokens = vec![
						(SyntaxToken::Directive, token_span.first_char()),
						(SyntaxToken::Directive, kw),
					];

					// We are expecting an identifier as the first token.
					let ident = if tokens.is_empty() {
						syntax_diags.push(Syntax::PreprocConditional(
							PreprocConditionalDiag::ExpectedNameAfterIfNotDef(
								kw.next_single_width(),
							),
						));
						None
					} else {
						let (token, span) = tokens.remove(0);
						match token {
							ConditionToken::Ident(str) => {
								syntax_tokens.push((SyntaxToken::Ident, span));
								Some(Ident { name: str, span })
							}
							_ => {
								syntax_diags.push(Syntax::PreprocConditional(
									PreprocConditionalDiag::ExpectedNameAfterIfNotDef(
										span.next_single_width(),
									),
								));
								None
							}
						}
					};

					// Check for any trailing tokens.
					if !tokens.is_empty() {
						let start = tokens.first().unwrap().1.start;
						let end = tokens.last().unwrap().1.end;
						syntax_diags.push(Syntax::PreprocTrailingTokens(
							Span::new(start, end),
						));
						for (_, span) in tokens {
							syntax_tokens.push((SyntaxToken::Invalid, span));
						}
					}

					// Finish the current token group.
					let idx = arena.len();
					arena.push(std::mem::take(&mut current_tokens));
					tree.get_mut(top(&stack))
						.unwrap()
						.children
						.push(Either::Left(idx));

					// Create a new condition block, and a new node for the `ifdef` condition.
					let idx = tree.len();
					tree.push(TreeNode {
						parent: Some(top(&stack)),
						children: Vec::new(),
						span: token_span,
					});
					tree.get_mut(top(&stack)).unwrap().children.push(
						Either::Right(ConditionBlock {
							conditions: vec![(
								Conditional {
									span: token_span,
									ty: ConditionalTy::IfNotDef { ident },
								},
								idx,
								syntax_tokens,
							)],
							end: None,
						}),
					);
					order_by_appearance.push((idx, stack.clone()));
					stack.push(idx);
				}
				PreprocStream::If { kw, tokens } => {
					let mut syntax_tokens = vec![
						(SyntaxToken::Directive, token_span.first_char()),
						(SyntaxToken::Directive, kw),
					];

					// We are expecting an identifier as the first token.
					let expr = if tokens.is_empty() {
						syntax_diags.push(Syntax::PreprocConditional(
							PreprocConditionalDiag::ExpectedExprAfterIf(
								kw.next_single_width(),
							),
						));
						None
					} else {
						let (expr, mut syntax, mut colours) =
							cond_parser(tokens);
						syntax_diags.append(&mut syntax);
						syntax_tokens.append(&mut colours);
						expr
					};

					// Finish the current token group.
					let idx = arena.len();
					arena.push(std::mem::take(&mut current_tokens));
					tree.get_mut(top(&stack))
						.unwrap()
						.children
						.push(Either::Left(idx));

					// Create a new condition block, and a new node for the `ifdef` condition.
					let idx = tree.len();
					tree.push(TreeNode {
						parent: Some(top(&stack)),
						children: Vec::new(),
						span: token_span,
					});
					tree.get_mut(top(&stack)).unwrap().children.push(
						Either::Right(ConditionBlock {
							conditions: vec![(
								Conditional {
									span: token_span,
									ty: ConditionalTy::If { expr },
								},
								idx,
								syntax_tokens,
							)],
							end: None,
						}),
					);
					order_by_appearance.push((idx, stack.clone()));
					stack.push(idx);
				}
				PreprocStream::ElseIf { kw, tokens } => {
					let mut syntax_tokens = vec![
						(SyntaxToken::Directive, token_span.first_char()),
						(SyntaxToken::Directive, kw),
					];

					// We are expecting an identifier as the first token.
					let expr = if tokens.is_empty() {
						syntax_diags.push(Syntax::PreprocConditional(
							PreprocConditionalDiag::ExpectedExprAfterIf(
								kw.next_single_width(),
							),
						));
						None
					} else {
						let (expr, mut syntax, mut colours) =
							cond_parser(tokens);
						syntax_diags.append(&mut syntax);
						syntax_tokens.append(&mut colours);
						expr
					};

					if stack.len() > 1 {
						// Finish the current token group for the previous conditional node.
						let idx = arena.len();
						arena.push(std::mem::take(&mut current_tokens));
						tree.get_mut(top(&stack))
							.unwrap()
							.children
							.push(Either::Left(idx));
						stack.pop();

						// By popping the stack, we are now pointing to the parent node that is the conditional
						// block.

						// Create a new node for the `elif` condition.
						let idx = tree.len();
						tree.push(TreeNode {
							parent: Some(top(&stack)),
							children: Vec::new(),
							span: token_span,
						});
						let node = tree.get_mut(top(&stack)).unwrap();
						node.span.end = token_span.end;
						let Either::Right(cond_block) = node.children.last_mut().unwrap() else { unreachable!() };
						cond_block.conditions.push((
							Conditional {
								span: token_span,
								ty: ConditionalTy::ElseIf { expr },
							},
							idx,
							syntax_tokens,
						));
						order_by_appearance.push((idx, stack.clone()));
						stack.push(idx);
					} else {
						syntax_diags.push(Syntax::PreprocConditional(
							PreprocConditionalDiag::UnmatchedElseIf(token_span),
						));
					}
				}
				PreprocStream::Else { kw, tokens } => {
					let mut syntax_tokens = vec![
						(SyntaxToken::Directive, token_span.first_char()),
						(SyntaxToken::Directive, kw),
					];

					// We are not expecting anything after `#else`.
					if !tokens.is_empty() {
						let span = Span::new(
							tokens.first().unwrap().1.start,
							tokens.last().unwrap().1.end,
						);
						syntax_diags.push(Syntax::PreprocTrailingTokens(span));
						syntax_tokens.push((SyntaxToken::Invalid, span));
					}

					if stack.len() > 1 {
						// Finish the current token group for the previous conditional node.
						let idx = arena.len();
						arena.push(std::mem::take(&mut current_tokens));
						tree.get_mut(top(&stack))
							.unwrap()
							.children
							.push(Either::Left(idx));
						stack.pop();

						// By popping the stack, we are now pointing to the parent node that is the conditional
						// block.

						// Create a new node for the `else` condition.
						let idx = tree.len();
						tree.push(TreeNode {
							parent: Some(top(&stack)),
							children: Vec::new(),
							span: token_span,
						});
						let node = tree.get_mut(top(&stack)).unwrap();
						node.span.end = token_span.end;
						let Either::Right(cond_block) = node.children.last_mut().unwrap() else { unreachable!() };
						cond_block.conditions.push((
							Conditional {
								span: token_span,
								ty: ConditionalTy::Else,
							},
							idx,
							syntax_tokens,
						));
						order_by_appearance.push((idx, stack.clone()));
						stack.push(idx);
					} else {
						syntax_diags.push(Syntax::PreprocConditional(
							PreprocConditionalDiag::UnmatchedElse(token_span),
						));
					}
				}
				PreprocStream::EndIf { kw, tokens } => {
					let mut syntax_tokens = vec![
						(SyntaxToken::Directive, token_span.first_char()),
						(SyntaxToken::Directive, kw),
					];

					// We are not expecting anything after `#endif`.
					if !tokens.is_empty() {
						let span = Span::new(
							tokens.first().unwrap().1.start,
							tokens.last().unwrap().1.end,
						);
						syntax_diags.push(Syntax::PreprocTrailingTokens(span));
						syntax_tokens.push((SyntaxToken::Invalid, span));
					}

					if stack.len() > 1 {
						let node = tree.get_mut(top(&stack)).unwrap();
						node.span.end = token_span.end;
						// Finish the current token group for the previous conditional node.
						let idx = arena.len();
						arena.push(std::mem::take(&mut current_tokens));
						tree.get_mut(top(&stack))
							.unwrap()
							.children
							.push(Either::Left(idx));
						stack.pop();

						// By popping the stack, we are now pointing to the parent node that is the conditional
						// block.

						// Close the condition block.
						let node = tree.get_mut(top(&stack)).unwrap();
						node.span.end = token_span.end;
						let Either::Right(cond_block) = node.children.last_mut().unwrap() else { unreachable!() };
						cond_block.end = Some((
							Conditional {
								span: token_span,
								ty: ConditionalTy::End,
							},
							syntax_tokens,
						));
					} else {
						syntax_diags.push(Syntax::PreprocConditional(
							PreprocConditionalDiag::UnmatchedEndIf(token_span),
						));
					}
				}
				_ => {
					let node = tree.get_mut(top(&stack)).unwrap();
					node.span.end = token_span.end;
					current_tokens.push((Token::Directive(d), token_span));
				}
			},
			_ => {
				let node = tree.get_mut(top(&stack)).unwrap();
				node.span.end = token_span.end;
				current_tokens.push((token, token_span));
			}
		}
	}

	// Finish the current group of remaining tokens.
	if !current_tokens.is_empty() {
		let idx = arena.len();
		arena.push(std::mem::take(&mut current_tokens));
		tree.get_mut(top(&stack))
			.unwrap()
			.children
			.push(Either::Left(idx));
	}
	stack.pop();

	// If we still have nodes on the stack, that means we have one or more unclosed condition blocks.
	if stack.len() > 0 {
		let node = tree.get_mut(top(&stack)).unwrap();
		node.span.end = token_stream_end;
		let Either::Right(cond) = node.children.last_mut().unwrap() else { unreachable!(); };
		let if_span = cond.conditions[0].0.span;
		syntax_diags.push(Syntax::PreprocConditional(
			PreprocConditionalDiag::UnclosedBlock(
				if_span,
				Span::new(token_stream_end, token_stream_end),
			),
		));
	}

	//dbg!(&arena);
	//dbg!(&tree);
	//dbg!(&syntax_diags);
	Ok(TokenTree {
		arena,
		tree,
		order_by_appearance,
		syntax_diags,
		contains_conditional_compilation: true,
	})
}

/// Pretty-prints the AST.
///
/// The output is not stable and can be changed at any time, so the specific formatting should not be relied upon.
///
/// # Examples
/// Print a simple GLSL expression:
/// ```rust
/// # use glast::parser::{parse_from_str, print_ast};
/// let src = r#"
/// ##version 450 core
/// int i = 5.0 + 1;
/// "#;
/// let (ast, _, _, _) = parse_from_str(&src).unwrap().root(false);
/// println!("{}", print_ast(ast));
/// ```
/// Would result in:
/// ```text
/// #Version(
///     version: 450
///     profile: core
/// ),
/// VarDef(
///     type: int
///     ident: i
///     value: BinOp(
///         op: +
///         left: 5.0
///         right: 1
///     )
/// )
/// ```
pub fn print_ast(ast: Vec<Node>) -> String {
	printing::print_ast(ast)
}

/// A tree of token streams generated from a GLSL source string.
///
/// The tree represents all possible conditional compilation branches. Call the
/// [`parse_by_order_of_appearance()`](Self::parse_by_order_of_appearance) or
/// [`parse_by_order_of_nesting()`](Self::parse_by_order_of_nesting) methods to parse a tree with the selected
/// conditional branches into a [`ParseResult`].
///
/// # Examples
/// For a fully detailed example on how to use this struct to create an abstract syntax tree, see the documentation
/// for the [`parse_from_str()`] function.
///
/// # Why is this necessary?
/// Conditional compilation is implemented through the preprocessor, which sets no rules as to where conditional
/// branching can take place, (apart from the fact that a preprocessor directive must exist on its own line). This
/// means that a conditional branch could, for example, completely change the entire signature of a program:
/// ```c
///  1│ void foo() {
///  2│
///  3│     int i = 5;
///  4│
///  5│     #ifdef TOGGLE
///  6│     }
///  7│     void bar() {
///  8│     #endif
///  9│
/// 10│     int p = 0;
/// 11│ }
/// ```
/// In the example above, if `TOGGLE` is not defined, we have a function `foo` who's scope ends on line `11` and
/// includes two variable definitions `i` and `p`. However, if `TOGGLE` is defined, the function `foo` ends on
/// line `6` instead and only contains the variable `i`, and we have a completely new function `bar` which has the
/// variable `p`.
///
/// This technically can be representable in the AST, it's just that it would look something like this:
/// ```text
/// Root(
///     Either(
///         (
///             Function(
///                 name="foo"
///                 start=1
///                 end=11
///                 contents(
///                     Variable(name="i" value=5)
///                     Variable(name="p" value=0)
///                 )
///             )
///         ),
///         (
///             Function(
///                 name="foo"
///                 start=1
///                 end=6
///                 contents(
///                     Variable(name="i" value=5)
///                 )
///             ),
///             Function(
///                 name="bar"
///                 start=7
///                 end=11
///                 contents(
///                     Variable(name="p" value=0)
///                 )
///             ),
///         )
///     )
/// )
/// ```
/// Notice how this AST is effectively `Either(AST_with_condition_false, AST_with_condition_true)`. This is because
/// the function `foo` could potentially be split in the middle, but an AST node cannot have multiple end points,
/// which means that we can't include both permutations in the function node; we need separate function nodes
/// instead. And since we have two separate possibilities for `foo`, we need to branch in the node above `foo`,
/// which in this example is effectively the root node.
///
/// It is arguable whether such a representation would be better than the current solution. On one hand all
/// possibilities are within the single AST, but on the other hand such an AST would quickly become confusing to
/// work with, manipulate, analyse, etc.
///
/// The main reason this option wasn't chosen is because it would immensely complicate the parsing logic, and in
/// turn the maintainability of this project. As with all recursive-descent parsers, the individual parsing
/// functions hold onto any temporary state. In this example, the function for parsing functions holds information
/// such as the name, the starting position, the parameters, etc. If we would encounter the conditional branching
/// within this parsing function, we would somehow need to be able to return up the call stack to split the parser,
/// whilst also somehow not loosing the temporary state. This should be technically possible, but it would greatly
/// complicate the parser and make writing the parsing logic itself an absolutely awful experience, and that is not
/// a trade-off I'm willing to take.
///
/// This complication occurs because the preprocessor is a separate pass ran before the main compiler and does not
/// follow the GLSL grammar rules, which means that preprocessor directives and macros can be included literally
/// anywhere and the file may still be valid after expansion. In comparison, some newer languages include
/// conditional compilation as part of the language grammar itself. In Rust for example, conditional compilation is
/// applied via attributes to entire expressions/statements, which means that you can't run into this mess where a
/// conditional branch splits a function mid-way through parsing. GLSL unfortunately uses the C preprocessor, which
/// results in this sort of stuff (the approach taken by this crate) being necessary to achieve 100%
/// specification-defined behaviour.
pub struct TokenTree {
	/// The arena of token streams.
	///
	/// # Invariants
	/// If `contains_conditional_compilation` is `false`, this is:
	/// ```ignore
	/// vec![enitire_token_stream]
	/// ```
	arena: Vec<TokenStream>,
	/// The tree.
	///
	/// # Invariants
	/// If `contains_conditional_compilation` is `false`, this is:
	/// ```ignore
	/// vec![TreeNode {
	///     parent: None,
	///     children: vec![Either::Left(0)]
	/// }]
	/// ```
	tree: Vec<TreeNode>,
	/// IDs of the relevant nodes ordered by appearance.
	///
	/// - `0` - The ID of the `[n]`th conditional node.
	/// - `1` - The IDs of the nodes which this conditional node depends on.
	///
	/// # Invariants
	/// If `contains_conditional_compilation` is `false`, this is empty.
	order_by_appearance: Vec<(NodeId, Vec<NodeId>)>,

	/// Syntax diagnostics related to conditional compilation directives.
	///
	/// # Invariants
	/// If `contains_conditional_compilation` is `false`, this is empty.
	#[allow(unused)]
	syntax_diags: Vec<Syntax>,

	/// Whether there are any conditional compilation branches.
	contains_conditional_compilation: bool,
}

impl TokenTree {
	/// Parses the root token stream.
	///
	/// Whilst this is guaranteed to succeed, if the entire source string is wrapped within a conditional block
	/// this will return an empty AST.
	///
	/// # Syntax highlighting
	/// The `syntax_highlight_entire_file` parameter controls whether to produce syntax tokens for the entire file,
	/// not just for the root tokens. This involves parsing all conditional blocks in order to produce the syntax
	/// highlighting information. Whilst this functionality uses the smallest possible number of permutations that
	/// cover the entire file, if there are a lot of conditional blocks that can mean the source string gets parsed
	/// many times, which may have performance implications.
	///
	/// The actual syntax highlighting results are based off the chosen permutations which cannot be controlled. If
	/// you require more control, you must manually parse the relevant permutations and collect the tokens
	/// yourself.
	///
	/// If there are no conditional blocks, this parameter does nothing.
	///
	/// # Examples
	/// For a fully detailed example on how to use this method to create an abstract syntax tree, see the
	/// documentation for the [`parse_from_str()`] function.
	pub fn root(&self, syntax_highlight_entire_file: bool) -> ParseResult {
		// Get the relevant streams for the root branch.
		let streams = if !self.contains_conditional_compilation {
			vec![self.arena.get(0).unwrap().clone()]
		} else {
			let mut streams = Vec::new();
			let node = self.tree.get(0).unwrap();
			for child in &node.children {
				match child {
					Either::Left(idx) => {
						streams.push(self.arena.get(*idx).unwrap().clone())
					}
					Either::Right(_) => {}
				}
			}
			streams
		};

		// Parse the root branch.
		let mut walker = Walker::new(streams, vec![]);
		let mut nodes = Vec::new();
		while !walker.is_done() {
			parse_stmt(&mut walker, &mut nodes);
		}

		if syntax_highlight_entire_file && self.contains_conditional_compilation
		{
			let mut root_tokens = std::mem::take(&mut walker.syntax_tokens);
			let mut tokens = Vec::with_capacity(walker.syntax_tokens.len());

			// Each key points to the nodes which contain the tokens of the conditional branch. If we want
			// information about the conditional directive itself, we have to look at the parent.
			let keys = self
				.minimal_no_of_permutations_for_complete_syntax_highlighting();

			// Move over the root tokens before any conditional scope.
			let first_node = self.tree.get(keys[0][0]).unwrap();
			let span = Span::new(0, first_node.span.start);
			loop {
				let (_, s) = match root_tokens.get(0) {
					Some(t) => t,
					None => break,
				};

				if span.contains(*s) {
					tokens.push(root_tokens.remove(0));
				} else {
					break;
				}
			}

			// Deal with all tokens produced from conditional scopes, as well as root tokens in-between conditional
			// scopes, (if any).
			for (i, key) in keys.iter().enumerate() {
				let node = self.tree.get(key[0]).unwrap();

				let (_, _, _, mut new_tokens) =
					self.parse_node_ids_chronologically(key);
				loop {
					let (_, s) = match new_tokens.get(0) {
						Some(t) => t,
						None => break,
					};

					if s.is_before_pos(node.span.start) {
						new_tokens.remove(0);
						continue;
					}

					if node.span.contains(*s) {
						tokens.push(new_tokens.remove(0));
					} else {
						break;
					}
				}

				if let Some(next_key) = keys.get(i + 1) {
					let next_node = self.tree.get(next_key[0]).unwrap();
					let span = Span::new(node.span.end, next_node.span.start);
					if !span.is_zero_width() {
						// We have another conditional block after this one; there may be root tokens in-between
						// these two blocks.
						loop {
							let (_, s) = match root_tokens.get(0) {
								Some(t) => t,
								None => break,
							};

							if span.contains(*s) {
								tokens.push(root_tokens.remove(0));
							} else {
								break;
							}
						}
					}
				}
			}

			// Append any remaining root tokens.
			tokens.append(&mut root_tokens);

			(nodes, walker.syntax_diags, walker.semantic_diags, tokens)
		} else {
			(
				nodes,
				walker.syntax_diags,
				walker.semantic_diags,
				walker.syntax_tokens,
			)
		}
	}

	/// Parses a token tree by enabling conditional branches in the order of their appearance.
	///
	/// This method can return an `Err` in the following cases:
	/// - The `key` has a number which doesn't map to a conditional compilation branch.
	/// - The `key` has a number which depends on another number that is missing.
	///
	/// # Examples
	/// For a fully detailed example on how to use this method to create an abstract syntax tree, see the
	/// documentation for the [`parse_from_str()`] function.
	pub fn parse_by_order_of_appearance(
		&self,
		key: impl AsRef<[usize]>,
	) -> Result<ParseResult, TreeParseErr> {
		let key = key.as_ref();

		if !self.contains_conditional_compilation {
			return Err(TreeParseErr::NoConditionalBranches);
		}

		let mut nodes = Vec::with_capacity(key.len());
		// Check that the key is valid.
		{
			let mut visited_node_ids = vec![0];
			for num in key {
				let (id, parent_id) = match self.order_by_appearance.get(*num) {
					Some(t) => t,
					None => return Err(TreeParseErr::InvalidNum(*num)),
				};

				if !visited_node_ids.contains(parent_id.first().unwrap()) {
					return Err(TreeParseErr::InvalidChain(*num));
				}

				visited_node_ids.push(*id);
				nodes.push(*id);
			}
		}

		Ok(self.parse_node_ids_chronologically(&nodes))
	}

	/// TODO: Implement.
	#[allow(unused)]
	pub fn parse_by_order_of_nesting(
		&self,
		key: impl AsRef<[(usize, usize)]>,
	) -> Option<ParseResult> {
		todo!()
	}

	/// Parses the specified nodes.
	///
	/// # Invariants
	/// At least one node needs to be specified.
	///
	/// The IDs of the nodes-to-parse should be in a chronological order.
	///
	/// The IDs should map to a valid permutation of conditional blocks.
	fn parse_node_ids_chronologically(&self, nodes: &[NodeId]) -> ParseResult {
		if nodes.is_empty() {
			panic!("Expected at least one node to evaluate");
		}

		let mut nodes_idx = 0;
		let mut streams = Vec::new();
		let mut conditional_syntax_tokens = Vec::new();
		let mut end_tokens_stack = Vec::new();
		let mut node_stack = vec![(0, 0)];
		// Invariant: We have at least one node, so at least one iteration of this loop can be performed without
		// any panics.
		'outer: loop {
			let (node_id, child_idx) = node_stack.last_mut().unwrap();
			let node = &self.tree[*node_id];

			// Consume the next content element in this node.
			while let Some(child) = node.children.get(*child_idx) {
				*child_idx += 1;
				match child {
					Either::Left(arena_id) => {
						streams.push(self.arena[*arena_id].clone())
					}
					Either::Right(ConditionBlock { conditions, end }) => {
						// Check if any of the conditional branches match the current key number.
						for (_, node_id, tokens) in conditions {
							if *node_id == nodes[nodes_idx] {
								conditional_syntax_tokens.push(tokens.clone());
								node_stack.push((*node_id, 0));
								nodes_idx += 1;
								if let Some((_, tokens)) = end {
									end_tokens_stack.push(tokens.clone());
								}
								continue 'outer;
							}
						}
					}
				}
			}

			// We have consumed all the content of this node which means we can pop it from the stack and continue
			// with the parent node, (if there is one).
			if node_stack.len() > 1 {
				node_stack.pop();
				conditional_syntax_tokens.push(end_tokens_stack.pop().unwrap());
			} else {
				break 'outer;
			}
		}

		let mut walker = Walker::new(streams, conditional_syntax_tokens);
		let mut nodes = Vec::new();
		while !walker.is_done() {
			parse_stmt(&mut walker, &mut nodes);
		}

		(
			nodes,
			walker.syntax_diags,
			walker.semantic_diags,
			walker.syntax_tokens,
		)
	}

	/// Returns all of the (by-order-of-appearance) keys (**of node IDs, not order-of-appearance numbers**)
	/// required to fully syntax highlight the entire source string.
	fn minimal_no_of_permutations_for_complete_syntax_highlighting(
		&self,
	) -> Vec<Vec<NodeId>> {
		let mut chains_of_nodes = Vec::new();
		for (id, required_ids) in self.order_by_appearance.iter().skip(1) {
			let mut new_chain = required_ids[1..].to_vec();
			new_chain.push(*id);

			// We may have a chain of nodes which fully fits within this new chain. For example, we could have a
			// chain `[0, 4]`, and the new chain we have is `[0, 4, 5]`. In this case, the existing chain is wholly
			// unnecessary because all of the lines of code in that chain will be covered in this new chain, (plus
			// the lines of code in the new `5` branch). Since we are trying to find the minimal number of
			// permutations to cover the whole file, we can discard the existing chain.

			// See if any existing chains are contained within the new one.
			let idx = chains_of_nodes
				.iter()
				.position(|v: &Vec<usize>| new_chain.starts_with(v.as_ref()));

			if let Some(idx) = idx {
				// `idx` points to an existing chain of nodes that is part of the new chain of nodes being added
				// right now. That means the existing chain can be removed because this new chain will cover 100%
				// of the old chain.
				chains_of_nodes.remove(idx);
			}

			chains_of_nodes.push(new_chain);
		}
		chains_of_nodes
	}

	/// Returns whether the source string contains any conditional compilation branches.
	pub fn contains_conditional_compilation(&self) -> bool {
		self.contains_conditional_compilation
	}
}

type NodeId = usize;
type ArenaId = usize;

/// A node within the token tree.
#[derive(Debug)]
struct TreeNode {
	/// The parent of this node.
	#[allow(unused)]
	parent: Option<NodeId>,
	/// The children/contents of this node. Each entry either points to a token stream (in the arena), or is a
	/// condition block which points to child nodes.
	children: Vec<Either<ArenaId, ConditionBlock>>,
	span: Span,
}

#[derive(Debug)]
struct ConditionBlock {
	/// The individual condition blocks.
	///
	/// # Invariants
	/// The entry at `[0]` will be a `ConditionalTy::IfDef/IfNotDef/If` variant.
	///
	/// A `ConditionalTy::End` will never be present.
	conditions: Vec<(Conditional, NodeId, Vec<Spanned<SyntaxToken>>)>,
	/// The `#endif` directive.
	///
	/// This is separate because the `#endif` doesn't contain any children, (since it ends the condition block),
	/// hence a `NodeId` would be incorrect.
	///
	/// # Invariants
	/// This will be a `ConditionalTy::End` variant.
	end: Option<(Conditional, Vec<Spanned<SyntaxToken>>)>,
}

/// Information necessary to expand a macro.
#[derive(Debug, Clone)]
enum Macro {
	Object(TokenStream),
	Function {
		params: Vec<Ident>,
		body: TokenStream,
	},
}

/// Allows for stepping through a token stream. Takes care of dealing with irrelevant details from the perspective
/// of the parser, such as comments and macro expansion.
pub(crate) struct Walker {
	/// The token streams of the source string with the preselected conditional branches.
	source_streams: Vec<TokenStream>,
	/// The active token streams.
	///
	/// - `0` - The macro identifier, (for the root source stream this is just `""`).
	/// - `1` - The token stream.
	/// - `2` - The cursor.
	streams: Vec<(String, TokenStream, usize)>,

	/// The currently defined macros.
	///
	/// Key: The macro identifier.
	///
	/// Value:
	/// - `0` - The span of the macro signature.
	/// - `1` - Macro information.
	macros: HashMap<String, (Span, Macro)>,
	/// The span of an initial macro call site. Only the first macro call site is registered here.
	macro_call_site: Option<Span>,
	/// The actively-called macro identifiers.
	active_macros: HashSet<String>,

	/// Any syntax diagnostics created from the tokens parsed so-far.
	syntax_diags: Vec<Syntax>,
	/// Any semantic diagnostics created from the tokens parsed so-far.
	semantic_diags: Vec<Semantic>,

	/// The syntax highlighting tokens created from the tokens parsed so-far.
	syntax_tokens: Vec<Spanned<SyntaxToken>>,
	/// The syntax highlighting tokens for any conditional directives.
	///
	/// - `0` - The span of the entire directive.
	/// - `1` - The syntax tokens.
	conditional_syntax_tokens: Vec<(Span, Vec<Spanned<SyntaxToken>>)>,

	/// The last span in the source string.
	last_span: Span,
}

#[allow(unused)]
impl Walker {
	/// Constructs a new walker.
	fn new(
		mut token_streams: Vec<TokenStream>,
		conditional_syntax_tokens: Vec<Vec<Spanned<SyntaxToken>>>,
	) -> Self {
		let mut last_span = Span::new(0, 0);
		for stream in token_streams.iter().rev() {
			match stream.last() {
				Some((_, span)) => {
					last_span = *span;
					break;
				}
				None => continue,
			}
		}

		// Deal with the possibility of having one or more streams that are all completely empty.
		// Note: We don't have to deal with the possibility of the first token being a macro call site because a
		// macro needs to be defined before it can be expanded.
		let mut token_streams: Vec<_> = token_streams
			.into_iter()
			.filter(|s| !s.is_empty())
			.collect();
		let streams = if !token_streams.is_empty() {
			vec![("".into(), token_streams.remove(0), 0)]
		} else {
			vec![]
		};

		let mut active_macros = HashSet::new();
		// Invariant: A macro cannot have no name (an empty identifier), so this won't cause any hashing clashes
		// with valid macros. By using "" we can avoid having a special case for the root source stream.
		active_macros.insert("".into());

		Self {
			source_streams: token_streams,
			streams,
			macros: HashMap::new(),
			macro_call_site: None,
			active_macros,
			syntax_diags: Vec::new(),
			semantic_diags: Vec::new(),
			syntax_tokens: Vec::new(),
			conditional_syntax_tokens: conditional_syntax_tokens
				.into_iter()
				.filter_map(|v| {
					if !v.is_empty() {
						Some((
							Span::new(
								v.first().unwrap().1.start,
								v.last().unwrap().1.end,
							),
							v,
						))
					} else {
						None
					}
				})
				.collect(),
			last_span,
		}
	}

	/// Returns a reference to the current token under the cursor, without advancing the cursor.
	fn peek(&self) -> Option<Spanned<&Token>> {
		if self.streams.is_empty() {
			None
		} else if self.streams.len() == 1 {
			let (_, stream, cursor) = self.streams.last().unwrap();
			stream.get(*cursor).map(|(t, s)| (t, *s))
		} else {
			let (_, stream, cursor) = self.streams.last().unwrap();
			match stream.get(*cursor).map(|(t, _)| t) {
				Some(token) => Some((
					token,
					// Panic: This is guaranteed to be some if `self.streams.len() > 1`.
					self.macro_call_site.unwrap(),
				)),
				None => None,
			}
		}
	}

	/// Returns the current token under the cursor, without advancing the cursor. (The token gets cloned).
	fn get(&self) -> Option<Spanned<Token>> {
		if self.streams.is_empty() {
			None
		} else if self.streams.len() == 1 {
			let (_, stream, cursor) = self.streams.last().unwrap();
			stream.get(*cursor).cloned()
		} else {
			let (_, stream, cursor) = self.streams.last().unwrap();
			let token = stream.get(*cursor).map(|(t, _)| t).cloned();
			token.map(|t| {
				(
					t,
					// Panic: This is guaranteed to be some if `self.streams.len() > 1`.
					self.macro_call_site.unwrap(),
				)
			})
		}
	}

	/// Peeks the next token without advancing the cursor.
	///
	/// **This method is expensive** to call because it needs to correctly deal with macros. Avoid calling this
	/// often.
	///
	/// This method correctly steps into/out-of macros, jumps between conditional compilation branches, and
	/// consumes any comments.
	fn lookahead_1(&self) -> Option<Spanned<Token>> {
		let mut source_streams = self.source_streams.clone();
		let mut streams = self.streams.clone();
		let mut macros = self.macros.clone();
		let mut active_macros = self.active_macros.clone();
		let mut macro_call_site = self.macro_call_site.clone();
		let mut syntax_diags = Vec::new();
		let mut semantic_diags = Vec::new();
		let mut syntax_tokens = Vec::new();
		// PERF: Optimize for certain cases to prevent having to clone everything everytime.
		Self::move_cursor(
			&mut source_streams,
			&mut streams,
			&mut macros,
			&mut active_macros,
			&mut macro_call_site,
			&mut syntax_diags,
			&mut semantic_diags,
			&mut syntax_tokens,
		);

		// Copy of `Self::get()`.
		if streams.is_empty() {
			None
		} else if streams.len() == 1 {
			let (_, stream, cursor) = streams.last().unwrap();
			stream.get(*cursor).cloned()
		} else {
			let (_, stream, cursor) = streams.last().unwrap();
			let token = stream.get(*cursor).map(|(t, _)| t).cloned();
			token.map(|t| {
				(
					t,
					// Panic: This is guaranteed to be some if `streams.len() > 1`.
					macro_call_site.unwrap(),
				)
			})
		}
	}

	/// Advances the cursor by one.
	///
	/// This method correctly steps into/out-of macros, jumps between conditional compilation branches, and
	/// consumes any comments.
	fn advance(&mut self) {
		Self::move_cursor(
			&mut self.source_streams,
			&mut self.streams,
			&mut self.macros,
			&mut self.active_macros,
			&mut self.macro_call_site,
			&mut self.syntax_diags,
			&mut self.semantic_diags,
			&mut self.syntax_tokens,
		);
	}

	/// Advances the cursor by one.
	///
	/// This method is identical to `advance()` apart from that diagnostics and syntax highlighting tokens are
	/// returned. This is necessary because otherwise the spans could be produced in the wrong order, if, for
	/// example, the walker consumes a comment but the expresion syntax tokens are appended after the fact.
	fn advance_expr_parser(
		&mut self,
		syntax_diags: &mut Vec<Syntax>,
		semantic_diags: &mut Vec<Semantic>,
		syntax_tokens: &mut Vec<Spanned<SyntaxToken>>,
	) {
		Self::move_cursor(
			&mut self.source_streams,
			&mut self.streams,
			&mut self.macros,
			&mut self.active_macros,
			&mut self.macro_call_site,
			syntax_diags,
			semantic_diags,
			syntax_tokens,
		);
	}

	/// Returns whether the walker has reached the end of the token streams.
	fn is_done(&self) -> bool {
		self.streams.is_empty()
	}

	/// Returns the span of the last token in the token stream.
	fn get_last_span(&self) -> Span {
		self.last_span
	}

	/// Moves the cursor to the next token. This function takes all the necessary data by parameter so that the
	/// functionality can be re-used between the `Self::advance()` and `Self::lookahead_1()` methods.
	fn move_cursor(
		source_streams: &mut Vec<TokenStream>,
		streams: &mut Vec<(String, TokenStream, usize)>,
		macros: &mut HashMap<String, (Span, Macro)>,
		active_macros: &mut HashSet<String>,
		macro_call_site: &mut Option<Span>,
		syntax_diags: &mut Vec<Syntax>,
		semantic_diags: &mut Vec<Semantic>,
		syntax_tokens: &mut Vec<Spanned<SyntaxToken>>,
	) {
		let mut dont_increment = false;
		'outer: while let Some((identifier, stream, cursor)) =
			streams.last_mut()
		{
			if !dont_increment {
				*cursor += 1;
			}
			dont_increment = false;

			if *cursor == stream.len() {
				// We have reached the end of this stream. We close it and re-run the loop on the next stream (if
				// there is one).

				let ident = identifier.clone();
				if streams.len() == 1 {
					// If we aren't in a macro, that means we've finished the current source stream but there may
					// be another one, (since they can be split up due to conditional compilation).
					if source_streams.is_empty() {
						// We have reached the final end.
						streams.remove(0);
						break;
					} else {
						let mut next_source = source_streams.remove(0);
						let (_, s, c) = streams.get_mut(0).unwrap();
						std::mem::swap(s, &mut next_source);
						*c = 0;
						dont_increment = true;
						continue;
					}
				} else {
					// Panic: Anytime a stream is added the identifier is inserted into the set.
					active_macros.remove(&ident);
					streams.remove(streams.len() - 1);
					continue;
				}
			}

			let (token, token_span) = stream.get(*cursor).unwrap();

			match token {
				// We check if the new token is a macro call site.
				Token::Ident(s) => {
					if let Some((signature_span, macro_)) = macros.get(s) {
						if active_macros.contains(s) {
							// We have already visited a macro with this identifier. Recursion is not supported so
							// we don't continue.
							break;
						}

						let ident_span = *token_span;

						if let Macro::Function { params, body } = macro_ {
							// We have an identifier which matches a function-like macro, so we are expecting a
							// parameter list in the current token stream before we do any switching.

							// We don't need to worry about having to switch source streams because that would
							// imply that a conditional compilation directive is in the middle of a function-like
							// macro call site, which isn't valid. A function-like macro call cannot have
							// preprocessor directives within, which means that the source stream won't be split up
							// by a conditional, which means the entire invocation of the macro will be within this
							// stream.

							let mut tmp_cursor = *cursor + 1;
							let mut syntax_spans =
								vec![(SyntaxToken::FunctionMacro, ident_span)];
							loop {
								match stream.get(tmp_cursor) {
									Some((token, token_span)) => match token {
										Token::LineComment(_)
										| Token::BlockComment { .. } => {
											syntax_spans.push((
												SyntaxToken::Comment,
												*token_span,
											));
											tmp_cursor += 1;
										}
										_ => break,
									},
									None => break 'outer,
								}
							}

							// Consume the opening `(` parenthesis.
							let l_paren_span = match stream.get(tmp_cursor) {
								Some((token, token_span)) => match token {
									Token::LParen => {
										syntax_spans.push((
											SyntaxToken::Punctuation,
											*token_span,
										));
										*cursor = tmp_cursor + 1;
										*token_span
									}
									_ => {
										// We did not immediately encounter a parenthesis, which means that this is
										// not a call to a function-like macro even if the names match.
										break;
									}
								},
								None => break,
							};

							// Look for any arguments until we hit a closing `)` parenthesis. The preprocessor
							// immediately switches to the next argument when a `,` is encountered, unless we are
							// within a parenthesis group.
							#[derive(PartialEq)]
							enum Prev {
								None,
								Param,
								Comma,
								Invalid,
							}
							let mut prev = Prev::None;
							let mut prev_span = l_paren_span;
							let mut paren_groups = 0;
							let mut args = Vec::new();
							let mut arg = Vec::new();
							let r_paren_span = loop {
								let (token, token_span) =
									match stream.get(*cursor) {
										Some(t) => t,
										None => {
											syntax_diags.push(Syntax::PreprocDefine(PreprocDefineDiag::ParamsExpectedRParen(
											prev_span.next_single_width()
										)));
											break 'outer;
										}
									};

								match token {
									Token::Comma => {
										syntax_spans.push((
											SyntaxToken::Punctuation,
											*token_span,
										));
										if paren_groups == 0 {
											let arg = std::mem::take(&mut arg);
											args.push(arg);
											prev = Prev::Comma;
										}
										prev_span = *token_span;
										*cursor += 1;
										continue;
									}
									Token::LParen => {
										paren_groups += 1;
									}
									Token::RParen => {
										if paren_groups == 0 {
											// We have reached the end of this function-like macro call site.
											syntax_spans.push((
												SyntaxToken::Punctuation,
												*token_span,
											));
											let arg = std::mem::take(&mut arg);
											args.push(arg);
											// It is important that we don't increment the cursor to the next token
											// after the macro call site. This is because once this macro is
											// finished, and we return to the previous stream, we will
											// automatically increment the cursor onto the next token which will be
											// the first token after the macro call site. The object-like macro
											// branch also doesn't perform this increment.
											// *cursor += 1;
											break *token_span;
										}
										paren_groups -= 1;
									}
									_ => {}
								}
								syntax_spans.push((
									token.non_semantic_colour(),
									*token_span,
								));
								arg.push((token.clone(), *token_span));
								*cursor += 1;
							};
							let call_site_span =
								Span::new(ident_span.start, r_paren_span.end);

							// We have a set of arguments now.
							if params.len() != args.len() {
								// If there is a mismatch in the argument/parameter count, we ignore this macro
								// call and move onto the next token after the call site.
								semantic_diags.push(
									Semantic::FunctionMacroMismatchedArgCount(
										call_site_span,
										*signature_span,
									),
								);
								continue;
							}
							let mut param_map = HashMap::new();
							params.iter().zip(args.into_iter()).for_each(
								|(ident, tokens)| {
									param_map.insert(&ident.name, tokens);
								},
							);

							// We now go through the replacement token list and replace any identifiers which match
							// a parameter name with the relevant argument's tokens.
							let mut new_body = Vec::with_capacity(body.len());
							for (token, token_span) in body {
								match token {
									Token::Ident(str) => {
										if let Some(arg) = param_map.get(&str) {
											for token in arg {
												new_body.push(token.clone());
											}
											continue;
										}
									}
									_ => {}
								}
								new_body.push((token.clone(), *token_span));
							}
							// Then, we perform token concatenation.
							let (new_body, mut diags) =
								crate::lexer::preprocessor::concat_macro_body(
									new_body,
								);
							syntax_diags.append(&mut diags);

							if body.is_empty() {
								// The macro is empty, so we want to move to the next token of the existing stream.
								semantic_diags.push(
									Semantic::EmptyMacroCallSite(
										call_site_span,
									),
								);
								if streams.len() == 1 {
									// We only syntax highlight when it is the first macro call.
									syntax_tokens.append(&mut syntax_spans);
								}
								continue;
							}

							let ident = s.to_owned();

							// We only syntax highlight and note the macro call site when it is the first macro
							// call.
							if streams.len() == 1 {
								*macro_call_site = Some(call_site_span);
								syntax_tokens.append(&mut syntax_spans);
							}

							active_macros.insert(ident.clone());
							streams.push((ident, new_body, 0));

							// The first token in the new stream could be another macro call, so we re-run the loop
							// on this new stream in case.
							dont_increment = true;
							continue;
						} else if let Macro::Object(stream) = macro_ {
							if stream.is_empty() {
								// The macro is empty, so we want to move to the next token of the existing stream.
								semantic_diags.push(
									Semantic::EmptyMacroCallSite(ident_span),
								);
								if streams.len() == 1 {
									// We only syntax highlight when it is the first macro call.
									syntax_tokens.push((
										SyntaxToken::ObjectMacro,
										ident_span,
									));
								}
								continue;
							}

							let ident = s.to_owned();

							// We only syntax highlight and note the macro call site when it is the first macro
							// call.
							if streams.len() == 1 {
								*macro_call_site = Some(ident_span);
								syntax_tokens.push((
									SyntaxToken::ObjectMacro,
									ident_span,
								));
							}

							active_macros.insert(ident.clone());
							streams.push((ident, stream.clone(), 0));

							// The first token in the new stream could be another macro call, so we re-run the loop
							// on this new stream in case.
							dont_increment = true;
							continue;
						}
					}
					break;
				}
				// We want to consume any comments since they are semantically ignored.
				Token::LineComment(_) => {
					let token_span = *token_span;
					if streams.len() == 1 {
						// We only syntax highlight when we are not in a macro call.
						syntax_tokens.push((SyntaxToken::Comment, token_span));
					}
				}
				Token::BlockComment { contains_eof, .. } => {
					if *contains_eof {
						syntax_diags.push(Syntax::BlockCommentMissingEnd(
							token_span.end_zero_width(),
						));
					}
					let token_span = *token_span;
					if streams.len() == 1 {
						// We only syntax highlight when we are not in a macro call.
						syntax_tokens.push((SyntaxToken::Comment, token_span));
					}
				}
				_ => break,
			}
		}

		if streams.len() <= 1 {
			*macro_call_site = None;
		}
	}

	/// Registers a define macro.
	fn register_macro(
		&mut self,
		ident: String,
		signature_span: Span,
		macro_: Macro,
	) {
		if let Some(_prev) = self.macros.insert(ident, (signature_span, macro_))
		{
			// TODO: Emit error if the macros aren't identical (will require scanning the tokenstream to compare).
		}
	}

	/// Un-registers a defined macro.
	fn unregister_macro(&mut self, ident: &str, span: Span) {
		match self.macros.remove(ident) {
			Some(_) => self.push_colour(span, SyntaxToken::ObjectMacro),
			None => {
				self.push_semantic_diag(Semantic::UndefMacroNameUnresolved(
					span,
				));
				self.push_colour(span, SyntaxToken::UnresolvedIdent);
			}
		}
	}

	/// Pushes a syntax diagnostic.
	fn push_syntax_diag(&mut self, diag: Syntax) {
		self.syntax_diags.push(diag);
	}

	/// Appends a collection of syntax diagnostics.
	fn append_syntax_diags(&mut self, syntax: &mut Vec<Syntax>) {
		self.syntax_diags.append(syntax);
	}

	/// Pushes a semantic diagnostic.
	fn push_semantic_diag(&mut self, diag: Semantic) {
		self.semantic_diags.push(diag);
	}

	/// Appends a collection of semantic diagnostics.
	fn append_semantic_diags(&mut self, semantic: &mut Vec<Semantic>) {
		self.semantic_diags.append(semantic);
	}

	/// Pushes a syntax highlighting token over the given span.
	fn push_colour(&mut self, span: Span, token: SyntaxToken) {
		// When we are within a macro, we don't want to produce syntax tokens.
		// Note: This functionality is duplicated in the `ShuntingYard::colour()` method.
		if self.streams.len() != 1 {
			return;
		}

		if self.conditional_syntax_tokens.is_empty() {
			self.syntax_tokens.push((token, span));
		} else {
			let mut previous_span = self
				.syntax_tokens
				.get(0)
				.map(|(_, s)| *s)
				.unwrap_or(Span::new(0, 0));
			while let Some(bottom) = self.conditional_syntax_tokens.first() {
				if bottom.0.is_before(&previous_span) {
					// We have already consumes syntax tokens for the conditional directive so we want to discard
					// current ones. This happens if error recovery consumes conditional directive symbols.
					self.conditional_syntax_tokens.remove(0);
					continue;
				} else if bottom.0.is_before(&span) {
					// The current conditional syntax tokens are before this new span, so we must add them
					// beforehand.
					let (_, mut tokens) =
						self.conditional_syntax_tokens.remove(0);
					self.syntax_tokens.append(&mut tokens);
					continue;
				} else {
					break;
				}
			}
			self.syntax_tokens.push((token, span));
		}
	}

	/// Appends a collection of syntax highlighting tokens.
	fn append_colours(&mut self, colours: &mut Vec<Spanned<SyntaxToken>>) {
		if self.conditional_syntax_tokens.is_empty() {
			self.syntax_tokens.append(colours);
		} else if !self.conditional_syntax_tokens.is_empty()
			&& !colours.is_empty()
		{
			let previous_span = self
				.syntax_tokens
				.last()
				.map(|(_, s)| *s)
				.unwrap_or(Span::new(0, 0));
			for colour in colours.into_iter() {
				let span = &colour.1;
				while let Some(bottom) = self.conditional_syntax_tokens.first()
				{
					if bottom.0.is_before(&previous_span) {
						// We have already consumes syntax tokens for the conditional directive so we want to
						// discard current ones. This happens if error recovery consumes conditional directive
						// symbols.
						self.conditional_syntax_tokens.remove(0);
						continue;
					} else if bottom.0.is_before(&span) {
						// The current conditional syntax tokens are before this new span, so we must add them
						// beforehand.
						let (_, mut tokens) =
							self.conditional_syntax_tokens.remove(0);
						self.syntax_tokens.append(&mut tokens);
						continue;
					} else {
						break;
					}
				}
			}
		} else {
			// If we are not appending anything, we can't know whether we can append any conditional expression
			// tokens, hence we do nothing.
		}
	}
}

/* ACTUAL STATEMENT PARSING LOGIC BELOW */

/// Consumes tokens until a beginning of a new statement is reached.
///
/// This function consumes tokens until a keyword which can begin a statement is found, or until a semi-colon is
/// reached (which is consumed). This is used for some instances of error recovery, where no more specific
/// strategies can be employed.
fn seek_next_stmt(walker: &mut Walker) {
	loop {
		match walker.peek() {
			Some((token, span)) => {
				if token.can_start_statement() {
					return;
				} else if *token == Token::Semi {
					walker.push_colour(span, SyntaxToken::Punctuation);
					walker.advance();
					return;
				} else {
					walker.push_colour(span, SyntaxToken::Invalid);
					walker.advance();
					continue;
				}
			}
			None => return,
		}
	}
}

/// Invalidates a set of qualifiers.
///
/// This function is used to emit a diagnostic about the use of qualifiers before a statement which doesn't support
/// qualifiers.
fn invalidate_qualifiers(walker: &mut Walker, qualifiers: Vec<Qualifier>) {
	if let Some(q) = qualifiers.last() {
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::FoundQualifiersBeforeStmt(Span::new(
				qualifiers.first().unwrap().span.start,
				q.span.end,
			)),
		));
	}
}

/// Parses an individual statement at the current position.
fn parse_stmt(walker: &mut Walker, nodes: &mut Vec<ast::Node>) {
	let qualifiers = try_parse_qualifiers(walker);

	let Some((token, token_span)) = walker.get() else {
		return;
	};

	match token {
		Token::LBrace => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxToken::Punctuation);
			walker.advance();
			let block = parse_scope(walker, BRACE_SCOPE, token_span);
			nodes.push(Node {
				span: block.span,
				ty: NodeTy::Block(block),
			});
		}
		Token::Semi => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxToken::Punctuation);
			walker.advance();
			nodes.push(Node {
				span: token_span,
				ty: NodeTy::Empty,
			});
		}
		Token::Struct => parse_struct(walker, nodes, qualifiers, token_span),
		Token::Directive(stream) => {
			invalidate_qualifiers(walker, qualifiers);
			parse_directive(walker, nodes, stream, token_span);
			walker.advance();
		}
		Token::If => parse_if(walker, nodes, token_span),
		Token::Switch => parse_switch(walker, nodes, token_span),
		Token::For => parse_for_loop(walker, nodes, token_span),
		Token::While => parse_while_loop(walker, nodes, token_span),
		Token::Do => parse_do_while_loop(walker, nodes, token_span),
		Token::Break => {
			invalidate_qualifiers(walker, qualifiers);
			parse_break_continue_discard(
				walker,
				nodes,
				token_span,
				|| NodeTy::Break,
				|span| Syntax::Stmt(StmtDiag::BreakExpectedSemiAfterKw(span)),
			)
		}
		Token::Continue => {
			invalidate_qualifiers(walker, qualifiers);
			parse_break_continue_discard(
				walker,
				nodes,
				token_span,
				|| NodeTy::Continue,
				|span| {
					Syntax::Stmt(StmtDiag::ContinueExpectedSemiAfterKw(span))
				},
			);
		}
		Token::Discard => {
			invalidate_qualifiers(walker, qualifiers);
			parse_break_continue_discard(
				walker,
				nodes,
				token_span,
				|| NodeTy::Discard,
				|span| Syntax::Stmt(StmtDiag::DiscardExpectedSemiAfterKw(span)),
			);
		}
		Token::Return => {
			invalidate_qualifiers(walker, qualifiers);
			parse_return(walker, nodes, token_span);
		}
		Token::RBrace => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxToken::Punctuation);
			walker.push_syntax_diag(Syntax::FoundUnmatchedRBrace(token_span));
			walker.advance();
		}
		Token::Else => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxToken::Keyword);
			walker.push_syntax_diag(Syntax::FoundLonelyElseKw(token_span));
			walker.advance();
		}
		Token::Case => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxToken::Keyword);
			walker.push_syntax_diag(Syntax::FoundLonelyCaseKw(token_span));
			walker.advance();
		}
		Token::Default => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxToken::Keyword);
			walker.push_syntax_diag(Syntax::FoundLonelyDefaultKw(token_span));
			walker.advance();
		}
		Token::Subroutine => {
			invalidate_qualifiers(walker, qualifiers);
			parse_subroutine(walker, nodes, token_span);
		}
		Token::Reserved(str) => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxToken::Invalid);
			walker.push_syntax_diag(Syntax::FoundReservedKw(token_span, str));
			walker.advance();
		}
		Token::Invalid(c) => {
			invalidate_qualifiers(walker, qualifiers);
			walker.push_colour(token_span, SyntaxToken::Invalid);
			walker.push_syntax_diag(Syntax::FoundIllegalChar(token_span, c));
			walker.advance();
		}
		_ => try_parse_definition_declaration_expr(
			walker, nodes, qualifiers, false,
		),
	}
}

/// Parses a scope of statements.
///
/// This function assumes that the opening delimiter is already consumed.
fn parse_scope(
	walker: &mut Walker,
	exit_condition: ScopeEnd,
	opening_span: Span,
) -> Scope {
	let mut nodes = Vec::new();
	let ending_span = loop {
		// Check if we have reached the closing delimiter.
		if let Some(span) = exit_condition(walker, opening_span) {
			break span;
		}
		parse_stmt(walker, &mut nodes);
	};

	Scope {
		contents: nodes,
		span: Span::new(opening_span.start, ending_span.end),
	}
}

/// A function, which given the `walker`, determines whether to end parsing the current scope of statements and
/// return back to the caller. If this returns `Some`, we have reached the end of the scope. If the span returned
/// is zero-width, that means we have no closing delimiter.
///
/// This also takes a span of the opening delimiter which allows for the creation of a syntax error if the function
/// never encounters the desired ending delimiter.
type ScopeEnd = fn(&mut Walker, Span) -> Option<Span>;

const BRACE_SCOPE: ScopeEnd = |walker, l_brace_span| match walker.peek() {
	Some((token, span)) => {
		if *token == Token::RBrace {
			walker.push_colour(span, SyntaxToken::Punctuation);
			walker.advance();
			Some(span)
		} else {
			None
		}
	}
	None => {
		walker.push_syntax_diag(Syntax::Stmt(StmtDiag::ScopeMissingRBrace(
			l_brace_span,
			walker.get_last_span().next_single_width(),
		)));
		Some(walker.get_last_span().end_zero_width())
	}
};

const SWITCH_CASE_SCOPE: ScopeEnd = |walker, _start_span| match walker.peek() {
	Some((token, span)) => match token {
		Token::Case | Token::Default | Token::RBrace => Some(span),
		_ => None,
	},
	None => {
		walker.push_syntax_diag(Syntax::Stmt(StmtDiag::SwitchExpectedRBrace(
			walker.get_last_span().next_single_width(),
		)));
		Some(walker.get_last_span().end_zero_width())
	}
};

/// Tries to parse one or more qualifiers.
///
/// This function makes no assumptions as to what the current token is.
fn try_parse_qualifiers(walker: &mut Walker) -> Vec<Qualifier> {
	let mut qualifiers = Vec::new();
	'outer: loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => break,
		};

		match token {
			Token::Const => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Const,
				});
			}
			Token::In => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::In,
				});
			}
			Token::Out => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Out,
				});
			}
			Token::InOut => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::InOut,
				});
			}
			Token::Attribute => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Attribute,
				});
			}
			Token::Uniform => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Uniform,
				});
			}
			Token::Varying => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Varying,
				});
			}
			Token::Buffer => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Buffer,
				});
			}
			Token::Shared => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Shared,
				});
			}
			Token::Centroid => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Centroid,
				});
			}
			Token::Sample => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Sample,
				});
			}
			Token::Patch => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Patch,
				});
			}
			Token::Flat => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Flat,
				});
			}
			Token::Smooth => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Smooth,
				});
			}
			Token::NoPerspective => {
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::NoPerspective,
				});
			}
			Token::HighP => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::HighP,
				});
			}
			Token::MediumP => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::MediumP,
				});
			}
			Token::LowP => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::LowP,
				});
			}
			Token::Invariant => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Invariant,
				});
			}
			Token::Precise => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Precise,
				});
			}
			Token::Coherent => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Coherent,
				});
			}
			Token::Volatile => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Volatile,
				});
			}
			Token::Restrict => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Restrict,
				});
			}
			Token::Readonly => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Readonly,
				});
			}
			Token::Writeonly => {
				walker.push_colour(token_span, SyntaxToken::Keyword);
				qualifiers.push(Qualifier {
					span: token_span,
					ty: QualifierTy::Writeonly,
				});
			}
			Token::Layout => {
				let kw_span = token_span;
				walker.push_colour(kw_span, SyntaxToken::Keyword);
				walker.advance();

				// Consume the `(`.
				let (token, token_span) = match walker.peek() {
					Some(t) => t,
					None => {
						// We don't have any layout contents yet.
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::LayoutExpectedLParenAfterKw(
								kw_span.next_single_width(),
							),
						));
						qualifiers.push(Qualifier {
							span: kw_span,
							ty: QualifierTy::Layout(vec![]),
						});
						break;
					}
				};
				let l_paren_span = if *token == Token::LParen {
					walker.push_colour(token_span, SyntaxToken::Punctuation);
					walker.advance();
					token_span
				} else {
					// We don't have any layout contents yet.
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::LayoutExpectedLParenAfterKw(
							kw_span.next_single_width(),
						),
					));
					qualifiers.push(Qualifier {
						span: kw_span,
						ty: QualifierTy::Layout(vec![]),
					});
					break;
				};

				// Look for any layouts until we hit a closing `)` parenthesis.
				#[derive(PartialEq)]
				enum Prev {
					None,
					Layout,
					Comma,
					Invalid,
				}
				let mut prev = Prev::None;
				let mut prev_span = l_paren_span;
				let mut layouts = Vec::new();
				let r_paren_span = loop {
					let (token, token_span) = match walker.get() {
						Some(t) => t,
						None => {
							// We have not yet finished parsing the layout list, but we treat this as a valid
							// layout qualifier.
							let span = Span::new(
								kw_span.start,
								walker.get_last_span().end,
							);
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::LayoutMissingRParen(
									span.next_single_width(),
								),
							));
							qualifiers.push(Qualifier {
								span,
								ty: QualifierTy::Layout(layouts),
							});
							break 'outer;
						}
					};

					match token {
						Token::Comma => {
							walker.push_colour(
								token_span,
								SyntaxToken::Punctuation,
							);
							walker.advance();
							if prev == Prev::Comma {
								walker.push_syntax_diag(Syntax::Stmt(
									StmtDiag::LayoutExpectedLayoutAfterComma(
										Span::new(
											prev_span.start,
											token_span.end,
										),
									),
								));
							} else if prev == Prev::None {
								walker.push_syntax_diag(Syntax::Stmt(StmtDiag::LayoutExpectedLayoutBetweenParenComma(
									Span::new(prev_span.start, token_span.end)
								)));
							}
							prev = Prev::Comma;
							prev_span = token_span;
							continue;
						}
						Token::RParen => {
							walker.push_colour(
								token_span,
								SyntaxToken::Punctuation,
							);
							walker.advance();
							break token_span;
						}
						_ => {}
					}

					if prev == Prev::Layout {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::LayoutExpectedCommaAfterLayout(
								prev_span.next_single_width(),
							),
						));
					}
					let layout_span_start = token_span.start;

					// Consume the layout identifier. This creates a constructor either for a layout which only
					// consists of an identifier, or for a layout which expects an expression.
					let constructor: Either<
						LayoutTy,
						fn(Option<Expr>) -> LayoutTy,
					> = if let Token::Ident(str) = token {
						match str.as_ref() {
							"packed" => Either::Left(LayoutTy::Packed),
							"std140" => Either::Left(LayoutTy::Std140),
							"std430" => Either::Left(LayoutTy::Std430),
							"row_major" => Either::Left(LayoutTy::RowMajor),
							"column_major" => {
								Either::Left(LayoutTy::ColumnMajor)
							}
							"binding" => Either::Right(LayoutTy::Binding),
							"offset" => Either::Right(LayoutTy::Offset),
							"align" => Either::Right(LayoutTy::Align),
							"location" => Either::Right(LayoutTy::Location),
							"component" => Either::Right(LayoutTy::Component),
							"index" => Either::Right(LayoutTy::Index),
							"points" => Either::Left(LayoutTy::Points),
							"lines" => Either::Left(LayoutTy::Lines),
							"isolines" => Either::Left(LayoutTy::Isolines),
							"triangles" => Either::Left(LayoutTy::Triangles),
							"quads" => Either::Left(LayoutTy::Quads),
							"equal_spacing" => {
								Either::Left(LayoutTy::EqualSpacing)
							}
							"fractional_even_spacing" => {
								Either::Left(LayoutTy::FractionalEvenSpacing)
							}
							"fractional_odd_spacing" => {
								Either::Left(LayoutTy::FractionalOddSpacing)
							}
							"cw" => Either::Left(LayoutTy::Clockwise),
							"ccw" => Either::Left(LayoutTy::CounterClockwise),
							"point_mode" => Either::Left(LayoutTy::PointMode),
							"line_adjacency" => {
								Either::Left(LayoutTy::LineAdjacency)
							}
							"triangle_adjacency" => {
								Either::Left(LayoutTy::TriangleAdjacency)
							}
							"invocations" => {
								Either::Right(LayoutTy::Invocations)
							}
							"origin_upper_left" => {
								Either::Left(LayoutTy::OriginUpperLeft)
							}
							"pixel_center_integer" => {
								Either::Left(LayoutTy::PixelCenterInteger)
							}
							"early_fragment_tests" => {
								Either::Left(LayoutTy::EarlyFragmentTests)
							}
							"local_size_x" => {
								Either::Right(LayoutTy::LocalSizeX)
							}
							"local_size_y" => {
								Either::Right(LayoutTy::LocalSizeY)
							}
							"local_size_z" => {
								Either::Right(LayoutTy::LocalSizeZ)
							}
							"xfb_buffer" => Either::Right(LayoutTy::XfbBuffer),
							"xfb_stride" => Either::Right(LayoutTy::XfbStride),
							"xfb_offset" => Either::Right(LayoutTy::XfbOffset),
							"vertices" => Either::Right(LayoutTy::Vertices),
							"line_strip" => Either::Left(LayoutTy::LineStrip),
							"triangle_strip" => {
								Either::Left(LayoutTy::TriangleStrip)
							}
							"max_vertices" => {
								Either::Right(LayoutTy::MaxVertices)
							}
							"stream" => Either::Right(LayoutTy::Stream),
							"depth_any" => Either::Left(LayoutTy::DepthAny),
							"depth_greater" => {
								Either::Left(LayoutTy::DepthGreater)
							}
							"depth_less" => Either::Left(LayoutTy::DepthLess),
							"depth_unchanged" => {
								Either::Left(LayoutTy::DepthUnchanged)
							}
							_ => {
								// We have an identifier that is not a valid layout. We ignore it and continue
								// for the next layout.
								walker.push_colour(
									token_span,
									SyntaxToken::UnresolvedIdent,
								);
								walker.push_syntax_diag(Syntax::Stmt(
									StmtDiag::LayoutInvalidIdent(token_span),
								));
								walker.advance();
								prev = Prev::Invalid;
								prev_span = token_span;
								continue;
							}
						}
					} else if let Token::Shared = token {
						Either::Left(LayoutTy::Shared)
					} else {
						// We have a token that is not a valid layout. We ignore it and continue for the next
						// layout.
						walker.push_colour(token_span, SyntaxToken::Invalid);
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::LayoutInvalidIdent(token_span),
						));
						walker.advance();
						prev = Prev::Invalid;
						prev_span = token_span;
						continue;
					};

					let (constructor, ident_span) = match constructor {
						Either::Left(ty) => {
							walker.push_colour(
								token_span,
								SyntaxToken::LayoutIdent,
							);
							walker.advance();
							layouts.push(Layout {
								span: token_span,
								ty,
							});
							prev = Prev::Layout;
							prev_span = token_span;
							continue;
						}
						Either::Right(constructor) => {
							walker.push_colour(
								token_span,
								SyntaxToken::LayoutIdent,
							);
							walker.advance();
							(constructor, token_span)
						}
					};

					// We have a layout identifier which expects an expression.

					// Consume the `=`.
					let (token, token_span) = match walker.peek() {
						Some(t) => t,
						None => {
							// We are missing the equals sign and we don't know what comes after. We ignore this
							// layout.
							let span = Span::new(
								kw_span.start,
								walker.get_last_span().end,
							);
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::LayoutExpectedEqAfterIdent(
									span.next_single_width(),
								),
							));
							qualifiers.push(Qualifier {
								span,
								ty: QualifierTy::Layout(layouts),
							});
							break 'outer;
						}
					};
					let eq_span = if let Token::Op(OpTy::Eq) = token {
						walker.push_colour(token_span, SyntaxToken::Operator);
						walker.advance();
						token_span
					} else {
						// We are missing the equals sign and we don't know what comes after. We ignore this
						// layout.
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::LayoutExpectedEqAfterIdent(
								ident_span.next_single_width(),
							),
						));
						prev = Prev::Layout;
						prev_span = ident_span;
						continue;
					};

					// Consume the expression.
					let value_expr = match expr_parser(
						walker,
						Mode::DisallowTopLevelList,
						[Token::RParen],
					) {
						(Some(e), mut syntax, mut semantic, mut colours) => {
							walker.append_colours(&mut colours);
							walker.append_syntax_diags(&mut syntax);
							walker.append_semantic_diags(&mut semantic);
							e
						}
						(None, _, _, _) => {
							// We are missing the expression.
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::LayoutExpectedExprAfterEq(
									eq_span.next_single_width(),
								),
							));
							layouts.push(Layout {
								span: Span::new(layout_span_start, eq_span.end),
								ty: constructor(None),
							});
							prev = Prev::Layout;
							prev_span = eq_span;
							continue;
						}
					};

					prev = Prev::Layout;
					prev_span = value_expr.span;
					layouts.push(Layout {
						span: Span::new(layout_span_start, value_expr.span.end),
						ty: constructor(Some(value_expr)),
					});
				};

				qualifiers.push(Qualifier {
					span: Span::new(kw_span.start, r_paren_span.end),
					ty: QualifierTy::Layout(layouts),
				});
				continue;
			}
			_ => break,
		}
		walker.advance();
	}

	qualifiers
}

/// Tries to parse a variable definition or a function declaration/definition or an expression statement.
///
/// This function attempts to look for a statement at the current position. If this fails, error recovery till the
/// next clear statement delineation occurs.
///
/// - `parsing_last_for_stmt` - Set to `true` if this function is attempting to parse the increment statement in a
///   for loop header.
fn try_parse_definition_declaration_expr(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	qualifiers: Vec<Qualifier>,
	parsing_last_for_stmt: bool,
) {
	// We attempt to parse an expression at the current position.
	let (start, mut start_syntax, mut start_semantic, mut start_colours) =
		match expr_parser(walker, Mode::Default, [Token::Semi]) {
			(Some(expr), syntax, semantic, colours) => {
				(expr, syntax, semantic, colours)
			}
			(None, _, _, _) => {
				// The current token cannot begin any sort of expression. Since this function gets called if all
				// other statement branches have failed to match, it means that whatever we have cannot be a valid
				// statement at all.
				invalidate_qualifiers(walker, qualifiers);
				seek_next_stmt(walker);
				return;
			}
		};

	// We test if the expression can be converted into a type.
	if let Some(mut type_) = Type::parse(&start) {
		// Since we ran the expression parser in the Default mode, what we have so far must be something like
		// `foobar`, `int`, `vec2[3]`, `MyStruct` etc. This can be the type part of a declaration/definition, but
		// it could be just an expression statement depending on what comes next.

		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We lack any identifiers necessary for a declaration/definition, so this must be an expression
				// statement.
				invalidate_qualifiers(walker, qualifiers);
				walker.append_colours(&mut start_colours);
				walker.append_syntax_diags(&mut start_syntax);
				walker.append_semantic_diags(&mut start_semantic);
				if parsing_last_for_stmt {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ForExpectedRParenAfterStmts(
							start.span.next_single_width(),
						),
					))
				} else {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ExprStmtExpectedSemiAfterExpr(
							start.span.next_single_width(),
						),
					));
				}
				nodes.push(Node {
					span: start.span,
					ty: NodeTy::Expr(start),
				});
				return;
			}
		};

		// Check whether we have a function declaration/definition, or whether this is an expression immediately
		// followed by a semi-colon.
		match token {
			Token::Ident(i) => match walker.lookahead_1() {
				Some(next) => match next.0 {
					Token::LParen => {
						// We have a function declaration/definition.
						type_.qualifiers = qualifiers;
						let l_paren_span = next.1;
						let ident = Ident {
							name: i.clone(),
							span: token_span,
						};
						walker.push_colour(
							token_span,
							SyntaxToken::UncheckedIdent,
						);
						walker.advance();
						walker.push_colour(next.1, SyntaxToken::Punctuation);
						walker.advance();
						parse_function(
							walker,
							nodes,
							type_,
							ident,
							l_paren_span,
						);
						return;
					}
					_ => {}
				},
				None => {}
			},
			Token::Semi => {
				// We have an expression statement.
				invalidate_qualifiers(walker, qualifiers);
				let semi_span = token_span;
				walker.append_colours(&mut start_colours);
				walker.append_syntax_diags(&mut start_syntax);
				walker.append_semantic_diags(&mut start_semantic);
				walker.push_colour(semi_span, SyntaxToken::Punctuation);
				walker.advance();
				if parsing_last_for_stmt {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ForExpectedRParenAfterStmts(semi_span),
					));
				}
				nodes.push(Node {
					span: Span::new(start.span.start, semi_span.end),
					ty: NodeTy::Expr(start),
				});
				return;
			}
			Token::RParen if parsing_last_for_stmt => {
				// We have an expression statement.
				invalidate_qualifiers(walker, qualifiers);
				walker.append_colours(&mut start_colours);
				walker.append_syntax_diags(&mut start_syntax);
				walker.append_semantic_diags(&mut start_semantic);
				nodes.push(Node {
					span: start.span,
					ty: NodeTy::Expr(start),
				});
				return;
			}
			_ => {}
		}

		// We don't have a function declaration/definition, so this must be a variable definition (with possibly an
		// initialization) or an expression statement.

		// We attempt to parse an expression for the identifier(s).
		let (
			ident_expr,
			mut ident_syntax,
			mut ident_semantic,
			mut ident_colours,
		) = match expr_parser(walker, Mode::BreakAtEq, [Token::Semi]) {
			(Some(e), syntax, semantic, colours) => {
				(e, syntax, semantic, colours)
			}
			(None, _, _, _) => {
				// We have an expression followed by neither another expression nor a semi-colon. We treat this
				// as an expression statement since that's the closest possible match.
				invalidate_qualifiers(walker, qualifiers);
				walker.append_colours(&mut start_colours);
				walker.append_syntax_diags(&mut start_syntax);
				walker.append_semantic_diags(&mut start_semantic);
				if parsing_last_for_stmt {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ForExpectedRParenAfterStmts(
							start.span.next_single_width(),
						),
					))
				} else {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ExprStmtExpectedSemiAfterExpr(
							start.span.next_single_width(),
						),
					));
				}
				nodes.push(Node {
					span: start.span,
					ty: NodeTy::Expr(start),
				});
				return;
			}
		};
		let ident_span = ident_expr.span;

		// We test if the identifier(s) expression can be converted into one or more variable identifiers.
		let ident_info = if let Some(i) = Type::parse_var_idents(&ident_expr) {
			i
		} else {
			// We have a second expression after the first expression, but the second expression can't be converted
			// to one or more identifiers for a variable definition. We treat the first expression as an expression
			// statement, and the second expression as invalid.
			invalidate_qualifiers(walker, qualifiers);
			walker.append_colours(&mut start_colours);
			walker.append_syntax_diags(&mut start_syntax);
			walker.append_semantic_diags(&mut start_semantic);
			if parsing_last_for_stmt {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ForExpectedRParenAfterStmts(
						start.span.next_single_width(),
					),
				))
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ExprStmtExpectedSemiAfterExpr(
						start.span.next_single_width(),
					),
				));
			}
			nodes.push(Node {
				span: start.span,
				ty: NodeTy::Expr(start),
			});
			for (_, span) in ident_colours {
				walker.push_colour(span, SyntaxToken::Invalid);
			}
			seek_next_stmt(walker);
			return;
		};

		// We have one expression which can be converted to a type, and a second expression which can be converted
		// to one or more identifiers. That means the first expression will have a syntax error about a missing
		// operator between the two; we remove that error since in this case it's not applicable.
		start_syntax.retain(|e| {
			if let Syntax::Expr(ExprDiag::FoundOperandAfterOperand(_, _)) = e {
				false
			} else {
				true
			}
		});
		type_.qualifiers = qualifiers;
		walker.append_colours(&mut start_colours);
		walker.append_syntax_diags(&mut start_syntax);
		walker.append_semantic_diags(&mut start_semantic);
		walker.append_colours(&mut ident_colours);
		walker.append_syntax_diags(&mut ident_syntax);
		walker.append_semantic_diags(&mut ident_semantic);

		fn var_def(
			type_: Type,
			idents: Vec<(Ident, Vec<ArrSize>)>,
			end_pos: usize,
		) -> Node {
			let span = Span::new(type_.span.start, end_pos);
			let mut vars = combine_type_with_idents(type_, idents);
			match vars.len() {
				1 => {
					let (type_, ident) = vars.remove(0);
					Node {
						span,
						ty: NodeTy::VarDef { type_, ident },
					}
				}
				_ => Node {
					span,
					ty: NodeTy::VarDefs(vars),
				},
			}
		}

		fn var_def_init(
			type_: Type,
			idents: Vec<(Ident, Vec<ArrSize>)>,
			value: Option<Expr>,
			end_pos: usize,
		) -> Node {
			let span = Span::new(type_.span.start, end_pos);
			let mut vars = combine_type_with_idents(type_, idents);
			match vars.len() {
				1 => {
					let (type_, ident) = vars.remove(0);
					Node {
						span,
						ty: NodeTy::VarDefInit {
							type_,
							ident,
							value,
						},
					}
				}
				_ => Node {
					span,
					ty: NodeTy::VarDefInits(vars, value),
				},
			}
		}

		// Consume the `;` for a definition, or a `=` for a definition with initialization.
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We have something that matches the start of a variable definition. Since we have neither the `;`
				// or `=`, we assume that this is a definition without initialization that is missing the
				// semi-colon.
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::VarDefExpectedSemiOrEqAfterIdents(
						ident_span.next_single_width(),
					),
				));
				nodes.push(var_def(type_, ident_info, ident_span.end));
				return;
			}
		};
		if *token == Token::Semi {
			// We have a variable definition without initialization.
			let semi_span = token_span;
			walker.push_colour(semi_span, SyntaxToken::Punctuation);
			walker.advance();
			nodes.push(var_def(type_, ident_info, semi_span.end));
			return;
		} else if *token == Token::Op(crate::lexer::OpTy::Eq) {
			// We have a variable definition with initialization.
			let eq_span = token_span;
			walker.push_colour(eq_span, SyntaxToken::Operator);
			walker.advance();

			// Consume the value expression.
			let value_expr =
				match expr_parser(walker, Mode::Default, [Token::Semi]) {
					(Some(e), mut syntax, mut semantic, mut colours) => {
						walker.append_colours(&mut colours);
						walker.append_syntax_diags(&mut syntax);
						walker.append_semantic_diags(&mut semantic);
						e
					}
					(None, _, _, _) => {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::VarDefInitExpectedValueAfterEq(
								eq_span.next_single_width(),
							),
						));
						nodes.push(var_def_init(
							type_,
							ident_info,
							None,
							eq_span.end,
						));
						seek_next_stmt(walker);
						return;
					}
				};

			// Consume the semi-colon.
			let (token, token_span) = match walker.peek() {
				Some(t) => t,
				None => {
					let value_span = value_expr.span;
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::VarDefInitExpectedSemiAfterValue(
							value_span.next_single_width(),
						),
					));
					nodes.push(var_def_init(
						type_,
						ident_info,
						Some(value_expr),
						value_span.end,
					));
					return;
				}
			};
			if *token == Token::Semi {
				let semi_span = token_span;
				walker.push_colour(semi_span, SyntaxToken::Punctuation);
				walker.advance();
				nodes.push(var_def_init(
					type_,
					ident_info,
					Some(value_expr),
					semi_span.end,
				));
				return;
			} else {
				let end_span = token_span;
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::VarDefInitExpectedSemiAfterValue(
						end_span.next_single_width(),
					),
				));
				nodes.push(var_def_init(
					type_,
					ident_info,
					Some(value_expr),
					end_span.end,
				));
				seek_next_stmt(walker);
				return;
			}
		} else {
			// We have something that matches the start of a variable definition. Since we have neither the `;` or
			// `=`, we assume that this is a definition without initialization which is missing the semi-colon.
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::VarDefExpectedSemiOrEqAfterIdents(
					ident_span.next_single_width(),
				),
			));
			nodes.push(var_def(type_, ident_info, ident_span.end));
			seek_next_stmt(walker);
			return;
		}
	}

	// We have an expression which cannot be parsed as a type, so this cannot start a declaration/definition; it
	// must therefore be a standalone expression statement.
	invalidate_qualifiers(walker, qualifiers);
	let expr = start;
	walker.append_colours(&mut start_colours);
	walker.append_syntax_diags(&mut start_syntax);
	walker.append_semantic_diags(&mut start_semantic);

	// Consume the `;` to end the statement.
	let semi_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::Semi {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				Some(span)
			} else {
				None
			}
		}
		None => None,
	};
	if semi_span.is_none() {
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::ExprStmtExpectedSemiAfterExpr(
				expr.span.next_single_width(),
			),
		));
		seek_next_stmt(walker);
	}

	nodes.push(Node {
		span: if let Some(semi_span) = semi_span {
			Span::new(expr.span.start, semi_span.end)
		} else {
			expr.span
		},
		ty: NodeTy::Expr(expr),
	});
}

/// Parses a function declaration/definition.
///
/// This function assumes that the return type, ident, and opening parenthesis have been consumed.
fn parse_function(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	return_type: Type,
	ident: Ident,
	l_paren_span: Span,
) {
	// Look for any parameters until we hit a closing `)` parenthesis.
	#[derive(PartialEq)]
	enum Prev {
		None,
		Param,
		Comma,
		Invalid,
	}
	let mut prev = Prev::None;
	let mut prev_span = l_paren_span;
	let mut params = Vec::new();
	let param_end_span = loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We have not yet finished parsing the parameter list, but we treat this as a valid declaration
				// since that's the closest match.
				let span = Span::new(return_type.span.start, prev_span.end);
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ParamsExpectedRParen(
						prev_span.next_single_width(),
					),
				));
				nodes.push(Node {
					span,
					ty: NodeTy::FnDecl {
						return_type,
						ident,
						params,
					},
				});
				return;
			}
		};

		match token {
			Token::Comma => {
				walker.push_colour(token_span, SyntaxToken::Punctuation);
				walker.advance();
				if prev == Prev::Comma {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsExpectedParamAfterComma(
							Span::new_between(prev_span, token_span),
						),
					));
				} else if prev == Prev::None {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsExpectedParamBetweenParenComma(
							Span::new_between(l_paren_span, token_span),
						),
					));
				}
				prev = Prev::Comma;
				prev_span = token_span;
				continue;
			}
			Token::RParen => {
				walker.push_colour(token_span, SyntaxToken::Punctuation);
				walker.advance();
				if prev == Prev::Comma {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsExpectedParamAfterComma(
							Span::new_between(prev_span, token_span),
						),
					));
				}
				break token_span;
			}
			Token::Semi => {
				walker.push_colour(token_span, SyntaxToken::Punctuation);
				walker.advance();
				// We have not yet finished parsing the parameter list but we've encountered a semi-colon. We treat
				// this as a valid declaration since that's the closest match.
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ParamsExpectedRParen(
						prev_span.next_single_width(),
					),
				));
				nodes.push(Node {
					span: Span::new(return_type.span.start, token_span.end),
					ty: NodeTy::FnDecl {
						return_type,
						ident,
						params,
					},
				});
				return;
			}
			Token::LBrace => {
				walker.push_colour(token_span, SyntaxToken::Punctuation);
				// We don't advance because the next check after this loop checks for a l-brace.

				// We have not yet finished parsing the parameter list but we've encountered a l-brace. We treat
				// this as a potentially valid definition since that's the closest match.
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ParamsExpectedRParen(
						prev_span.next_single_width(),
					),
				));
				break token_span;
			}
			_ => {}
		}

		if prev == Prev::Param {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ParamsExpectedCommaAfterParam(
					prev_span.next_single_width(),
				),
			));
		}
		let param_span_start = token_span.start;

		let qualifiers = try_parse_qualifiers(walker);

		// Consume the type.
		let mut type_ = match expr_parser(
			walker,
			Mode::TakeOneUnit,
			[Token::Semi, Token::LBrace],
		) {
			(Some(e), _, mut semantic, mut colours) => {
				if let Some(type_) = Type::parse(&e) {
					walker.append_colours(&mut colours);
					walker.append_semantic_diags(&mut semantic);
					type_
				} else {
					// We have an expression which cannot be parsed into a type. We ignore this and continue
					// searching for the next parameter.
					for (_, span) in colours {
						walker.push_colour(span, SyntaxToken::Invalid);
					}
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ParamsInvalidTypeExpr(e.span),
					));
					prev = Prev::Invalid;
					prev_span = Span::new(param_span_start, e.span.end);
					continue;
				}
			}
			(None, _, _, _) => {
				// We immediately have a token that is not an expression. We ignore this and loop until we hit
				// something recognizable.
				let end_span = loop {
					match walker.peek() {
						Some((token, span)) => {
							if *token == Token::Comma
								|| *token == Token::RParen || *token
								== Token::Semi || *token == Token::LBrace
							{
								break span;
							} else {
								walker.push_colour(span, SyntaxToken::Invalid);
								walker.advance();
								continue;
							}
						}
						None => break walker.get_last_span(),
					}
				};
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ParamsInvalidTypeExpr(Span::new(
						param_span_start,
						end_span.end,
					)),
				));
				prev = Prev::Invalid;
				prev_span = token_span;
				continue;
			}
		};

		// Look for the optional ident.
		let (ident_expr, ident_colours) = match expr_parser(
			walker,
			Mode::TakeOneUnit,
			[Token::Semi, Token::LBrace],
		) {
			(Some(e), _, mut semantic, colours) => {
				walker.append_semantic_diags(&mut semantic);
				(e, colours)
			}
			(None, _, _, _) => {
				// We have a first expression and then something that is not an expression. We treat this as an
				// anonymous parameter, whatever the current token is will be dealt with in the next iteration.
				type_.qualifiers = qualifiers;
				let param_span = Span::new(param_span_start, type_.span.end);
				params.push(Param {
					span: param_span,
					type_,
					ident: Omittable::None,
				});
				prev = Prev::Param;
				prev_span = param_span;
				continue;
			}
		};
		let ident_span = ident_expr.span;

		// Invariant: This vector is guaranteed to have a length of 1 because the `ident_expr` was parsed with the
		// `TakeOneUnit` mode which prevents lists.
		let ident_info = if let Some(i) = Type::parse_var_idents(&ident_expr) {
			i
		} else {
			// We have a second expression after the first expression, but the second expression can't be converted
			// to an identifier for the parameter. We treat the first type expression as an anonymous parameter,
			// and the second expression as invalid.
			let param_span = Span::new(param_span_start, type_.span.end);
			type_.qualifiers = qualifiers;
			params.push(Param {
				span: Span::new(param_span_start, type_.span.end),
				type_,
				ident: Omittable::None,
			});
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ParamsInvalidIdentExpr(ident_expr.span),
			));
			for (_, span) in ident_colours {
				walker.push_colour(span, SyntaxToken::Invalid);
			}
			prev = Prev::Param;
			prev_span = param_span;
			continue;
		};

		type_.qualifiers = qualifiers;
		let (type_, ident) =
			combine_type_with_idents(type_, ident_info).remove(0);
		let param_span = Span::new(param_span_start, ident_span.end);
		params.push(Param {
			span: param_span,
			type_,
			ident: Omittable::Some(ident),
		});
		prev = Prev::Param;
		prev_span = param_span;
	};

	// Consume the `;` for a declaration or a `{` for a definition.
	let (token, token_span) = match walker.peek() {
		Some(t) => t,
		None => {
			// This branch will only be triggered if we exited the param loop with a `)`, it will not trigger if we
			// exit with a `{` because that token is not consumed.

			// We are missing a `;` for a declaration. We treat this as a declaration since that's the closest
			// match.
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::FnExpectedSemiOrLBraceAfterParams(
					param_end_span.next_single_width(),
				),
			));
			nodes.push(Node {
				span: Span::new(return_type.span.start, param_end_span.end),
				ty: NodeTy::FnDecl {
					return_type,
					ident,
					params,
				},
			});
			return;
		}
	};
	if *token == Token::Semi {
		// We have a declaration.
		walker.push_colour(token_span, SyntaxToken::Punctuation);
		walker.advance();
		nodes.push(Node {
			span: Span::new(return_type.span.start, param_end_span.end),
			ty: NodeTy::FnDecl {
				return_type,
				ident,
				params,
			},
		});
	} else if *token == Token::LBrace {
		// We have a definition.
		let l_brace_span = token_span;
		walker.push_colour(l_brace_span, SyntaxToken::Punctuation);
		walker.advance();
		let body = parse_scope(walker, BRACE_SCOPE, l_brace_span);
		nodes.push(Node {
			span: Span::new(return_type.span.start, body.span.end),
			ty: NodeTy::FnDef {
				return_type,
				ident,
				params,
				body,
			},
		});
	} else {
		// We are missing a `;` for a declaration. We treat this as a declaration since that's the closest match.
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::FnExpectedSemiOrLBraceAfterParams(
				param_end_span.next_single_width(),
			),
		));
		nodes.push(Node {
			span: Span::new(return_type.span.start, param_end_span.end),
			ty: NodeTy::FnDecl {
				return_type,
				ident,
				params,
			},
		});
		seek_next_stmt(walker);
	}
}

/// Parses a subroutine type, associated function, or a subroutine uniform.
///
/// This function assumes that the `subroutine` keyword is not yet consumed.
fn parse_subroutine(walker: &mut Walker, nodes: &mut Vec<Node>, kw_span: Span) {
	walker.push_colour(kw_span, SyntaxToken::Keyword);
	walker.advance();

	let (token, token_span) = match walker.peek() {
		Some(t) => t,
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::SubroutineExpectedTypeFuncUniformAfterKw(
					kw_span.next_single_width(),
				),
			));
			return;
		}
	};

	if *token == Token::Uniform {
		// We have a subroutine uniform definition.
		let uniform_kw_span = token_span;
		walker.push_colour(uniform_kw_span, SyntaxToken::Keyword);
		walker.advance();
		let mut inner = Vec::new();
		try_parse_definition_declaration_expr(
			walker,
			&mut inner,
			vec![],
			false,
		);

		if inner.is_empty() {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::SubroutineExpectedVarDefAfterUniformKw(
					uniform_kw_span.next_single_width(),
				),
			));
		} else {
			let first = inner.remove(0);
			match first.ty {
				NodeTy::VarDef { type_, ident } => {
					nodes.push(Node {
						span: Span::new(kw_span.start, first.span.end),
						ty: NodeTy::SubroutineUniformDef { type_, ident },
					});
				}
				_ => {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SubroutineExpectedVarDefAfterUniformKw(
							uniform_kw_span.next_single_width(),
						),
					));
					nodes.push(first);
				}
			}
			inner.into_iter().for_each(|n| nodes.push(n));
		}
	} else if *token == Token::LParen {
		// We have an associated function definition.
		let l_paren_span = token_span;
		walker.push_colour(l_paren_span, SyntaxToken::Punctuation);
		walker.advance();

		// Look for any subroutine identifiers until we hit a closing `)` parenthesis.
		#[derive(PartialEq)]
		enum Prev {
			None,
			Ident,
			Comma,
			Invalid,
		}
		let mut prev = Prev::None;
		let mut prev_span = l_paren_span;
		let mut associations = Vec::new();
		let r_paren_span = loop {
			let (token, token_span) = match walker.peek() {
				Some(t) => t,
				None => {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SubroutineAssociatedListExpectedRParen(
							prev_span.next_single_width(),
						),
					));
					return;
				}
			};

			match token {
				Token::Comma => {
					walker.push_colour(token_span, SyntaxToken::Punctuation);
					walker.advance();
					if prev == Prev::Comma {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SubroutineAssociatedListExpectedIdentAfterComma(
								Span::new_between(prev_span, token_span),
							),
						));
					} else if prev == Prev::None {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SubroutineAssociatedListExpectedIdentBetweenParenComma(
								Span::new_between(l_paren_span, token_span),
							),
						));
					}
					prev = Prev::Comma;
					prev_span = token_span;
					continue;
				}
				Token::RParen => {
					walker.push_colour(token_span, SyntaxToken::Punctuation);
					walker.advance();
					if prev == Prev::Comma {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SubroutineAssociatedListExpectedIdentAfterComma(
								Span::new_between(prev_span, token_span),
							),
						));
					}
					break token_span;
				}
				Token::Ident(str) => {
					associations.push(Ident {
						name: str.to_owned(),
						span: token_span,
					});
					walker.push_colour(token_span, SyntaxToken::UncheckedIdent);
					walker.advance();
					if prev == Prev::Ident {
						walker.push_syntax_diag(Syntax::Stmt(StmtDiag::SubroutineAssociatedListExpectedCommaAfterIdent(
							prev_span.next_single_width()
						)));
					}
					prev = Prev::Ident;
					prev_span = token_span;
					continue;
				}
				_ => {
					walker.push_colour(token_span, SyntaxToken::Invalid);
					walker.advance();
					prev = Prev::Invalid;
					prev_span = token_span;
				}
			}
		};

		let mut inner = Vec::new();
		try_parse_definition_declaration_expr(
			walker,
			&mut inner,
			vec![],
			false,
		);

		if inner.is_empty() {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::SubroutineExpectedFnDefAfterAssociatedList(
					r_paren_span.next_single_width(),
				),
			));
		} else {
			let first = inner.remove(0);
			match first.ty {
				NodeTy::FnDef {
					return_type,
					ident,
					params,
					body,
				} => {
					nodes.push(Node {
						span: Span::new(kw_span.start, first.span.end),
						ty: NodeTy::SubroutineFnDef {
							associations,
							return_type,
							ident,
							params,
							body: Some(body),
						},
					});
				}
				NodeTy::FnDecl {
					return_type,
					ident,
					params,
				} => {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SubroutineExpectedFnDefAfterAssociatedListFoundDecl(
							first.span,
						),
					));
					nodes.push(Node {
						span: Span::new(kw_span.start, first.span.end),
						ty: NodeTy::SubroutineFnDef {
							associations,
							return_type,
							ident,
							params,
							body: None,
						},
					});
				}
				_ => {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SubroutineExpectedFnDefAfterAssociatedList(
							r_paren_span.next_single_width(),
						),
					));
					nodes.push(first);
				}
			}
		}
		inner.into_iter().for_each(|n| nodes.push(n));
	} else {
		// We have a subroutine type declaration.
		let mut inner = Vec::new();
		try_parse_definition_declaration_expr(
			walker,
			&mut inner,
			vec![],
			false,
		);

		if inner.is_empty() {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::SubroutineExpectedTypeFuncUniformAfterKw(
					kw_span.next_single_width(),
				),
			));
		} else {
			let first = inner.remove(0);
			match first.ty {
				NodeTy::FnDecl {
					return_type,
					ident,
					params,
				} => {
					nodes.push(Node {
						span: Span::new(kw_span.start, first.span.end),
						ty: NodeTy::SubroutineTypeDecl {
							return_type,
							ident,
							params,
						},
					});
				}
				NodeTy::FnDef {
					return_type,
					ident,
					params,
					body,
				} => {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SubroutineMissingAssociationsForFnDef(
							Span::new_between(kw_span, return_type.span),
						),
					));
					nodes.push(Node {
						span: Span::new(kw_span.start, first.span.end),
						ty: NodeTy::SubroutineFnDef {
							associations: vec![],
							return_type,
							ident,
							params,
							body: Some(body),
						},
					});
				}
				NodeTy::VarDef { type_, ident } => {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SubroutineMissingUniformKwForUniformDef(
							Span::new_between(kw_span, type_.span),
						),
					));
					nodes.push(Node {
						span: Span::new(kw_span.start, first.span.end),
						ty: NodeTy::SubroutineUniformDef { type_, ident },
					});
				}
				_ => {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SubroutineExpectedTypeFuncUniformAfterKw(
							kw_span.next_single_width(),
						),
					));
					nodes.push(first);
				}
			}
			inner.into_iter().for_each(|n| nodes.push(n));
		}
	}
}

/// Parses a struct declaration/definition.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_struct(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	qualifiers: Vec<Qualifier>,
	kw_span: Span,
) {
	walker.push_colour(kw_span, SyntaxToken::Keyword);
	walker.advance();

	// Consume the identifier.
	let ident = match expr_parser(
		walker,
		Mode::TakeOneUnit,
		[Token::LBrace, Token::Semi],
	) {
		(Some(e), _, mut semantic, mut colours) => match e.ty {
			ExprTy::Ident(i) => {
				walker.append_colours(&mut colours);
				walker.append_semantic_diags(&mut semantic);
				i
			}
			_ => {
				walker.append_colours(&mut colours);
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::StructExpectedIdentAfterKw(e.span),
				));
				return;
			}
		},
		(None, _, _, _) => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::StructExpectedIdentAfterKw(
					kw_span.next_single_width(),
				),
			));
			return;
		}
	};

	let struct_span_start = if let Some(q) = qualifiers.first() {
		q.span.start
	} else {
		kw_span.start
	};

	// Consume the `{`.
	let (token, token_span) = match walker.peek() {
		Some(t) => t,
		None => {
			// We don't create a struct declaration because it would result in two errors that would reduce
			// clarity.
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::StructExpectedLBraceAfterIdent(
					ident.span.next_single_width(),
				),
			));
			return;
		}
	};
	let l_brace_span = if *token == Token::LBrace {
		walker.push_colour(token_span, SyntaxToken::Punctuation);
		walker.advance();
		token_span
	} else if *token == Token::Semi {
		// We have a declaration, (which is illegal).
		let span = Span::new(struct_span_start, token_span.end);
		walker.push_colour(token_span, SyntaxToken::Punctuation);
		walker.push_syntax_diag(Syntax::Stmt(StmtDiag::StructDeclIsIllegal(
			span,
		)));
		walker.advance();
		nodes.push(Node {
			span,
			ty: NodeTy::StructDecl { qualifiers, ident },
		});
		return;
	} else {
		// We don't create a struct declaration because it would result in two errors that would reduce clarity.
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::StructExpectedLBraceAfterIdent(
				ident.span.next_single_width(),
			),
		));
		return;
	};

	// Parse the contents of the body.
	let body = parse_scope(walker, BRACE_SCOPE, l_brace_span);
	if body.contents.is_empty() {
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::StructExpectedAtLeastOneStmtInBody(body.span),
		));
	}
	for stmt in &body.contents {
		match &stmt.ty {
			NodeTy::VarDef { .. }
			| NodeTy::VarDefInit { .. }
			| NodeTy::VarDefs(_)
			| NodeTy::VarDefInits(_, _) => {}
			_ => {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::StructInvalidStmtInBody(stmt.span),
				));
			}
		}
	}

	// Look for an optional instance identifier.
	let instance = match expr_parser(walker, Mode::TakeOneUnit, [Token::Semi]) {
		(Some(e), _, mut semantic, mut colours) => match e.ty {
			ExprTy::Ident(i) => {
				walker.append_colours(&mut colours);
				walker.append_semantic_diags(&mut semantic);
				Omittable::Some(i)
			}
			_ => {
				walker.append_colours(&mut colours);
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::StructExpectedInstanceOrSemiAfterBody(e.span),
				));
				nodes.push(Node {
					span: Span::new(struct_span_start, body.span.end),
					ty: NodeTy::StructDef {
						qualifiers,
						ident,
						body,
						instance: Omittable::None,
					},
				});
				return;
			}
		},
		_ => Omittable::None,
	};

	// Consume the `;` to end the statement.
	let semi_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::Semi {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				Some(span)
			} else {
				None
			}
		}
		None => None,
	};
	if semi_span.is_none() {
		if let Omittable::Some(ref i) = instance {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::StructExpectedSemiAfterBodyOrInstance(
					i.span.next_single_width(),
				),
			));
		} else {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::StructExpectedInstanceOrSemiAfterBody(
					body.span.next_single_width(),
				),
			));
		}
	}

	nodes.push(Node {
		span: Span::new(
			struct_span_start,
			if let Some(semi_span) = semi_span {
				semi_span.end
			} else {
				if let Omittable::Some(ref i) = instance {
					i.span.end
				} else {
					body.span.end
				}
			},
		),
		ty: NodeTy::StructDef {
			qualifiers,
			ident,
			body,
			instance,
		},
	});
}

/// Parses an if statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_if(walker: &mut Walker, nodes: &mut Vec<Node>, kw_span: Span) {
	let mut branches = Vec::new();
	let mut first_iter = true;
	// On the first iteration of this loop, the current token is guaranteed to be `Token::If`.
	loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				nodes.push(Node {
					span: Span::new(kw_span.start, walker.get_last_span().end),
					ty: NodeTy::If(branches),
				});
				return;
			}
		};

		let else_kw_span = if *token != Token::Else && !first_iter {
			// We've found a token that is not `else`, which means we've finished the current if statement.
			nodes.push(Node {
				span: Span::new(
					kw_span.start,
					if let Some(branch) = branches.last() {
						branch.span.end
					} else {
						kw_span.end
					},
				),
				ty: NodeTy::If(branches),
			});
			return;
		} else if *token == Token::If && first_iter {
			// In the first iteration this variable is ignored. This is just to prevent divergence of branches
			// which would require a different overall parsing algorithm.
			token_span
		} else {
			// Consume the `else` keyword.
			walker.push_colour(token_span, SyntaxToken::Keyword);
			walker.advance();
			token_span
		};

		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We have an else keyword followed by nothing.
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::IfExpectedIfOrLBraceOrStmtAfterElseKw(
						walker.last_span.next_single_width(),
					),
				));
				nodes.push(Node {
					span: Span::new(kw_span.start, walker.get_last_span().end),
					ty: NodeTy::If(branches),
				});
				return;
			}
		};

		if *token == Token::If {
			let if_kw_span = token_span;
			walker.push_colour(if_kw_span, SyntaxToken::Keyword);
			walker.advance();

			// Consume the `(`.
			let l_paren_span = match walker.peek() {
				Some((token, span)) => {
					if *token == Token::LParen {
						walker.push_colour(span, SyntaxToken::Punctuation);
						walker.advance();
						Some(span)
					} else {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::IfExpectedLParenAfterKw(
								if_kw_span.next_single_width(),
							),
						));
						None
					}
				}
				None => {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::IfExpectedLParenAfterKw(
							if_kw_span.next_single_width(),
						),
					));
					branches.push(IfBranch {
						span: if first_iter {
							if_kw_span
						} else {
							Span::new(else_kw_span.start, if_kw_span.end)
						},
						condition: if first_iter {
							(IfCondition::If(None), if_kw_span)
						} else {
							(
								IfCondition::ElseIf(None),
								Span::new(else_kw_span.start, if_kw_span.end),
							)
						},
						body: None,
					});
					nodes.push(Node {
						span: Span::new(
							kw_span.start,
							walker.get_last_span().end,
						),
						ty: NodeTy::If(branches),
					});
					return;
				}
			};

			// Consume the condition expression.
			let cond_expr = match expr_parser(
				walker,
				Mode::Default,
				[Token::RParen, Token::LBrace],
			) {
				(Some(e), mut syntax, mut semantic, mut colours) => {
					walker.append_colours(&mut colours);
					walker.append_syntax_diags(&mut syntax);
					walker.append_semantic_diags(&mut semantic);
					Some(e)
				}
				(None, _, _, _) => {
					if let Some(l_paren_span) = l_paren_span {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::IfExpectedExprAfterLParen(
								l_paren_span.next_single_width(),
							),
						));
					}
					None
				}
			};

			// Consume the `)`.
			let r_paren_span = match walker.peek() {
				Some((token, span)) => {
					if *token == Token::RParen {
						walker.push_colour(span, SyntaxToken::Punctuation);
						walker.advance();
						Some(span)
					} else {
						if let Some(ref cond_expr) = cond_expr {
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::IfExpectedRParenAfterExpr(
									cond_expr.span.next_single_width(),
								),
							));
						}
						None
					}
				}
				None => {
					if let Some(ref cond_expr) = cond_expr {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::IfExpectedRParenAfterExpr(
								cond_expr.span.next_single_width(),
							),
						));
					}
					let span = Span::new(
						if first_iter {
							if_kw_span.start
						} else {
							else_kw_span.start
						},
						if let Some(ref cond_expr) = cond_expr {
							cond_expr.span.end
						} else if let Some(l_paren_span) = l_paren_span {
							l_paren_span.end
						} else {
							if_kw_span.end
						},
					);
					branches.push(IfBranch {
						span,
						condition: (
							if first_iter {
								IfCondition::If(cond_expr)
							} else {
								IfCondition::ElseIf(None)
							},
							span,
						),
						body: None,
					});
					nodes.push(Node {
						span: Span::new(
							kw_span.start,
							walker.get_last_span().end,
						),
						ty: NodeTy::If(branches),
					});
					return;
				}
			};

			// Consume either the `{` for a multi-line if body or a statement for a single-statement if body.
			match walker.peek() {
				Some((token, token_span)) => {
					if *token == Token::LBrace {
						// We have a multi-line body.
						walker
							.push_colour(token_span, SyntaxToken::Punctuation);
						walker.advance();
						let body = parse_scope(walker, BRACE_SCOPE, token_span);
						let span = Span::new(
							if first_iter {
								if_kw_span.start
							} else {
								else_kw_span.start
							},
							if let Some(r_paren_span) = r_paren_span {
								r_paren_span.end
							} else if let Some(ref cond_expr) = cond_expr {
								cond_expr.span.end
							} else if let Some(l_paren_span) = l_paren_span {
								l_paren_span.end
							} else {
								if_kw_span.end
							},
						);
						branches.push(IfBranch {
							span: Span::new(if_kw_span.start, body.span.end),
							condition: (
								if first_iter {
									IfCondition::If(cond_expr)
								} else {
									IfCondition::ElseIf(cond_expr)
								},
								span,
							),
							body: Some(body),
						});
					} else {
						// We don't have a multi-line body, so we attempt to parse a single statement.
						let mut stmts = Vec::new();
						parse_stmt(walker, &mut stmts);

						let body = if stmts.is_empty() {
							if let Some(r_paren_span) = r_paren_span {
								walker.push_syntax_diag(Syntax::Stmt(
									StmtDiag::IfExpectedLBraceOrStmtAfterRParen(
										r_paren_span,
									),
								));
							}
							None
						} else {
							let stmt = stmts.remove(0);
							let body = Scope {
								span: stmt.span,
								contents: vec![stmt],
							};
							Some(body)
						};

						let span = Span::new(
							if first_iter {
								if_kw_span.start
							} else {
								else_kw_span.start
							},
							if let Some(r_paren_span) = r_paren_span {
								r_paren_span.end
							} else if let Some(ref cond_expr) = cond_expr {
								cond_expr.span.end
							} else if let Some(l_paren_span) = l_paren_span {
								l_paren_span.end
							} else {
								if_kw_span.end
							},
						);
						branches.push(IfBranch {
							span: Span::new(
								if_kw_span.start,
								if let Some(ref body) = body {
									body.span.end
								} else {
									span.end
								},
							),
							condition: (
								if first_iter {
									IfCondition::If(cond_expr)
								} else {
									IfCondition::ElseIf(cond_expr)
								},
								span,
							),
							body,
						});
					}
				}
				None => {
					// We have a if-header but no associated body but we've reached the EOF.
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::IfExpectedLBraceOrStmtAfterRParen(
							walker.get_last_span().next_single_width(),
						),
					));
					let span = Span::new(
						if first_iter {
							if_kw_span.start
						} else {
							else_kw_span.start
						},
						if let Some(r_paren_span) = r_paren_span {
							r_paren_span.end
						} else if let Some(ref cond_expr) = cond_expr {
							cond_expr.span.end
						} else if let Some(l_paren_span) = l_paren_span {
							l_paren_span.end
						} else {
							if_kw_span.end
						},
					);
					branches.push(IfBranch {
						span,
						condition: (
							if first_iter {
								IfCondition::If(cond_expr)
							} else {
								IfCondition::ElseIf(cond_expr)
							},
							span,
						),
						body: None,
					});
					nodes.push(Node {
						span: Span::new(
							kw_span.start,
							walker.get_last_span().end,
						),
						ty: NodeTy::If(branches),
					});
					return;
				}
			}
		} else {
			// Consume either the `{` for a multi-line if body or a statement for a single-statement if body.
			match walker.peek() {
				Some((token, token_span)) => {
					if *token == Token::LBrace {
						// We have a multi-line body.
						walker
							.push_colour(token_span, SyntaxToken::Punctuation);
						walker.advance();
						let body = parse_scope(walker, BRACE_SCOPE, token_span);
						branches.push(IfBranch {
							span: Span::new(else_kw_span.start, body.span.end),
							condition: (IfCondition::Else, else_kw_span),
							body: Some(body),
						});
					} else {
						// We don't have a multi-line body, so we attempt to parse a single statement.
					}
				}
				None => {
					// We have one else-header but no associated body.
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::IfExpectedLBraceOrStmtAfterRParen(
							walker.get_last_span().next_single_width(),
						),
					));
					branches.push(IfBranch {
						span: else_kw_span,
						condition: (IfCondition::Else, else_kw_span),
						body: None,
					});
					nodes.push(Node {
						span: Span::new(
							kw_span.start,
							walker.get_last_span().end,
						),
						ty: NodeTy::If(branches),
					});
					return;
				}
			}
		}

		first_iter = false;
	}
}

/// Parses a switch statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_switch(walker: &mut Walker, nodes: &mut Vec<Node>, kw_span: Span) {
	walker.push_colour(kw_span, SyntaxToken::Keyword);
	walker.advance();

	// Consume the `(`.
	let l_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LParen {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				Some(span)
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::SwitchExpectedLParenAfterKw(
						kw_span.next_single_width(),
					),
				));
				None
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::SwitchExpectedLParenAfterKw(
					kw_span.next_single_width(),
				),
			));
			return;
		}
	};

	// Consume the condition expression.
	let cond_expr = match expr_parser(
		walker,
		Mode::Default,
		[Token::RParen, Token::LBrace],
	) {
		(Some(e), mut syntax, mut semantic, mut colours) => {
			walker.append_colours(&mut colours);
			walker.append_syntax_diags(&mut syntax);
			walker.append_semantic_diags(&mut semantic);
			Some(e)
		}
		(None, _, _, _) => {
			if let Some(l_paren_span) = l_paren_span {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::SwitchExpectedExprAfterLParen(
						l_paren_span.next_single_width(),
					),
				));
			}
			None
		}
	};

	// Consume the `)`.
	let r_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::RParen {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				Some(span)
			} else {
				if let Some(ref cond_expr) = cond_expr {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SwitchExpectedRParenAfterExpr(
							cond_expr.span.next_single_width(),
						),
					));
				}
				None
			}
		}
		None => {
			if let Some(ref cond_expr) = cond_expr {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::SwitchExpectedRParenAfterExpr(
						cond_expr.span.next_single_width(),
					),
				));
			}
			return;
		}
	};

	// Consume the `{`.
	let l_brace_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LBrace {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				span
			} else {
				if let Some(r_paren_span) = r_paren_span {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::SwitchExpectedLBraceAfterCond(
							r_paren_span.next_single_width(),
						),
					));
				}
				nodes.push(Node {
					span: Span::new(
						kw_span.start,
						if let Some(r_paren_span) = r_paren_span {
							r_paren_span.end
						} else if let Some(ref cond_expr) = cond_expr {
							cond_expr.span.end
						} else if let Some(l_paren_span) = l_paren_span {
							l_paren_span.end
						} else {
							kw_span.end
						},
					),
					ty: NodeTy::Switch {
						cond: cond_expr,
						cases: vec![],
					},
				});
				return;
			}
		}
		None => {
			if let Some(r_paren_span) = r_paren_span {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::SwitchExpectedLBraceAfterCond(
						r_paren_span.next_single_width(),
					),
				));
			}
			nodes.push(Node {
				span: Span::new(kw_span.start, walker.get_last_span().end),
				ty: NodeTy::Switch {
					cond: cond_expr,
					cases: vec![],
				},
			});
			return;
		}
	};

	// Check if the body is empty.
	match walker.peek() {
		Some((token, token_span)) => {
			if *token == Token::RBrace {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::SwitchFoundEmptyBody(Span::new(
						l_brace_span.start,
						token_span.end,
					)),
				));
				nodes.push(Node {
					span: Span::new(kw_span.start, token_span.end),
					ty: NodeTy::Switch {
						cond: cond_expr,
						cases: vec![],
					},
				});
				return;
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ScopeMissingRBrace(
					l_brace_span,
					walker.get_last_span().next_single_width(),
				),
			));
			nodes.push(Node {
				span: Span::new(kw_span.start, walker.get_last_span().end),
				ty: NodeTy::Switch {
					cond: cond_expr,
					cases: vec![],
				},
			});
			return;
		}
	}

	// Consume cases until we reach the end of the body.
	let mut cases = Vec::new();
	loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ScopeMissingRBrace(
						l_brace_span,
						walker.get_last_span().next_single_width(),
					),
				));
				nodes.push(Node {
					span: Span::new(kw_span.start, walker.get_last_span().end),
					ty: NodeTy::Switch {
						cond: cond_expr,
						cases,
					},
				});
				return;
			}
		};

		match token {
			Token::Case => {
				let case_kw_span = token_span;
				walker.push_colour(case_kw_span, SyntaxToken::Keyword);
				walker.advance();

				// Consume the expression.
				let expr =
					match expr_parser(walker, Mode::Default, [Token::Colon]) {
						(Some(e), mut syntax, mut semantic, mut colours) => {
							walker.append_colours(&mut colours);
							walker.append_syntax_diags(&mut syntax);
							walker.append_semantic_diags(&mut semantic);
							Some(e)
						}
						(None, _, _, _) => {
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::SwitchExpectedExprAfterCaseKw(
									case_kw_span.next_single_width(),
								),
							));
							None
						}
					};

				// Consume the `:`.
				let colon_span = match walker.peek() {
					Some((token, token_span)) => {
						if *token == Token::Colon {
							walker.push_colour(
								token_span,
								SyntaxToken::Punctuation,
							);
							walker.advance();
							Some(token_span)
						} else {
							if let Some(ref expr) = expr {
								walker.push_syntax_diag(Syntax::Stmt(
									StmtDiag::SwitchExpectedColonAfterCaseExpr(
										expr.span.next_single_width(),
									),
								));
							}
							None
						}
					}
					None => {
						// We don't have a complete case but we've reached the EOF.
						if let Some(ref expr) = expr {
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::SwitchExpectedColonAfterCaseExpr(
									expr.span.next_single_width(),
								),
							));
						}
						cases.push(SwitchCase {
							span: Span::new(
								case_kw_span.start,
								walker.get_last_span().end,
							),
							expr: Either::Left(expr),
							body: None,
						});
						nodes.push(Node {
							span: Span::new(
								kw_span.start,
								walker.get_last_span().end,
							),
							ty: NodeTy::Switch {
								cond: cond_expr,
								cases,
							},
						});
						return;
					}
				};

				// Consume the body of the case.
				let body = parse_scope(
					walker,
					SWITCH_CASE_SCOPE,
					colon_span.unwrap_or(if let Some(ref expr) = expr {
						expr.span
					} else {
						case_kw_span
					}),
				);
				cases.push(SwitchCase {
					span: Span::new(case_kw_span.start, body.span.end),
					expr: Either::Left(expr),
					body: Some(body),
				});
			}
			Token::Default => {
				let default_kw_span = token_span;
				walker.push_colour(default_kw_span, SyntaxToken::Keyword);
				walker.advance();

				// Consume the `:`.
				let colon_span = match walker.peek() {
					Some((token, token_span)) => {
						if *token == Token::Colon {
							walker.push_colour(
								token_span,
								SyntaxToken::Punctuation,
							);
							walker.advance();
							Some(token_span)
						} else {
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::SwitchExpectedColonAfterDefaultKw(
									default_kw_span.next_single_width(),
								),
							));
							None
						}
					}
					None => {
						// We don't have a complete case but we've reached the EOF.
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::SwitchExpectedColonAfterDefaultKw(
								default_kw_span.next_single_width(),
							),
						));
						cases.push(SwitchCase {
							span: default_kw_span,
							expr: Either::Right(()),
							body: None,
						});
						nodes.push(Node {
							span: Span::new(
								kw_span.start,
								walker.get_last_span().end,
							),
							ty: NodeTy::Switch {
								cond: cond_expr,
								cases,
							},
						});
						return;
					}
				};

				// Consume the body of the case.
				let body = parse_scope(
					walker,
					SWITCH_CASE_SCOPE,
					colon_span.unwrap_or(default_kw_span.end_zero_width()),
				);
				cases.push(SwitchCase {
					span: Span::new(default_kw_span.start, body.span.end),
					expr: Either::Right(()),
					body: Some(body),
				});
			}
			Token::RBrace => {
				// If this branch is triggered, this `}` is closing the entire body of the switch statement. In the
				// following example:
				//
				// switch (true) {
				//     default: {
				//         /*...*/
				//     }
				// }
				//
				// the first `}` will be consumed by the `parse_scope()` function of the default case body, whilst
				// the second will be consumed by this branch. In the following example:
				//
				// switch (true) {
				//     default:
				//         /*...*/
				// }
				//
				// The `}` will close the body of the default case but it won't be consumed, and hence it will be
				// consumed by this branch.
				walker.push_colour(token_span, SyntaxToken::Punctuation);
				walker.advance();
				nodes.push(Node {
					span: Span::new(kw_span.start, token_span.end),
					ty: NodeTy::Switch {
						cond: cond_expr,
						cases,
					},
				});
				return;
			}
			_ => {
				// We have a token which cannot begin a case, nor can finish the switch body. We consume tokens
				// until we hit something recognizable.
				let invalid_span_start = token_span.start;
				let mut invalid_span_end = token_span.end;
				loop {
					match walker.peek() {
						Some((token, token_span)) => {
							if *token == Token::Case
								|| *token == Token::Default || *token
								== Token::RBrace
							{
								// We don't consume the token because the next iteration of the main loop will deal
								// with it appropriately.
								walker.push_syntax_diag(Syntax::Stmt(StmtDiag::SwitchExpectedCaseOrDefaultKwOrEnd(
									Span::new(invalid_span_start, invalid_span_end)
								)));
								break;
							} else {
								invalid_span_end = token_span.end;
								walker.push_colour(
									token_span,
									token.non_semantic_colour(),
								);
								walker.advance();
							}
						}
						None => {
							// We haven't yet hit anything recognizable but we've reached the EOF.
							walker.push_syntax_diag(Syntax::Stmt(
								StmtDiag::SwitchExpectedCaseOrDefaultKwOrEnd(
									Span::new(
										invalid_span_start,
										walker.get_last_span().end,
									),
								),
							));
							nodes.push(Node {
								span: Span::new(
									kw_span.start,
									walker.get_last_span().end,
								),
								ty: NodeTy::Switch {
									cond: cond_expr,
									cases,
								},
							});
							return;
						}
					}
				}
			}
		}
	}
}

/// Parses a for loop statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_for_loop(walker: &mut Walker, nodes: &mut Vec<Node>, kw_span: Span) {
	walker.push_colour(kw_span, SyntaxToken::Keyword);
	walker.advance();

	// Consume the `(`.
	let l_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LParen {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				Some(span)
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ForExpectedLParenAfterKw(
						kw_span.next_single_width(),
					),
				));
				None
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ForExpectedLParenAfterKw(kw_span.next_single_width()),
			));
			return;
		}
	};

	// Consume the "expressions" (actually expression/declaration statements).
	let mut init: Option<Node> = None;
	let mut cond: Option<Node> = None;
	let mut inc: Option<Node> = None;
	let mut counter = 0;
	let r_paren_span = 'outer: loop {
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We have not encountered a `)` yet.
				let span = Span::new(
					kw_span.start,
					if let Some(ref inc) = inc {
						inc.span.end
					} else if let Some(ref cond) = cond {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::ForExpectedIncStmt(
								cond.span.next_single_width(),
							),
						));
						cond.span.end
					} else if let Some(ref init) = init {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::ForExpectedCondStmt(
								init.span.next_single_width(),
							),
						));
						init.span.end
					} else if let Some(l_paren_span) = l_paren_span {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::ForExpectedInitStmt(
								l_paren_span.next_single_width(),
							),
						));
						l_paren_span.end
					} else {
						kw_span.end
					},
				);
				nodes.push(Node {
					span,
					ty: NodeTy::For {
						init: init.map(|n| Box::from(n)),
						cond: cond.map(|n| Box::from(n)),
						inc: inc.map(|n| Box::from(n)),
						body: None,
					},
				});
				return;
			}
		};

		match token {
			Token::RParen => {
				if counter < 3 {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ForExpected3Stmts(
							token_span.previous_single_width(),
						),
					));
				}
				walker.push_colour(token_span, SyntaxToken::Punctuation);
				walker.advance();
				break token_span;
			}
			_ => {
				if counter == 3 {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::ForExpectedRParenAfterStmts(
							inc.as_ref().unwrap().span.next_single_width(),
						),
					));

					walker.push_colour(token_span, SyntaxToken::Invalid);
					walker.advance();

					loop {
						match walker.peek() {
							Some((token, span)) => {
								if *token == Token::RParen {
									walker.push_colour(
										span,
										SyntaxToken::Punctuation,
									);
									walker.advance();
									break 'outer span;
								} else {
									walker.push_colour(
										span,
										SyntaxToken::Invalid,
									);
									walker.advance();
								}
							}
							None => break,
						}
					}

					nodes.push(Node {
						span: Span::new(
							kw_span.start,
							inc.as_ref().unwrap().span.end,
						),
						ty: NodeTy::For {
							init: init.map(|n| Box::from(n)),
							cond: cond.map(|n| Box::from(n)),
							inc: inc.map(|n| Box::from(n)),
							body: None,
						},
					});
					return;
				}
			}
		}

		let qualifiers = try_parse_qualifiers(walker);
		let mut stmt = Vec::new();
		try_parse_definition_declaration_expr(
			walker,
			&mut stmt,
			qualifiers,
			counter == 2,
		);

		if !stmt.is_empty() {
			if counter == 0 {
				init = Some(stmt.remove(0));
			} else if counter == 1 {
				cond = Some(stmt.remove(0));
			} else if counter == 2 {
				inc = Some(stmt.remove(0));
			}
			counter += 1;
		}
	};

	// Consume the `{`.
	let l_brace_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LBrace {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				span
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ForExpectedLBraceAfterHeader(
						r_paren_span.next_single_width(),
					),
				));
				nodes.push(Node {
					span: Span::new(kw_span.start, r_paren_span.end),
					ty: NodeTy::For {
						init: init.map(|n| Box::from(n)),
						cond: cond.map(|n| Box::from(n)),
						inc: inc.map(|n| Box::from(n)),
						body: None,
					},
				});
				return;
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ForExpectedLBraceAfterHeader(
					r_paren_span.next_single_width(),
				),
			));
			nodes.push(Node {
				span: Span::new(kw_span.start, r_paren_span.end),
				ty: NodeTy::For {
					init: init.map(|n| Box::from(n)),
					cond: cond.map(|n| Box::from(n)),
					inc: inc.map(|n| Box::from(n)),
					body: None,
				},
			});
			return;
		}
	};

	// Consume the body.
	let body = parse_scope(walker, BRACE_SCOPE, l_brace_span);
	nodes.push(Node {
		span: Span::new(kw_span.start, body.span.end),
		ty: NodeTy::For {
			init: init.map(|n| Box::from(n)),
			cond: cond.map(|n| Box::from(n)),
			inc: inc.map(|n| Box::from(n)),
			body: Some(body),
		},
	});
}

/// Parses a while loop statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_while_loop(walker: &mut Walker, nodes: &mut Vec<Node>, kw_span: Span) {
	walker.push_colour(kw_span, SyntaxToken::Keyword);
	walker.advance();

	// Consume the `(`.
	let l_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LParen {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				Some(span)
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedLParenAfterKw(
						kw_span.next_single_width(),
					),
				));
				None
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::WhileExpectedLParenAfterKw(
					kw_span.next_single_width(),
				),
			));
			return;
		}
	};

	// Consume the condition expression.
	let cond_expr = match expr_parser(
		walker,
		Mode::Default,
		[Token::RParen, Token::Semi],
	) {
		(Some(e), mut syntax, mut semantic, mut colours) => {
			walker.append_colours(&mut colours);
			walker.append_syntax_diags(&mut syntax);
			walker.append_semantic_diags(&mut semantic);
			Some(e)
		}
		(None, _, _, _) => {
			if let Some(l_paren_span) = l_paren_span {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedExprAfterLParen(
						l_paren_span.next_single_width(),
					),
				));
			}
			None
		}
	};

	// Consume the `)`.
	let r_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::RParen {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				Some(span)
			} else {
				if let Some(ref cond_expr) = cond_expr {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::WhileExpectedRParenAfterExpr(
							cond_expr.span.next_single_width(),
						),
					));
				}
				None
			}
		}
		None => {
			if let Some(ref cond_expr) = cond_expr {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedRParenAfterExpr(
						cond_expr.span.next_single_width(),
					),
				));
			}
			return;
		}
	};

	// Consume the `{`.
	let l_brace_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LBrace {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				span
			} else {
				if let Some(r_paren_span) = r_paren_span {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::WhileExpectedLBraceAfterCond(
							r_paren_span.next_single_width(),
						),
					));
				}
				return;
			}
		}
		None => {
			if let Some(r_paren_span) = r_paren_span {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedLBraceAfterCond(
						r_paren_span.next_single_width(),
					),
				));
			}
			return;
		}
	};

	// Parse the body.
	let body = parse_scope(walker, BRACE_SCOPE, l_brace_span);
	nodes.push(Node {
		span: Span::new(kw_span.start, body.span.end),
		ty: NodeTy::While {
			cond: cond_expr,
			body,
		},
	});
}

/// Parses a do-while loop statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_do_while_loop(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	kw_span: Span,
) {
	walker.push_colour(kw_span, SyntaxToken::Keyword);
	walker.advance();

	// Consume the `{`.
	let l_brace_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LBrace {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				span
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::DoWhileExpectedLBraceAfterKw(
						kw_span.next_single_width(),
					),
				));
				return;
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::DoWhileExpectedLBraceAfterKw(
					kw_span.next_single_width(),
				),
			));
			return;
		}
	};

	// Parse the body.
	let body = parse_scope(walker, BRACE_SCOPE, l_brace_span);

	// Consume the `while` keyword.
	let while_kw_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::While {
				walker.push_colour(span, SyntaxToken::Keyword);
				walker.advance();
				span
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::DoWhileExpectedWhileAfterBody(
						body.span.next_single_width(),
					),
				));
				nodes.push(Node {
					span: Span::new(kw_span.start, body.span.end),
					ty: NodeTy::DoWhile { body, cond: None },
				});
				return;
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::DoWhileExpectedWhileAfterBody(
					body.span.next_single_width(),
				),
			));
			nodes.push(Node {
				span: Span::new(kw_span.start, body.span.end),
				ty: NodeTy::DoWhile { body, cond: None },
			});
			return;
		}
	};

	// Consume the `(`.
	let l_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::LParen {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				Some(span)
			} else {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedLParenAfterKw(
						while_kw_span.next_single_width(),
					),
				));
				None
			}
		}
		None => {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::WhileExpectedLParenAfterKw(
					while_kw_span.next_single_width(),
				),
			));
			nodes.push(Node {
				span: Span::new(kw_span.start, while_kw_span.end),
				ty: NodeTy::DoWhile { body, cond: None },
			});
			return;
		}
	};

	// Consume the condition expression.
	let cond_expr = match expr_parser(
		walker,
		Mode::Default,
		[Token::RParen, Token::Semi],
	) {
		(Some(e), mut syntax, mut semantic, mut colours) => {
			walker.append_colours(&mut colours);
			walker.append_syntax_diags(&mut syntax);
			walker.append_semantic_diags(&mut semantic);
			Some(e)
		}
		(None, _, _, _) => {
			if let Some(l_paren_span) = l_paren_span {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedExprAfterLParen(
						l_paren_span.next_single_width(),
					),
				));
			}
			None
		}
	};

	// Consume the `)`.
	let r_paren_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::RParen {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				Some(span)
			} else {
				if let Some(ref cond_expr) = cond_expr {
					walker.push_syntax_diag(Syntax::Stmt(
						StmtDiag::WhileExpectedRParenAfterExpr(
							cond_expr.span.next_single_width(),
						),
					));
				}
				None
			}
		}
		None => {
			if let Some(ref cond_expr) = cond_expr {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::WhileExpectedRParenAfterExpr(
						cond_expr.span.next_single_width(),
					),
				));
			}
			nodes.push(Node {
				span: Span::new(kw_span.start, while_kw_span.end),
				ty: NodeTy::DoWhile {
					body,
					cond: cond_expr,
				},
			});
			return;
		}
	};

	// Consume the `;` to end the statement.
	let semi_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::Semi {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				span
			} else {
				let span = if let Some(r_paren_span) = r_paren_span {
					r_paren_span
				} else if let Some(ref expr) = cond_expr {
					expr.span
				} else if let Some(l_paren_span) = l_paren_span {
					l_paren_span
				} else {
					while_kw_span
				};
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::DoWhileExpectedSemiAfterRParen(
						span.next_single_width(),
					),
				));
				nodes.push(Node {
					span,
					ty: NodeTy::DoWhile {
						body,
						cond: cond_expr,
					},
				});
				return;
			}
		}
		None => {
			let span = if let Some(r_paren_span) = r_paren_span {
				r_paren_span
			} else if let Some(ref expr) = cond_expr {
				expr.span
			} else if let Some(l_paren_span) = l_paren_span {
				l_paren_span
			} else {
				while_kw_span
			};
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::DoWhileExpectedSemiAfterRParen(
					span.next_single_width(),
				),
			));
			nodes.push(Node {
				span,
				ty: NodeTy::DoWhile {
					body,
					cond: cond_expr,
				},
			});
			return;
		}
	};

	nodes.push(Node {
		span: Span::new(kw_span.start, semi_span.end),
		ty: NodeTy::DoWhile {
			cond: cond_expr,
			body,
		},
	});
}

/// Parses a break/continue/discard statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_break_continue_discard(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	kw_span: Span,
	ty: impl FnOnce() -> NodeTy,
	error: impl FnOnce(Span) -> Syntax,
) {
	walker.push_colour(kw_span, SyntaxToken::Keyword);
	walker.advance();

	// Consume the `;` to end the statement.
	let semi_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::Semi {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				Some(span)
			} else {
				None
			}
		}
		None => None,
	};
	if semi_span.is_none() {
		walker.push_syntax_diag(error(kw_span.next_single_width()));
	}

	nodes.push(Node {
		span: Span::new(
			kw_span.start,
			if let Some(s) = semi_span {
				s.end
			} else {
				kw_span.end
			},
		),
		ty: ty(),
	});
}

/// Parses a return statement.
///
/// This function assumes that the keyword is not yet consumed.
fn parse_return(walker: &mut Walker, nodes: &mut Vec<Node>, kw_span: Span) {
	walker.push_colour(kw_span, SyntaxToken::Keyword);
	walker.advance();

	// Look for the optional return value expression.
	let return_expr = match expr_parser(walker, Mode::Default, [Token::Semi]) {
		(Some(expr), mut syntax, mut semantic, mut colours) => {
			walker.append_colours(&mut colours);
			walker.append_syntax_diags(&mut syntax);
			walker.append_semantic_diags(&mut semantic);
			Omittable::Some(expr)
		}
		(None, _, _, _) => Omittable::None,
	};

	// Consume the `;` to end the statement.
	let semi_span = match walker.peek() {
		Some((token, span)) => {
			if *token == Token::Semi {
				walker.push_colour(span, SyntaxToken::Punctuation);
				walker.advance();
				Some(span)
			} else {
				None
			}
		}
		None => None,
	};
	if semi_span.is_none() {
		if let Omittable::Some(ref return_expr) = return_expr {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ReturnExpectedSemiAfterExpr(
					return_expr.span.next_single_width(),
				),
			));
		} else {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ReturnExpectedSemiOrExprAfterKw(
					kw_span.next_single_width(),
				),
			));
		}
	}

	nodes.push(Node {
		span: Span::new(
			kw_span.start,
			if let Some(s) = semi_span {
				s.end
			} else {
				kw_span.end
			},
		),
		ty: NodeTy::Return { value: return_expr },
	});
}

/// Parses a preprocessor directive.
///
/// This function assumes that the directive has not yet been consumed.
fn parse_directive(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	stream: PreprocStream,
	dir_span: Span,
) {
	use crate::lexer::preprocessor::{self, DefineToken, UndefToken};

	match stream {
		PreprocStream::Empty => {
			walker.push_colour(dir_span, SyntaxToken::Directive);
			walker.push_semantic_diag(Semantic::EmptyDirective(dir_span));
			nodes.push(Node {
				span: dir_span,
				ty: NodeTy::EmptyDirective,
			});
		}
		PreprocStream::Custom { kw, .. } => {
			walker.push_colour(dir_span, SyntaxToken::Directive);
			walker.push_syntax_diag(Syntax::FoundIllegalPreproc(
				dir_span,
				Some(kw),
			));
		}
		PreprocStream::Invalid { .. } => {
			walker.push_colour(dir_span, SyntaxToken::Directive);
			walker
				.push_syntax_diag(Syntax::FoundIllegalPreproc(dir_span, None));
		}
		PreprocStream::Version { kw, tokens } => {
			parse_version_directive(walker, nodes, dir_span, kw, tokens)
		}
		PreprocStream::Extension { kw, tokens } => {
			parse_extension_directive(walker, nodes, dir_span, kw, tokens)
		}
		PreprocStream::Line { kw, tokens } => {
			parse_line_directive(walker, nodes, dir_span, kw, tokens)
		}
		PreprocStream::Define {
			kw: kw_span,
			mut ident_tokens,
			body_tokens,
		} => {
			walker.push_colour(dir_span.first_char(), SyntaxToken::Directive);
			walker.push_colour(kw_span, SyntaxToken::Directive);

			if ident_tokens.is_empty() {
				// We have a macro that's missing a name.

				walker.push_syntax_diag(Syntax::PreprocDefine(
					PreprocDefineDiag::DefineExpectedMacroName(
						kw_span.next_single_width(),
					),
				));
				body_tokens.iter().for_each(|(_, s)| {
					walker.push_colour(*s, SyntaxToken::Invalid)
				});
			} else if ident_tokens.len() == 1 {
				// We have an object-like macro.

				let ident = match ident_tokens.remove(0) {
					(DefineToken::Ident(s), span) => {
						walker.push_colour(span, SyntaxToken::ObjectMacro);
						(s, span)
					}
					_ => unreachable!(),
				};

				// Since object-like macros don't have parameters, we can perform the concatenation right here
				// since we know the contents of the macro body will never change.
				let (body_tokens, mut diags) =
					preprocessor::concat_macro_body(body_tokens);
				walker.append_syntax_diags(&mut diags);
				body_tokens.iter().for_each(|(t, s)| {
					walker.push_colour(*s, t.non_semantic_colour())
				});

				walker.register_macro(
					ident.0.clone(),
					ident.1,
					Macro::Object(body_tokens.clone()),
				);
				nodes.push(Node {
					span: dir_span,
					ty: NodeTy::DefineDirective {
						macro_: ast::Macro::Object {
							ident: Ident {
								span: ident.1,
								name: ident.0,
							},
						},
						replacement_tokens: body_tokens,
					},
				});
			} else {
				// We have a function-like macro.

				let ident = match ident_tokens.remove(0) {
					(DefineToken::Ident(s), span) => {
						walker.push_colour(span, SyntaxToken::FunctionMacro);
						(s, span)
					}
					_ => unreachable!(),
				};

				// Consume the `(`.
				let l_paren_span = match ident_tokens.remove(0) {
					(DefineToken::LParen, span) => {
						walker.push_colour(span, SyntaxToken::Punctuation);
						span
					}
					_ => unreachable!(),
				};

				// Look for any parameters until we hit a closing `)` parenthesis.
				#[derive(PartialEq)]
				enum Prev {
					None,
					Param,
					Comma,
					Invalid,
				}
				let mut prev = Prev::None;
				let mut prev_span = l_paren_span;
				let mut params = Vec::new();
				let r_paren_span = loop {
					let (token, token_span) = if !ident_tokens.is_empty() {
						ident_tokens.remove(0)
					} else {
						walker.push_syntax_diag(Syntax::PreprocDefine(
							PreprocDefineDiag::ParamsExpectedRParen(
								prev_span.next_single_width(),
							),
						));
						nodes.push(Node {
							span: dir_span,
							ty: NodeTy::DefineDirective {
								macro_: ast::Macro::Function {
									ident: Ident {
										span: ident.1,
										name: ident.0,
									},
									params,
								},
								replacement_tokens: body_tokens,
							},
						});
						return;
					};

					match token {
						DefineToken::Comma => {
							walker.push_colour(
								token_span,
								SyntaxToken::Punctuation,
							);
							if prev == Prev::Comma {
								walker.push_syntax_diag(Syntax::PreprocDefine(
									PreprocDefineDiag::ParamsExpectedParamAfterComma(Span::new_between(
										prev_span, token_span
									))
								));
							} else if prev == Prev::None {
								walker.push_syntax_diag(Syntax::PreprocDefine(
									PreprocDefineDiag::ParamsExpectedParamBetweenParenComma(Span::new_between(
										l_paren_span, token_span
									))
								));
							}
							prev = Prev::Comma;
							prev_span = token_span;
						}
						DefineToken::Ident(str) => {
							walker.push_colour(token_span, SyntaxToken::Ident);
							params.push(Ident {
								name: str,
								span: token_span,
							});
							if prev == Prev::Param {
								walker.push_syntax_diag(Syntax::PreprocDefine(
									PreprocDefineDiag::ParamsExpectedCommaAfterParam(prev_span.next_single_width())
								));
							}
							prev = Prev::Param;
							prev_span = token_span;
						}
						DefineToken::RParen => {
							walker.push_colour(
								token_span,
								SyntaxToken::Punctuation,
							);
							if prev == Prev::Comma {
								walker.push_syntax_diag(Syntax::PreprocDefine(
									PreprocDefineDiag::ParamsExpectedParamAfterComma(Span::new_between(
										prev_span, token_span
									))
								));
							}
							break token_span;
						}
						DefineToken::Invalid(_) | _ => {
							walker
								.push_colour(token_span, SyntaxToken::Invalid);
							walker.push_syntax_diag(Syntax::PreprocDefine(
								PreprocDefineDiag::ParamsExpectedParam(
									token_span,
								),
							));
							prev = Prev::Invalid;
							prev_span = token_span;
						}
					}
				};

				body_tokens.iter().for_each(|(t, s)| {
					walker.push_colour(*s, t.non_semantic_colour())
				});

				walker.register_macro(
					ident.0.clone(),
					Span::new(ident.1.start, r_paren_span.end),
					Macro::Function {
						params: params.clone(),
						body: body_tokens.clone(),
					},
				);
				nodes.push(Node {
					span: dir_span,
					ty: NodeTy::DefineDirective {
						macro_: ast::Macro::Function {
							ident: Ident {
								span: ident.1,
								name: ident.0,
							},
							params,
						},
						replacement_tokens: body_tokens,
					},
				});
			}
		}
		PreprocStream::Undef {
			kw: kw_span,
			mut tokens,
		} => {
			walker.push_colour(dir_span.first_char(), SyntaxToken::Directive);
			walker.push_colour(kw_span, SyntaxToken::Directive);

			let ident = if tokens.is_empty() {
				walker.push_syntax_diag(Syntax::PreprocDefine(
					PreprocDefineDiag::UndefExpectedMacroName(
						kw_span.next_single_width(),
					),
				));
				Omittable::None
			} else {
				let (token, token_span) = tokens.remove(0);

				let ident = match token {
					UndefToken::Ident(s) => {
						walker.unregister_macro(&s, token_span);
						Omittable::Some(Ident {
							name: s,
							span: token_span,
						})
					}
					UndefToken::Invalid(_) => {
						walker.push_syntax_diag(Syntax::PreprocDefine(
							PreprocDefineDiag::UndefExpectedMacroName(
								token_span,
							),
						));
						Omittable::None
					}
				};

				if !tokens.is_empty() {
					let (_, first) = tokens.first().unwrap();
					let (_, last) = tokens.last().unwrap();
					walker.push_syntax_diag(Syntax::PreprocTrailingTokens(
						Span::new(first.start, last.end),
					));
				}

				ident
			};

			nodes.push(Node {
				span: Span::new(
					dir_span.start,
					if let Omittable::Some(ref ident) = ident {
						ident.span.end
					} else {
						kw_span.end
					},
				),
				ty: NodeTy::UndefDirective { name: ident },
			});
		}
		PreprocStream::Error { kw, message } => {
			parse_error_directive(walker, nodes, dir_span, kw, message)
		}
		PreprocStream::Pragma { kw, options } => {
			parse_pragma_directive(walker, nodes, dir_span, kw, options)
		}
		_ => {}
	}
}

/// Parses a `#version` directive.
fn parse_version_directive(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	dir_span: Span,
	kw_span: Span,
	tokens: Vec<(VersionToken, Span)>,
) {
	walker.push_colour(dir_span.first_char(), SyntaxToken::Directive);
	walker.push_colour(kw_span, SyntaxToken::Directive);

	if tokens.is_empty() {
		walker.push_syntax_diag(Syntax::PreprocVersion(
			PreprocVersionDiag::ExpectedNumber(kw_span.next_single_width()),
		));
		return;
	}
	let mut tokens = tokens.into_iter();

	/// Consumes the rest of the tokens.
	fn seek_end(
		walker: &mut Walker,
		mut tokens: impl Iterator<Item = (VersionToken, Span)>,
		emit_diagnostic: bool,
	) {
		let span_start = match tokens.next() {
			Some((_, span)) => span.start,
			None => return,
		};
		let mut span_end = span_start;
		for (token, token_span) in tokens {
			walker.push_colour(
				token_span,
				match token {
					VersionToken::Invalid(_) => SyntaxToken::Invalid,
					_ => SyntaxToken::Directive,
				},
			);
			span_end = token_span.end;
		}
		if emit_diagnostic {
			walker.push_syntax_diag(Syntax::PreprocTrailingTokens(Span::new(
				span_start, span_end,
			)));
		}
	}

	/// Parses the version number.
	fn parse_version(
		walker: &mut Walker,
		number: usize,
		span: Span,
	) -> Option<usize> {
		match number {
			450 => Some(number),
			100 | 110 | 120 | 130 | 140 | 150 | 300 | 310 | 320 | 330 | 400
			| 410 | 420 | 430 | 460 => {
				walker.push_syntax_diag(Syntax::PreprocVersion(
					PreprocVersionDiag::UnsupportedVersion(span, number),
				));
				Some(number)
			}
			_ => {
				walker.push_syntax_diag(Syntax::PreprocVersion(
					PreprocVersionDiag::InvalidVersion(span, number),
				));
				None
			}
		}
	}

	/// Parses the profile.
	fn parse_profile(
		walker: &mut Walker,
		str: &str,
		span: Span,
	) -> Option<ProfileTy> {
		match str {
			"core" => {
				walker.push_colour(span, SyntaxToken::Directive);
				Some(ProfileTy::Core)
			}
			"compatability" => {
				walker.push_colour(span, SyntaxToken::Directive);
				Some(ProfileTy::Compatability)
			}
			"es" => {
				walker.push_colour(span, SyntaxToken::Directive);
				Some(ProfileTy::Es)
			}
			_ => {
				let str = str.to_lowercase();
				match str.as_ref() {
					"core" => {
						walker.push_colour(span, SyntaxToken::Directive);
						walker.push_syntax_diag(Syntax::PreprocVersion(
							PreprocVersionDiag::InvalidProfileCasing(
								span, "core",
							),
						));
						Some(ProfileTy::Core)
					}
					"compatability" => {
						walker.push_colour(span, SyntaxToken::Directive);
						walker.push_syntax_diag(Syntax::PreprocVersion(
							PreprocVersionDiag::InvalidProfileCasing(
								span,
								"compatability",
							),
						));
						Some(ProfileTy::Compatability)
					}
					"es" => {
						walker.push_colour(span, SyntaxToken::Directive);
						walker.push_syntax_diag(Syntax::PreprocVersion(
							PreprocVersionDiag::InvalidProfileCasing(
								span, "es",
							),
						));
						Some(ProfileTy::Es)
					}
					_ => None,
				}
			}
		}
	}

	// Consume the version number.
	let version = {
		let (token, token_span) = tokens.next().unwrap();
		match token {
			VersionToken::Num(n) => {
				match parse_version(walker, n, token_span) {
					Some(n) => {
						walker.push_colour(token_span, SyntaxToken::Directive);
						(n, token_span)
					}
					None => {
						walker.push_colour(token_span, SyntaxToken::Directive);
						seek_end(walker, tokens, false);
						return;
					}
				}
			}
			VersionToken::InvalidNum(_) => {
				walker.push_colour(token_span, SyntaxToken::Directive);
				walker.push_syntax_diag(Syntax::PreprocVersion(
					PreprocVersionDiag::InvalidNumber(token_span),
				));
				seek_end(walker, tokens, false);
				return;
			}
			VersionToken::Invalid(_) => {
				walker.push_colour(token_span, SyntaxToken::Invalid);
				walker.push_syntax_diag(Syntax::PreprocVersion(
					PreprocVersionDiag::ExpectedNumber(token_span),
				));
				seek_end(walker, tokens, false);
				return;
			}
			VersionToken::Word(str) => {
				match parse_profile(walker, &str, token_span) {
					Some(profile) => {
						// We have a profile immediately after the `version` keyword.
						walker.push_syntax_diag(Syntax::PreprocVersion(PreprocVersionDiag::MissingNumberBetweenKwAndProfile(
								Span::new_between(kw_span, token_span)
							)));
						seek_end(walker, tokens, true);
						nodes.push(Node {
							span: Span::new(dir_span.start, token_span.end),
							ty: NodeTy::VersionDirective {
								version: None,
								profile: Omittable::Some((profile, token_span)),
							},
						});
						return;
					}
					None => {
						walker.push_colour(token_span, SyntaxToken::Directive);
						walker.push_syntax_diag(Syntax::PreprocVersion(
							PreprocVersionDiag::ExpectedNumber(token_span),
						));
						seek_end(walker, tokens, false);
						return;
					}
				}
			}
		}
	};

	// Look for an optional profile.
	let profile = match tokens.next() {
		Some((token, token_span)) => match token {
			VersionToken::Word(str) => {
				match parse_profile(walker, &str, token_span) {
					Some(p) => Omittable::Some((p, token_span)),
					None => {
						walker.push_syntax_diag(Syntax::PreprocVersion(
							PreprocVersionDiag::InvalidProfile(token_span),
						));
						seek_end(walker, tokens, false);
						nodes.push(Node {
							span: Span::new(dir_span.start, version.1.end),
							ty: NodeTy::VersionDirective {
								version: Some(version),
								profile: Omittable::None,
							},
						});
						return;
					}
				}
			}
			_ => {
				walker.push_syntax_diag(Syntax::PreprocVersion(
					PreprocVersionDiag::ExpectedProfile(token_span),
				));
				seek_end(walker, tokens, false);
				nodes.push(Node {
					span: Span::new(dir_span.start, version.1.end),
					ty: NodeTy::VersionDirective {
						version: Some(version),
						profile: Omittable::None,
					},
				});
				return;
			}
		},
		None => Omittable::None,
	};

	seek_end(walker, tokens, true);
	nodes.push(Node {
		span: Span::new(
			dir_span.start,
			if let Omittable::Some(ref profile) = profile {
				profile.1.end
			} else {
				version.1.end
			},
		),
		ty: NodeTy::VersionDirective {
			version: Some(version),
			profile,
		},
	});
}

/// Parses an `#extension` directive.
fn parse_extension_directive(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	dir_span: Span,
	kw_span: Span,
	tokens: Vec<(ExtensionToken, Span)>,
) {
	walker.push_colour(dir_span.first_char(), SyntaxToken::Directive);
	walker.push_colour(kw_span, SyntaxToken::Directive);

	if tokens.is_empty() {
		walker.push_syntax_diag(Syntax::PreprocExt(
			PreprocExtDiag::ExpectedName(kw_span.next_single_width()),
		));
		return;
	}
	let mut tokens = tokens.into_iter();

	/// Consumes the rest of the tokens.
	fn seek_end(
		walker: &mut Walker,
		mut tokens: impl Iterator<Item = (ExtensionToken, Span)>,
		emit_diagnostic: bool,
	) {
		let span_start = match tokens.next() {
			Some((_, span)) => span.start,
			None => return,
		};
		let mut span_end = span_start;
		for (token, token_span) in tokens {
			walker.push_colour(
				token_span,
				match token {
					ExtensionToken::Invalid(_) => SyntaxToken::Invalid,
					_ => SyntaxToken::Directive,
				},
			);
			span_end = token_span.end;
		}
		if emit_diagnostic {
			walker.push_syntax_diag(Syntax::PreprocTrailingTokens(Span::new(
				span_start, span_end,
			)));
		}
	}

	/// Parses the behaviour.
	fn parse_behaviour(
		str: &str,
		span: Span,
	) -> Option<(BehaviourTy, Option<Syntax>)> {
		match str {
			"require" => Some((BehaviourTy::Require, None)),
			"enable" => Some((BehaviourTy::Enable, None)),
			"warn" => Some((BehaviourTy::Warn, None)),
			"disable" => Some((BehaviourTy::Disable, None)),
			_ => {
				let str = str.to_lowercase();
				match str.as_ref() {
					"require" => Some((
						BehaviourTy::Require,
						Some(Syntax::PreprocExt(
							PreprocExtDiag::InvalidBehaviourCasing(
								span, "require",
							),
						)),
					)),
					"enable" => Some((
						BehaviourTy::Enable,
						Some(Syntax::PreprocExt(
							PreprocExtDiag::InvalidBehaviourCasing(
								span, "enable",
							),
						)),
					)),
					"warn" => Some((
						BehaviourTy::Warn,
						Some(Syntax::PreprocExt(
							PreprocExtDiag::InvalidBehaviourCasing(
								span, "warn",
							),
						)),
					)),
					"disable" => Some((
						BehaviourTy::Disable,
						Some(Syntax::PreprocExt(
							PreprocExtDiag::InvalidBehaviourCasing(
								span, "disable",
							),
						)),
					)),
					_ => None,
				}
			}
		}
	}

	// Consume the extension name.
	let name = {
		let (token, token_span) = tokens.next().unwrap();
		match token {
			ExtensionToken::Word(str) => {
				match parse_behaviour(&str, token_span) {
					Some((behaviour, _)) => {
						walker.push_colour(token_span, SyntaxToken::Directive);
						walker.push_syntax_diag(Syntax::PreprocExt(
							PreprocExtDiag::MissingNameBetweenKwAndBehaviour(
								Span::new_between(kw_span, token_span),
							),
						));
						seek_end(walker, tokens, false);
						nodes.push(Node {
							span: Span::new(dir_span.start, token_span.end),
							ty: NodeTy::ExtensionDirective {
								name: None,
								behaviour: Some((behaviour, token_span)),
							},
						});
						return;
					}
					None => (str, token_span),
				}
			}
			ExtensionToken::Colon => {
				walker.push_colour(token_span, SyntaxToken::Directive);
				walker.push_syntax_diag(Syntax::PreprocExt(
					PreprocExtDiag::MissingNameBetweenKwAndColon(
						Span::new_between(kw_span, token_span),
					),
				));
				seek_end(walker, tokens, false);
				nodes.push(Node {
					span: Span::new(dir_span.start, kw_span.end),
					ty: NodeTy::ExtensionDirective {
						name: None,
						behaviour: None,
					},
				});
				return;
			}
			ExtensionToken::Invalid(_) => {
				walker.push_colour(token_span, SyntaxToken::Invalid);
				walker.push_syntax_diag(Syntax::PreprocExt(
					PreprocExtDiag::ExpectedName(token_span),
				));
				seek_end(walker, tokens, false);
				return;
			}
		}
	};

	// Consume the colon.
	let colon_span = match tokens.next() {
		Some((token, token_span)) => match token {
			ExtensionToken::Colon => {
				walker.push_colour(token_span, SyntaxToken::Directive);
				token_span
			}
			ExtensionToken::Word(str) => {
				match parse_behaviour(&str, token_span) {
					Some((behaviour, _)) => {
						walker.push_colour(token_span, SyntaxToken::Directive);
						walker.push_syntax_diag(Syntax::PreprocExt(
							PreprocExtDiag::MissingColonBetweenNameAndBehaviour(
								Span::new_between(name.1, token_span),
							),
						));
						seek_end(walker, tokens, false);
						nodes.push(Node {
							span: Span::new(dir_span.start, token_span.end),
							ty: NodeTy::ExtensionDirective {
								name: Some(name),
								behaviour: Some((behaviour, token_span)),
							},
						});
						return;
					}
					None => {
						walker.push_colour(token_span, SyntaxToken::Invalid);
						walker.push_syntax_diag(Syntax::PreprocExt(
							PreprocExtDiag::ExpectedColon(token_span),
						));
						seek_end(walker, tokens, false);
						nodes.push(Node {
							span: Span::new(dir_span.start, name.1.end),
							ty: NodeTy::ExtensionDirective {
								name: Some(name),
								behaviour: None,
							},
						});
						return;
					}
				}
			}
			ExtensionToken::Invalid(_) => {
				walker.push_colour(token_span, SyntaxToken::Invalid);
				walker.push_syntax_diag(Syntax::PreprocExt(
					PreprocExtDiag::ExpectedColon(token_span),
				));
				seek_end(walker, tokens, false);
				nodes.push(Node {
					span: Span::new(dir_span.start, name.1.end),
					ty: NodeTy::ExtensionDirective {
						name: Some(name),
						behaviour: None,
					},
				});
				return;
			}
		},
		None => {
			walker.push_syntax_diag(Syntax::PreprocExt(
				PreprocExtDiag::ExpectedColon(name.1.next_single_width()),
			));
			nodes.push(Node {
				span: Span::new(dir_span.start, name.1.end),
				ty: NodeTy::ExtensionDirective {
					name: Some(name),
					behaviour: None,
				},
			});
			return;
		}
	};

	// Consume the behaviour.
	let behaviour = match tokens.next() {
		Some((token, token_span)) => match token {
			ExtensionToken::Word(str) => {
				match parse_behaviour(&str, token_span) {
					Some((behaviour, diag)) => {
						walker.push_colour(token_span, SyntaxToken::Directive);
						if let Some(diag) = diag {
							walker.push_syntax_diag(diag);
						}
						(behaviour, token_span)
					}
					None => {
						walker.push_colour(token_span, SyntaxToken::Invalid);
						walker.push_syntax_diag(Syntax::PreprocExt(
							PreprocExtDiag::InvalidBehaviour(token_span),
						));
						seek_end(walker, tokens, false);
						nodes.push(Node {
							span: Span::new(dir_span.start, colon_span.end),
							ty: NodeTy::ExtensionDirective {
								name: Some(name),
								behaviour: None,
							},
						});
						return;
					}
				}
			}
			ExtensionToken::Colon | ExtensionToken::Invalid(_) => {
				walker.push_colour(token_span, SyntaxToken::Invalid);
				walker.push_syntax_diag(Syntax::PreprocExt(
					PreprocExtDiag::ExpectedBehaviour(token_span),
				));
				seek_end(walker, tokens, false);
				nodes.push(Node {
					span: Span::new(dir_span.start, colon_span.end),
					ty: NodeTy::ExtensionDirective {
						name: Some(name),
						behaviour: None,
					},
				});
				return;
			}
		},
		None => {
			walker.push_syntax_diag(Syntax::PreprocExt(
				PreprocExtDiag::ExpectedBehaviour(name.1.next_single_width()),
			));
			nodes.push(Node {
				span: Span::new(dir_span.start, colon_span.end),
				ty: NodeTy::ExtensionDirective {
					name: Some(name),
					behaviour: None,
				},
			});
			return;
		}
	};

	seek_end(walker, tokens, true);
	nodes.push(Node {
		span: Span::new(dir_span.start, behaviour.1.end),
		ty: NodeTy::ExtensionDirective {
			name: Some(name),
			behaviour: Some(behaviour),
		},
	});
}

/// Parses a `#line` directive.
fn parse_line_directive(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	dir_span: Span,
	kw_span: Span,
	tokens: Vec<(LineToken, Span)>,
) {
	walker.push_colour(dir_span.first_char(), SyntaxToken::Directive);
	walker.push_colour(kw_span, SyntaxToken::Directive);

	if tokens.is_empty() {
		walker.push_syntax_diag(Syntax::PreprocLine(
			PreprocLineDiag::ExpectedNumber(kw_span.next_single_width()),
		));
		return;
	}
	let mut tokens = tokens.into_iter();

	/// Consumes the rest of the tokens.
	fn seek_end(
		walker: &mut Walker,
		mut tokens: impl Iterator<Item = (LineToken, Span)>,
		emit_diagnostic: bool,
	) {
		let span_start = match tokens.next() {
			Some((_, span)) => span.start,
			None => return,
		};
		let mut span_end = span_start;
		for (token, token_span) in tokens {
			walker.push_colour(
				token_span,
				match token {
					LineToken::Invalid(_) => SyntaxToken::Invalid,
					_ => SyntaxToken::Directive,
				},
			);
			span_end = token_span.end;
		}
		if emit_diagnostic {
			walker.push_syntax_diag(Syntax::PreprocTrailingTokens(Span::new(
				span_start, span_end,
			)));
		}
	}

	let line = {
		let (token, token_span) = tokens.next().unwrap();
		match token {
			LineToken::Num(n) => {
				walker.push_colour(token_span, SyntaxToken::Directive);
				Some((n, token_span))
			}
			LineToken::InvalidNum(_) => {
				walker.push_colour(token_span, SyntaxToken::Invalid);
				walker.push_syntax_diag(Syntax::PreprocLine(
					PreprocLineDiag::InvalidNumber(token_span),
				));
				None
			}
			LineToken::Ident(str) => {
				let ident_span = token_span;

				let mut line = None;
				let mut src_str_num = Omittable::None;
				/* if let Some((_, replacement_list)) = walker.macros.get(&str) {
								   'replacement: for (token, _) in replacement_list {
									   match token {
										   Token::Num { type_, num, suffix } => {
											   if *type_ != NumType::Dec || suffix.is_some() {
												   walker.push_syntax_diag(
													   Syntax::PreprocLine(
														   PreprocLineDiag::InvalidNumber(
															   ident_span,
														   ),
													   ),
												   );
												   seek_end(walker, tokens, false);
												   nodes.push(Node {
													   span: Span::new(
														   dir_span.start,
														   kw_span.end,
													   ),
													   ty: NodeTy::LineDirective {
														   line,
														   src_str_num,
													   },
												   });
												   return;
											   }

											   let num: usize = match num.parse() {
												   Ok(n) => n,
												   Err(_) => {
													   walker.push_syntax_diag(
														   Syntax::PreprocLine(
															   PreprocLineDiag::InvalidNumber(
																   ident_span,
															   ),
														   ),
													   );
													   seek_end(walker, tokens, false);
													   nodes.push(Node {
														   span: Span::new(
															   dir_span.start,
															   kw_span.end,
														   ),
														   ty: NodeTy::LineDirective {
															   line,
															   src_str_num,
														   },
													   });
													   return;
												   }
											   };

											   if src_str_num.is_some() {
												   walker.push_syntax_diag(
													   Syntax::PreprocTrailingTokens(
														   ident_span,
													   ),
												   );
												   break 'replacement;
											   }

											   if line.is_none() {
												   line = Some((num, ident_span))
											   } else {
												   src_str_num =
													   Omittable::Some((num, ident_span));
											   }
										   }
										   _ => {
											   walker.push_syntax_diag(Syntax::PreprocLine(
												   PreprocLineDiag::ExpectedNumber(ident_span),
											   ));
											   seek_end(walker, tokens, false);
											   nodes.push(Node {
												   span: Span::new(
													   dir_span.start,
													   kw_span.end,
												   ),
												   ty: NodeTy::LineDirective {
													   line,
													   src_str_num,
												   },
											   });
											   return;
										   }
									   }
								   }
							   }
				*/
				if src_str_num.is_some() {
					seek_end(walker, tokens, true);
					nodes.push(Node {
						span: Span::new(dir_span.start, kw_span.end),
						ty: NodeTy::LineDirective { line, src_str_num },
					});
					return;
				} else {
					line
				}
			}
			LineToken::Invalid(_) => {
				walker.push_colour(token_span, SyntaxToken::Invalid);
				walker.push_syntax_diag(Syntax::PreprocLine(
					PreprocLineDiag::ExpectedNumber(token_span),
				));
				seek_end(walker, tokens, false);
				nodes.push(Node {
					span: Span::new(dir_span.start, kw_span.end),
					ty: NodeTy::LineDirective {
						line: None,
						src_str_num: Omittable::None,
					},
				});
				return;
			}
		}
	};

	let src_str_num = match tokens.next() {
		Some((token, token_span)) => match token {
			LineToken::Num(n) => {
				walker.push_colour(token_span, SyntaxToken::Directive);
				Omittable::Some((n, token_span))
			}
			LineToken::InvalidNum(_) => {
				walker.push_colour(token_span, SyntaxToken::Invalid);
				walker.push_syntax_diag(Syntax::PreprocLine(
					PreprocLineDiag::InvalidNumber(token_span),
				));
				Omittable::None
			}
			LineToken::Ident(str) => {
				let ident_span = token_span;

				let mut src_str_num = Omittable::None;
				if let Some((_, replacement_list)) = walker.macros.get(&str) {
					/* 'replacement: for (token, _) in replacement_list {
						   match token {
							   Token::Num { type_, num, suffix } => {
								   if *type_ != NumType::Dec || suffix.is_some() {
									   walker.push_syntax_diag(
										   Syntax::PreprocLine(
											   PreprocLineDiag::InvalidNumber(
												   ident_span,
											   ),
										   ),
									   );
									   seek_end(walker, tokens, false);
									   nodes.push(Node {
										   span: Span::new(
											   dir_span.start,
											   kw_span.end,
										   ),
										   ty: NodeTy::LineDirective {
											   line,
											   src_str_num,
										   },
									   });
									   return;
								   }

								   let num: usize = match num.parse() {
									   Ok(n) => n,
									   Err(_) => {
										   walker.push_syntax_diag(
											   Syntax::PreprocLine(
												   PreprocLineDiag::InvalidNumber(
													   ident_span,
												   ),
											   ),
										   );
										   seek_end(walker, tokens, false);
										   nodes.push(Node {
											   span: Span::new(
												   dir_span.start,
												   kw_span.end,
											   ),
											   ty: NodeTy::LineDirective {
												   line,
												   src_str_num,
											   },
										   });
										   return;
									   }
								   };

								   if src_str_num.is_some() {
									   walker.push_syntax_diag(
										   Syntax::PreprocTrailingTokens(
											   ident_span,
										   ),
									   );
									   break 'replacement;
								   }

								   src_str_num =
									   Omittable::Some((num, ident_span));
							   }
							   _ => {
								   walker.push_syntax_diag(Syntax::PreprocLine(
									   PreprocLineDiag::ExpectedNumber(ident_span),
								   ));
								   seek_end(walker, tokens, false);
								   nodes.push(Node {
									   span: Span::new(
										   dir_span.start,
										   kw_span.end,
									   ),
									   ty: NodeTy::LineDirective {
										   line,
										   src_str_num,
									   },
								   });
								   return;
							   }
						   }
					   }
					*/
				}

				src_str_num
			}
			LineToken::Invalid(_) => {
				walker.push_colour(token_span, SyntaxToken::Invalid);
				walker.push_syntax_diag(Syntax::PreprocLine(
					PreprocLineDiag::ExpectedNumber(token_span),
				));
				seek_end(walker, tokens, false);
				nodes.push(Node {
					span: Span::new(
						dir_span.start,
						if let Some(line) = line {
							line.1.end
						} else {
							kw_span.end
						},
					),
					ty: NodeTy::LineDirective {
						line,
						src_str_num: Omittable::None,
					},
				});
				return;
			}
		},
		None => Omittable::None,
	};

	seek_end(walker, tokens, true);
	nodes.push(Node {
		span: Span::new(
			dir_span.start,
			if let Omittable::Some(src_str_num) = src_str_num {
				src_str_num.1.end
			} else if let Some(line) = line {
				line.1.end
			} else {
				kw_span.end
			},
		),
		ty: NodeTy::LineDirective { line, src_str_num },
	});
}

/// Parses an `#error` directive.
fn parse_error_directive(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	dir_span: Span,
	kw_span: Span,
	message: Option<Spanned<String>>,
) {
	walker.push_colour(dir_span.first_char(), SyntaxToken::Directive);
	walker.push_colour(kw_span, SyntaxToken::Directive);
	if let Some(ref message) = message {
		walker.push_colour(message.1, SyntaxToken::Directive);
	}
	nodes.push(Node {
		span: Span::new(
			dir_span.start,
			if let Some(ref message) = message {
				message.1.end
			} else {
				kw_span.end
			},
		),
		ty: NodeTy::ErrorDirective {
			message: message.into(),
		},
	});
}

/// Parses a `#pragma` directive.
fn parse_pragma_directive(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	dir_span: Span,
	kw_span: Span,
	options: Option<Spanned<String>>,
) {
	walker.push_colour(dir_span.first_char(), SyntaxToken::Directive);
	walker.push_colour(kw_span, SyntaxToken::Directive);
	if let Some(ref options) = options {
		walker.push_colour(options.1, SyntaxToken::Directive);
	}
	nodes.push(Node {
		span: Span::new(
			dir_span.start,
			if let Some(ref options) = options {
				options.1.end
			} else {
				kw_span.end
			},
		),
		ty: NodeTy::PragmaDirective {
			options: options.into(),
		},
	});
}

/// Combines the ident information with the type to create one or more type-ident pairs. This step is necessary
/// because the idents themselves can contain type information, e.g. `int[3] i[9]`.
fn combine_type_with_idents(
	type_: Type,
	ident_info: Vec<(Ident, Vec<ArrSize>)>,
) -> Vec<(Type, Ident)> {
	let mut vars = Vec::new();
	for (ident, sizes) in ident_info {
		if sizes.is_empty() {
			vars.push((type_.clone(), ident));
		} else {
			let mut sizes = sizes.clone();
			let Type {
				ty,
				qualifiers,
				span,
			} = type_.clone();
			let primitive = match ty {
				TypeTy::Single(p) => p,
				TypeTy::Array(p, i) => {
					sizes.push(i);
					p
				}
				TypeTy::Array2D(p, i, j) => {
					sizes.push(i);
					sizes.push(j);
					p
				}
				TypeTy::ArrayND(p, mut v) => {
					sizes.append(&mut v);
					p
				}
			};

			let type_ = if sizes.len() == 0 {
				Type {
					span,
					ty: TypeTy::Single(primitive),
					qualifiers,
				}
			} else if sizes.len() == 1 {
				Type {
					span,
					ty: TypeTy::Array(primitive, sizes.remove(0)),
					qualifiers,
				}
			} else if sizes.len() == 2 {
				Type {
					span,
					ty: TypeTy::Array2D(
						primitive,
						sizes.remove(0),
						sizes.remove(0),
					),
					qualifiers,
				}
			} else {
				Type {
					span,
					ty: TypeTy::ArrayND(primitive, sizes),
					qualifiers,
				}
			};

			vars.push((type_, ident))
		}
	}
	vars
}
