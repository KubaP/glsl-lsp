pub mod ast;
mod expression;
mod syntax;

pub use syntax::*;

use crate::{
	diag::{PreprocDefineDiag, Semantic, StmtDiag, Syntax},
	lexer::{preprocessor::TokenStream as PreprocStream, Token, TokenStream},
	Span, Spanned,
};
use ast::*;
use expression::{expr_parser, Mode};
use std::collections::{HashMap, HashSet};

/// The result of a parsed GLSL source string.
///
/// - `0` - The abstract syntax tree,
/// - `1` - Any diagnostics created during parsing,
/// - `2` - Syntax highlighting tokens.
pub type ParseResult = (Vec<Node>, Vec<Syntax>, Vec<Spanned<SyntaxToken>>);

/// An error type for parsing operations.
#[derive(Debug)]
pub enum ParseErr {
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
/// AST, multiple ASTs are needed to represent all the conditional permutations.
///
/// The [`TokenTree`] struct allows you to pick which conditional compilation permutations to enable, and then
/// parse the source string with those conditions to produce a [`Shader`]. Each permutation of all possible ASTs
/// can be accessed with a key that describes which of the conditional options is selected. The example below
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
/// [`root()`](TokenTree::root) method. There are two ways of controlling which conditions are enabled, by order
/// of appearance or by order of nesting.
///
/// ## Order by appearance
/// Each encountered condition (an `ifdef`/`ifndef`/`if`/`elif`/`else` directive) is given an incrementing number.
/// You pass a slice of numbers that denote which conditions to enable into the
/// [`parse_by_order_of_appearance()`](TokenTree::parse_by_order_of_appearance) method.
///
/// Some examples to visualise:
/// - `[1, 3]` will produce: `foo AAA 60 BBB bar`,
/// - `[4]` will produce: `foo CCC bar`,
/// - `[6, 7]` will produce: `foo EEE 100 bar`,
/// - `[1, 2, 6, 7]` will produce: `foo AAA 50 BBB EEE 100 bar`.
///
/// ## Order by nesting
/// Each encountered group of conditions (an `ifdef`/`ifndef`/`if` - `elif`/`else` - `endif`) creates a newly
/// nested group. Within each group the individual conditions are numbered by order of appearance from 0. You pass
/// slices of numbers that denote which conditions to enable into the
/// [`parse_by_order_of_nesting()`](TokenTree::parse_by_order_of_nesting) method.
///
/// Some examples to visualise:
/// - `[[0-0, 0-1]]` will produce: `foo AAA 60 BBB bar`,
/// - `[[0-1]]` will produce: `foo CCC bar`,
/// - `[[1-0, 0-0]]` will produce: `foo EEE 100 bar`,
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
/// int i = 5.0 + 1;
/// "#;
/// let trees = parse_from_str(&src);
/// let (ast, _, _) = trees.root();
/// ```
pub fn parse_from_str(source: &str) -> TokenTree {
	let (mut token_stream, metadata) = crate::lexer::parse_from_str(source);

	// Skip tree generation if there are no conditional compilation blocks.
	if !metadata.contains_conditional_compilation {
		return TokenTree {
			arena: vec![TreeNode {
				parent: None,
				contents: vec![Content::Tokens(token_stream)],
			}],
			order_by_appearance: vec![],
			contains_conditional_compilation: false,
		};
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
	// tree representation:
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
	// order-by-appearance: [(0, 0), (1, 0), (2, 1), (3, 0)]

	fn push_condition(arena: &mut Vec<TreeNode>, id: NodeId) -> NodeId {
		let new_id = arena.len();
		arena.push(TreeNode {
			parent: Some(id),
			contents: vec![Content::Tokens(vec![])],
		});
		arena
			.get_mut(id)
			.unwrap() // Panic: `id` is always valid.
			.contents
			.push(Content::ConditionalBlock {
				if_: new_id,
				completed_if: false,
				elses: vec![],
			});
		new_id
	}

	fn push_token(
		arena: &mut Vec<TreeNode>,
		id: NodeId,
		token: Spanned<Token>,
	) {
		let node = arena.get_mut(id).unwrap(); // Panic: `id` is always valid.
		match node.contents.last_mut() {
			Some(content) => match content {
				Content::Tokens(v) => v.push(token),
				Content::ConditionalBlock { .. } => {
					node.contents.push(Content::Tokens(vec![token]));
				}
			},
			None => node.contents.push(Content::Tokens(vec![token])),
		};
	}

	// The arena containing all of the nodes. The IDs are just `usize` indexes into this vector.
	let mut arena = vec![TreeNode {
		parent: None,
		contents: vec![Content::Tokens(vec![])],
	}];
	// The stack representing the IDs of currently nested nodes. The first ID always refers to the root node.
	// Invariant: Any time this is `pop()`ed a length check is made to ensure that `[0]` is always valid.
	let mut stack = vec![0];
	// A vector which creates a mapping between `order-of-appearance` -> `node ID, parent node ID`. The parent node
	// ID is tracked so that in the `parse_by_order_of_appearance()` method we can validate whether the order is
	// valid.
	let mut order_by_appearance = vec![(0, 0)];

	// We consume all of the tokens from the beginning.
	loop {
		let (token, token_span) = if !token_stream.is_empty() {
			token_stream.remove(0)
		} else {
			break;
		};

		match token {
			Token::Directive(d) => match d {
				PreprocStream::IfDef { .. }
				| PreprocStream::IfNotDef { .. }
				| PreprocStream::If { .. } => {
					let new_id =
						push_condition(&mut arena, *stack.last().unwrap());
					order_by_appearance.push((new_id, *stack.last().unwrap()));
					stack.push(new_id);
				}
				PreprocStream::ElseIf { .. } => {
					if stack.len() > 1 {
						stack.pop();
						let new_id = arena.len();
						arena.push(TreeNode {
							parent: Some(*stack.last().unwrap()),
							contents: vec![],
						});

						let container =
							arena.get_mut(*stack.last().unwrap()).unwrap(); // Panic: the `id` is always valid.
						if let Some(Content::ConditionalBlock {
							if_: _,
							completed_if,
							elses,
						}) = container.contents.last_mut()
						{
							*completed_if = true;
							elses.push((Condition::ElseIf, new_id));
							order_by_appearance
								.push((new_id, *stack.last().unwrap()));
							stack.push(new_id);
						} else {
							// TODO: Emit error.
						}
					} else {
						// TODO: Emit error.
					}
				}
				PreprocStream::Else { .. } => {
					if stack.len() > 1 {
						stack.pop();
						let new_id = arena.len();
						arena.push(TreeNode {
							parent: Some(*stack.last().unwrap()),
							contents: vec![],
						});

						let container =
							arena.get_mut(*stack.last().unwrap()).unwrap();
						if let Some(Content::ConditionalBlock {
							if_: _,
							completed_if,
							elses,
						}) = container.contents.last_mut()
						{
							*completed_if = true;
							elses.push((Condition::Else, new_id));
							order_by_appearance
								.push((new_id, *stack.last().unwrap()));
							stack.push(new_id);
						} else {
							// TODO: Emit error.
						}
					} else {
						// TODO: Emit error.
					}
				}
				PreprocStream::EndIf { .. } => {
					if stack.len() > 1 {
						stack.pop();
					} else {
						// TODO: Emit error.
					}
				}
				_ => push_token(
					&mut arena,
					*stack.last().unwrap(),
					(Token::Directive(d), token_span),
				),
			},
			_ => push_token(
				&mut arena,
				*stack.last().unwrap(),
				(token, token_span),
			),
		}
	}

	TokenTree {
		arena,
		order_by_appearance,
		contains_conditional_compilation: true,
	}
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
///  1| void foo() {
///  2|
///  3|     int i = 5;
///  4|
///  5|     #ifdef TOGGLE
///  6|     }
///  7|     void bar() {
///  8|     #endif
///  9|
/// 10|     int p = 0;
/// 11| }
/// ```
/// In the example above, if `TOGGLE` is not defined, we have a function `foo` who's scope ends on line `11` and
/// includes two variable declarations `i` and `p`. However, if `TOGGLE` is defined, the function `foo` ends on
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
/// such as the name, the starting position, etc. If we would encounter the conditional branching within this
/// parsing function, we would somehow need to be able to return up the call stack to split the parser, whilst also
/// somehow not loosing the temporary state. This should be technically possible, but it would make writing the
/// parsing code absolutely awful in many ways and that is not a trade-off I'm willing to take.
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
	/// The arena of [`TreeNode`]s.
	///
	/// # Invariants
	/// `[0]` always contains a value. If `contains_conditional_compilation` is `false`, this is:
	/// ```ignore
	/// TreeNode {
	///		parent: None,
	///		content: vec![Content::Tokens(entire_token_stream)],
	///	}
	/// ```
	arena: Vec<TreeNode>,
	/// IDs of the relevant nodes ordered by appearance.
	///
	/// - `0` - The ID of the `[n]`th conditional node,
	/// - `1` - The ID of the node which this conditional node depends on.
	///
	/// # Invariants
	/// If `contains_conditional_compilation` is `false`, this is empty.
	order_by_appearance: Vec<(NodeId, NodeId)>,

	/// Whether there are any conditional compilation brances.
	contains_conditional_compilation: bool,
}

impl TokenTree {
	/// Parses the root token stream.
	///
	/// Whilst this is guaranteed to succeed, if the entire source string is wrapped within a conditional block
	/// this will return an empty AST.
	///
	/// # Examples
	/// For a fully detailed example on how to use this method to create an abstract syntax tree, see the
	/// documentation for the [`parse_from_str()`] function.
	pub fn root(&self) -> ParseResult {
		// Get the relevant streams for the root branch.
		let streams = if !self.contains_conditional_compilation {
			// Panic: See invariant.
			match self.arena.get(0).unwrap().contents.first().unwrap() {
				Content::Tokens(s) => vec![s.clone()],
				Content::ConditionalBlock { .. } => unreachable!(),
			}
		} else {
			let mut streams = Vec::new();
			let node = self.arena.get(0).unwrap();
			for content in &node.contents {
				match content {
					Content::Tokens(s) => streams.push(s.clone()),
					Content::ConditionalBlock { .. } => {}
				}
			}

			streams
		};

		let mut walker = Walker::new(streams);
		let mut nodes = Vec::new();
		while !walker.is_done() {
			parse_stmt(&mut walker, &mut nodes);
		}

		(nodes, walker.syntax_diags, walker.syntax_tokens)
	}

	/// Parses a token tree by enabling conditional branches in the order of their appearance.
	///
	/// This method can return an `Err` in the following cases:
	/// - The `key` has a number which doesn't map to a conditional compilation branch,
	/// - The `key` has a number which depends on another number that is missing.
	///
	/// # Examples
	/// For a fully detailed example on how to use this method to create an abstract syntax tree, see the
	/// documentation for the [`parse_from_str()`] function.
	pub fn parse_by_order_of_appearance(
		&self,
		key: impl AsRef<[usize]>,
	) -> Result<ParseResult, ParseErr> {
		let order = key.as_ref();

		if !self.contains_conditional_compilation {
			return Err(ParseErr::NoConditionalBranches);
		}

		// Check that the key is valid.
		{
			let mut visited_node_ids = vec![0];
			for num in order {
				let (id, parent_id) = match self.order_by_appearance.get(*num) {
					Some(t) => t,
					None => return Err(ParseErr::InvalidNum(*num)),
				};

				if !visited_node_ids.contains(parent_id) {
					return Err(ParseErr::InvalidChain(*num));
				}

				visited_node_ids.push(*id);
			}
		}

		let mut key_idx = 0;
		let mut streams = Vec::new();
		let mut nodes = vec![(0, 0)];
		'outer: loop {
			// Get the ID of the conditional node that the current key points to.
			let current_key_node_id = {
				match order.get(key_idx) {
					Some(num) => match self.order_by_appearance.get(*num) {
						Some((arena_id, _)) => Some(*arena_id),
						// Panic: We have validated above that all the numbers are valid.
						None => unreachable!(),
					},
					None => None,
				}
			};

			let (node_id, content_idx) = nodes.last_mut().unwrap();
			let node = self.arena.get(*node_id).unwrap();

			// Consume the next content element in this node.
			while let Some(inner) = &node.contents.get(*content_idx) {
				*content_idx += 1;
				match inner {
					Content::Tokens(s) => streams.push(s.clone()),
					Content::ConditionalBlock { if_, elses, .. } => {
						// Check if any of the conditional branches match the current key number.
						if let Some(current_order_id) = current_key_node_id {
							if *if_ == current_order_id {
								nodes.push((*if_, 0));
								key_idx += 1;
								continue 'outer;
							} else {
								for (_, else_) in elses {
									if *else_ == current_order_id {
										nodes.push((*else_, 0));
										key_idx += 1;
										continue 'outer;
									}
								}
							}
						}
					}
				}
			}

			// We have consumed all the content of this node which means we can pop it from the stack and continue
			// with the parent node (if there is one).
			if nodes.len() > 1 {
				nodes.pop();
			} else {
				break 'outer;
			}
		}

		let mut walker = Walker::new(streams);
		let mut nodes = Vec::new();
		while !walker.is_done() {
			parse_stmt(&mut walker, &mut nodes);
		}

		Ok((nodes, walker.syntax_diags, walker.syntax_tokens))
	}

	/// TODO: Implement.
	#[allow(unused)]
	pub fn parse_by_order_of_nesting(
		&self,
		key: impl AsRef<[(usize, usize)]>,
	) -> Option<ParseResult> {
		todo!()
	}
}

type NodeId = usize;

/// A node within the token tree.
#[derive(Debug)]
struct TreeNode {
	#[allow(unused)]
	parent: Option<NodeId>,
	/// The contents of this node.
	contents: Vec<Content>,
}

/// This enum is used to group together tokens into logical groups.
///
/// Individual tokens are grouped together as much as possible within the [`Tokens`](Content::Tokens) variant,
/// until a [`ConditionalBlock`](Content::ConditionalBlock) is encountered. Once the block is over however, another
/// `Tokens` group is created.
#[derive(Debug)]
enum Content {
	/// A vector of tokens appearing one after another.
	Tokens(Vec<Spanned<Token>>),
	/// A conditional block. Each branch points to a node in the tree arena; each node contains further nested
	/// content.
	ConditionalBlock {
		/// Tokens by default are pushed into this node.
		if_: NodeId,
		/// This flag is set to `true` when we encounter an `elif`/`else`.
		completed_if: bool,
		/// If `completed_if` is set to `true`, tokens are pushed into the last node in this vector.
		elses: Vec<(Condition, NodeId)>,
	},
}

/// The type of an extra conditional branch.
#[derive(Debug)]
enum Condition {
	ElseIf,
	Else,
}

pub(crate) struct Walker {
	/// The token streams of the source string with the preselected conditional branches.
	source_streams: Vec<TokenStream>,
	/// The active token streams.
	///
	/// - `0` - The macro identifier, (for the root source stream this is just `""`),
	/// - `1` - The token stream,
	/// - `2` - The cursor.
	streams: Vec<(String, TokenStream, usize)>,

	/// The currently defined macros.
	///
	/// Key: The macro identifier.
	///
	/// Value:
	/// - `0` - The span of the identifier,
	/// - `1` - The body/replacement-list of tokens.
	macros: HashMap<String, (Span, TokenStream)>,
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
}

#[allow(unused)]
impl Walker {
	/// Constructs a new walker.
	fn new(mut token_streams: Vec<TokenStream>) -> Self {
		let mut active_macros = HashSet::new();
		// Invariant: A macro cannot have no name (an empty identifier), so this won't cause any hashing clashes
		// with valid macros. By using "" we can avoid having a special case for the root source stream.
		active_macros.insert("".into());

		let first_source = token_streams.remove(0); // Panic: Ensured by the caller.

		Self {
			source_streams: token_streams,
			streams: vec![("".into(), first_source, 0)],
			macros: HashMap::new(),
			macro_call_site: None,
			active_macros,
			syntax_diags: Vec::new(),
			semantic_diags: Vec::new(),
			syntax_tokens: Vec::new(),
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

	/// Peeks the next token without advancing the cursor; (returns the token under `cursor + 1`).
	/* fn lookahead_1(&self) -> Option<&Spanned<Token>> {
		let token = self.token_stream.get(self.cursor + 1);
		if let Some((token, _)) = token {
			match token {
				Token::Ident(s) => {
					if let Some((_, replacement_stream)) = self.macros.get(s) {
						if let Some(first_replacement_token) =
							replacement_stream.get(0)
						{
							return Some(first_replacement_token);
						}
						// FIXME: Deal with empty replacement stream.
					}
				}
				_ => {}
			}
		}

		token
	} */

	/// Peeks the next token without advancing the cursor whilst ignoring any comments.
	/* fn lookahead_1_ignore_comments(&self) -> Option<&Spanned<Token>> {
		// FIXME: replacement
		let mut cursor = self.cursor + 1;
		while let Some(i) = self.token_stream.get(cursor) {
			match i.0 {
				Token::LineComment(_)
				| Token::BlockComment {
					str: _,
					contains_eof: _,
				} => {
					cursor += 1;
					continue;
				}
				_ => return Some(i),
			}
		}
		None
	} */

	/// Advances the cursor by one.
	///
	/// This method correctly steps into/out-of macros, jumps between conditional compilation branches, and
	/// consumes any comments.
	/// FIXME: Implement function macro support here!!! Doesn't abide by expression parser's rules
	fn advance(&mut self) {
		let mut dont_increment = false;
		'outer: while let Some((identifier, stream, cursor)) =
			self.streams.last_mut()
		{
			if !dont_increment {
				*cursor += 1;
			}
			dont_increment = false;

			if *cursor == stream.len() {
				// We have reached the end of this stream. We close it and re-run the loop on the next stream (if
				// there is one).

				let ident = identifier.clone();
				if self.streams.len() == 1 {
					// If we aren't in a macro, that means we've finished the current source stream but there may
					// be another one, (since they can be split up due to conditional compilation).
					if self.source_streams.is_empty() {
						// We have reached the final end.
						self.streams.remove(0);
						break;
					} else {
						let mut next_source = self.source_streams.remove(0);
						let (_, s, c) = self.streams.get_mut(0).unwrap();
						std::mem::swap(s, &mut next_source);
						*c = 0;
						dont_increment = true;
						continue;
					}
				} else {
					// Panic: Anytime a stream is added the identifier is inserted into the set.
					self.active_macros.remove(&ident);
					self.streams.remove(self.streams.len() - 1);
					continue;
				}
			}

			let (token, token_span) = stream.get(*cursor).unwrap();

			match token {
				// We check if the new token is a macro call site.
				Token::Ident(s) => {
					if let Some((_, new_stream)) = self.macros.get(s) {
						if self.active_macros.contains(s) {
							// We have already visited a macro with this identifier. Recursion is not supported so
							// we don't continue.
							break;
						}

						let token_span = *token_span;

						if new_stream.is_empty() {
							// The macro is empty, so we want to move to the next token of the existing stream.
							self.push_semantic_diag(
								Semantic::EmptyMacroCallSite(token_span),
							);
							if self.streams.len() == 1 {
								// We only syntax highlight when it is the first macro call.
								self.syntax_tokens.push((
									SyntaxToken::ObjectMacro,
									token_span,
								));
							}
							continue;
						}

						let ident = s.to_owned();

						// We only syntax highlight and note the macro call site when it is the first macro call.
						if self.streams.len() == 1 {
							self.macro_call_site = Some(token_span);
							self.syntax_tokens
								.push((SyntaxToken::ObjectMacro, token_span));
						}

						self.active_macros.insert(ident.clone());
						self.streams.push((ident, new_stream.clone(), 0));

						// The first token in the new stream could be another macro call, so we re-run the loop on
						// this new stream in case.
						dont_increment = true;
						continue;
					}
					break;
				}
				// We want to consume any comments since they are semantically ignored.
				Token::LineComment(_) => {
					let token_span = *token_span;
					if self.streams.len() == 1 {
						// We only syntax highlight when we are not in a macro call.
						self.syntax_tokens
							.push((SyntaxToken::Comment, token_span));
					}
				}
				Token::BlockComment { .. } => {
					// TODO: Emit error if missing end.
					let token_span = *token_span;
					if self.streams.len() == 1 {
						// We only syntax highlight when we are not in a macro call.
						self.syntax_tokens
							.push((SyntaxToken::Comment, token_span));
					}
				}
				_ => break,
			}
		}

		if self.streams.len() <= 1 {
			self.macro_call_site = None;
		}
	}

	/// Returns the current token under the cursor and advances the cursor by one.
	///
	/// Equivalent to [`peek()`](Self::peek) followed by [`advance()`](Self::advance).
	/* fn next(&mut self) -> Option<Spanned<Token>> {
		// FIXME: replacement
		// If we are successful in getting the token, advance the cursor.
		match self.token_stream.get(self.cursor) {
			Some(i) => {
				self.cursor += 1;
				Some(i.clone())
			}
			None => None,
		}
	} */

	/// Registers a define macro. Note: currently only supports object-like macros.
	fn register_macro(&mut self, ident: Spanned<String>, tokens: TokenStream) {
		if let Some(_prev) = self.macros.insert(ident.0, (ident.1, tokens)) {
			// TODO: Emit error if the macros aren't identical (will require scanning the tokenstream to compare).
		}
	}

	/// Un-registers a defined macro. Note: currently only supports object-like macros.
	fn unregister_macro(&mut self, ident: String, span: Span) {
		match self.macros.remove(&ident) {
			Some(_) => self.colour(span, SyntaxToken::ObjectMacro),
			None => {
				self.push_semantic_diag(Semantic::UndefMacroNameUnresolved(
					span,
				));
				self.colour(span, SyntaxToken::Unresolved);
			}
		}
	}

	/// Pushes a syntax diagnostic.
	pub(crate) fn push_syntax_diag(&mut self, diag: Syntax) {
		self.syntax_diags.push(diag);
	}

	/// Appends a collection of syntax diagnostics.
	fn append_syntax_diags(&mut self, diags: &mut Vec<Syntax>) {
		self.syntax_diags.append(diags);
	}

	/// Pushes a semantic diagnostic.
	pub(crate) fn push_semantic_diag(&mut self, diag: Semantic) {
		self.semantic_diags.push(diag);
	}

	/// Creates a syntax highlighting token over the given span.
	fn colour(&mut self, span: Span, token: SyntaxToken) {
		// When we are within a macro, we don't want to produce syntax tokens.
		// Note: This functionality is duplicated in the `ShuntingYard::colour()` method.
		if self.streams.len() == 1 {
			self.syntax_tokens.push((token, span));
		}
	}

	/// Appends a collection of syntax highlighting tokens.
	fn append_colours(&mut self, colours: &mut Vec<Spanned<SyntaxToken>>) {
		self.syntax_tokens.append(colours);
	}

	/// Returns whether the walker has reached the end of the token streams.
	fn is_done(&self) -> bool {
		self.streams.is_empty()
	}

	/* /// Returns the [`Span`] of the current `Token`.
	///
	/// *Note:* If we have reached the end of the tokens, this will return the value of
	/// [`get_last_span()`](Self::get_last_span).
	fn get_current_span(&self) -> Span {
		// FIXME: replacement
		match self.token_stream.get(self.cursor) {
			Some(t) => t.1,
			None => self.get_last_span(),
		}
	} */

	/* /// Returns the [`Span`] of the previous `Token`.
	///
	/// *Note:* If the current token is the first, the span returned will be `0-0`.
	fn get_previous_span(&self) -> Span {
		// FIXME: replacement
		self.token_stream
			.get(self.cursor - 1)
			.map_or(Span::new_zero_width(0), |t| t.1)
	} */

	/* /// Returns the [`Span`] of the last `Token`.
	///
	/// *Note:* If there are no tokens, the span returned will be `0-0`.
	fn get_last_span(&self) -> Span {
		// FIXME: replacement
		self.token_stream
			.last()
			.map_or(Span::new_zero_width(0), |t| t.1)
	} */
}

/* STATEMENT PARSING LOGIC BELOW */

/// Parses an individual statement at the current position.
fn parse_stmt(walker: &mut Walker, nodes: &mut Vec<ast::Node>) {
	use crate::lexer::preprocessor::{self, DefineToken, UndefToken};

	let (token, token_span) = walker.get().expect("This function should be called from a loop that checks this invariant!");

	match token {
		Token::Semi => {
			walker.colour(token_span, SyntaxToken::Punctuation);
			walker.advance();
			nodes.push(Node {
				span: token_span,
				ty: NodeTy::Empty,
			});
		}
		Token::Directive(dir) => match dir {
			PreprocStream::Define {
				kw: kw_span,
				mut ident_tokens,
				body_tokens,
			} => {
				walker.colour(token_span.first_char(), SyntaxToken::Directive);
				walker.colour(kw_span, SyntaxToken::Directive);

				if ident_tokens.is_empty() {
					// We have a macro that's missing a name.

					walker.push_syntax_diag(Syntax::PreprocDefine(
						PreprocDefineDiag::DefineExpectedMacroName(
							kw_span.next_single_width(),
						),
					));
					body_tokens.iter().for_each(|(_, s)| {
						walker.colour(*s, SyntaxToken::Invalid)
					});
				} else if ident_tokens.len() == 1 {
					// We have an object-like macro.

					let ident = match ident_tokens.remove(0) {
						(DefineToken::Ident(s), span) => (s, span),
						_ => unreachable!(),
					};
					walker.colour(ident.1, SyntaxToken::ObjectMacro);

					// Since object-like macros don't have parameters, we can perform the concatenation right here
					// since we know the contents of the macro body will never change.
					let body_tokens = preprocessor::concat_object_macro_body(
						walker,
						body_tokens,
					);
					body_tokens.iter().for_each(|(t, s)| {
						walker.colour(*s, t.non_semantic_colour())
					});
					walker.register_macro(ident, body_tokens);
				} else {
					// We have a function-like macro.
					// TODO: Implement
				}

				walker.advance();
			}
			PreprocStream::Undef {
				kw: kw_span,
				mut tokens,
			} => {
				walker.colour(token_span.first_char(), SyntaxToken::Directive);
				walker.colour(kw_span, SyntaxToken::Directive);

				if tokens.is_empty() {
					walker.push_syntax_diag(Syntax::PreprocDefine(
						PreprocDefineDiag::UndefExpectedMacroName(
							kw_span.next_single_width(),
						),
					));
				} else {
					let (token, token_span) = tokens.remove(0);

					match token {
						UndefToken::Ident(s) => {
							walker.unregister_macro(s, token_span)
						}
						_ => {
							walker.push_syntax_diag(Syntax::PreprocDefine(
								PreprocDefineDiag::UndefExpectedMacroName(
									token_span,
								),
							));
						}
					}

					if !tokens.is_empty() {
						let (_, first) = tokens.first().unwrap();
						let (_, last) = tokens.last().unwrap();
						walker.push_syntax_diag(Syntax::PreprocTrailingTokens(
							Span::new(first.start, last.end),
						));
					}
				}

				walker.advance();
			}
			_ => {
				walker.advance();
			}
		},
		Token::Break => parse_break_continue_discard(
			walker,
			nodes,
			token_span,
			|| NodeTy::Break,
			|span| Syntax::Stmt(StmtDiag::ExpectedSemiAfterBreakKw(span)),
		),
		Token::Continue => parse_break_continue_discard(
			walker,
			nodes,
			token_span,
			|| NodeTy::Continue,
			|span| Syntax::Stmt(StmtDiag::ExpectedSemiAfterContinueKw(span)),
		),
		Token::Discard => parse_break_continue_discard(
			walker,
			nodes,
			token_span,
			|| NodeTy::Discard,
			|span| Syntax::Stmt(StmtDiag::ExpectedSemiAfterDiscardKw(span)),
		),
		Token::Return => parse_return(walker, nodes, token_span),
		_ => {
			walker.advance();
		}
	}
}

/// Parses a break/continue/discard statement.
///
/// This assumes that the keyword is not yet consumed.
fn parse_break_continue_discard(
	walker: &mut Walker,
	nodes: &mut Vec<Node>,
	kw_span: Span,
	ty: impl FnOnce() -> NodeTy,
	error: impl FnOnce(Span) -> Syntax,
) {
	walker.colour(kw_span, SyntaxToken::Keyword);
	walker.advance();

	// Consume the `;` to end the statement.
	let semi_span = match walker.peek() {
		Some((token, token_span)) => {
			if *token == Token::Semi {
				walker.colour(token_span, SyntaxToken::Punctuation);
				walker.advance();
				Some(token_span)
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

/// Parses a break/continue/discard statement.
///
/// This assumes that the keyword is not yet consumed.
fn parse_return(walker: &mut Walker, nodes: &mut Vec<Node>, kw_span: Span) {
	walker.colour(kw_span, SyntaxToken::Keyword);
	walker.advance();

	// Look for the optional return value expression.
	let return_expr = match expr_parser(walker, Mode::Default, [Token::Semi]) {
		(Some(expr), mut diags, mut colours) => {
			walker.append_syntax_diags(&mut diags);
			walker.append_colours(&mut colours);
			Some(expr)
		}
		(None, _, _) => None,
	};

	// Consume the `;` to end the statement.
	let semi_span = match walker.peek() {
		Some((token, token_span)) => {
			if *token == Token::Semi {
				walker.colour(token_span, SyntaxToken::Punctuation);
				walker.advance();
				Some(token_span)
			} else {
				None
			}
		}
		None => None,
	};

	if semi_span.is_none() {
		if let Some(ref return_expr) = return_expr {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ExpectedSemiAfterReturnExpr(
					return_expr.span.next_single_width(),
				),
			));
		} else {
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::ExpectedSemiOrExprAfterReturnKw(
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
