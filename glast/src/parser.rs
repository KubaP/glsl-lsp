pub mod ast;
mod expression;
mod syntax;

pub use syntax::*;

use crate::{
	diag::{
		ExprDiag, PreprocConditionalDiag, PreprocDefineDiag, Semantic,
		StmtDiag, Syntax,
	},
	lexer::{
		preprocessor::TokenStream as PreprocStream, OpTy, Token, TokenStream,
	},
	Either, Span, Spanned,
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
			syntax_diags: vec![],
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
	let mut syntax_diags = Vec::new();

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
							syntax_diags.push(Syntax::PreprocConditional(
								PreprocConditionalDiag::UnmatchedElseIf(
									token_span,
								),
							));
						}
					} else {
						syntax_diags.push(Syntax::PreprocConditional(
							PreprocConditionalDiag::UnmatchedElseIf(token_span),
						));
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
							syntax_diags.push(Syntax::PreprocConditional(
								PreprocConditionalDiag::UnmatchedElse(
									token_span,
								),
							));
						}
					} else {
						syntax_diags.push(Syntax::PreprocConditional(
							PreprocConditionalDiag::UnmatchedElse(token_span),
						));
					}
				}
				PreprocStream::EndIf { .. } => {
					if stack.len() > 1 {
						stack.pop();
					} else {
						syntax_diags.push(Syntax::PreprocConditional(
							PreprocConditionalDiag::UnmatchedEndIf(token_span),
						));
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
		syntax_diags,
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

	/// Syntax diagnostics related to conditional compilation directives.
	///
	/// # Invariants
	/// If `contains_conditional_compilation` is `false`, this is empty.
	#[allow(unused)]
	syntax_diags: Vec<Syntax>,

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

	/// The last span in the source string.
	last_span: Span,
}

#[allow(unused)]
impl Walker {
	/// Constructs a new walker.
	fn new(mut token_streams: Vec<TokenStream>) -> Self {
		let mut active_macros = HashSet::new();
		// Invariant: A macro cannot have no name (an empty identifier), so this won't cause any hashing clashes
		// with valid macros. By using "" we can avoid having a special case for the root source stream.
		active_macros.insert("".into());

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
	///
	/// FIXME: Implement function macro support here!!! Doesn't abide by expression parser's rules
	fn move_cursor(
		source_streams: &mut Vec<TokenStream>,
		streams: &mut Vec<(String, TokenStream, usize)>,
		macros: &mut HashMap<String, (Span, TokenStream)>,
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
					if let Some((_, new_stream)) = macros.get(s) {
						if active_macros.contains(s) {
							// We have already visited a macro with this identifier. Recursion is not supported so
							// we don't continue.
							break;
						}

						let token_span = *token_span;

						if new_stream.is_empty() {
							// The macro is empty, so we want to move to the next token of the existing stream.
							semantic_diags
								.push(Semantic::EmptyMacroCallSite(token_span));
							if streams.len() == 1 {
								// We only syntax highlight when it is the first macro call.
								syntax_tokens.push((
									SyntaxToken::ObjectMacro,
									token_span,
								));
							}
							continue;
						}

						let ident = s.to_owned();

						// We only syntax highlight and note the macro call site when it is the first macro call.
						if streams.len() == 1 {
							*macro_call_site = Some(token_span);
							syntax_tokens
								.push((SyntaxToken::ObjectMacro, token_span));
						}

						active_macros.insert(ident.clone());
						streams.push((ident, new_stream.clone(), 0));

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

	/// Registers a define macro. Note: currently only supports object-like macros.
	fn register_macro(&mut self, ident: Spanned<String>, tokens: TokenStream) {
		if let Some(_prev) = self.macros.insert(ident.0, (ident.1, tokens)) {
			// TODO: Emit error if the macros aren't identical (will require scanning the tokenstream to compare).
		}
	}

	/// Un-registers a defined macro. Note: currently only supports object-like macros.
	fn unregister_macro(&mut self, ident: String, span: Span) {
		match self.macros.remove(&ident) {
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

	/// Pushes a syntax highlighting token over the given span.
	fn push_colour(&mut self, span: Span, token: SyntaxToken) {
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
				if token.starts_statement() {
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

	let (token, token_span) = walker.get().expect("This function should be called from a loop that checks this invariant!");

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
			parse_directive(walker, stream, token_span);
			walker.advance();
		}
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
				loop {
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
							break;
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
						Mode::Default,
						[Token::RParen],
					) {
						(Some(e), mut diags, mut colours) => {
							walker.append_colours(&mut colours);
							walker.append_syntax_diags(&mut diags);
							e
						}
						(None, _, _) => {
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

					layouts.push(Layout {
						span: Span::new(layout_span_start, value_expr.span.end),
						ty: constructor(Some(value_expr)),
					});
				}

				continue;
			}
			_ => break,
		}
		walker.advance();
	}

	qualifiers
}

/// Tries to parse a variable/function definition/declaration or an expression statement.
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
	let (start, mut start_diags, mut start_colours) =
		match expr_parser(walker, Mode::Default, [Token::Semi]) {
			(Some(expr), diags, colours) => (expr, diags, colours),
			(None, _, _) => {
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
		// `foobar`, `int`, `vec2[3]`, `MyStruct` etc. This can be the type part of a definition/declaration, but
		// it could be just an expression statement depending on what comes next.

		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We lack any identifiers necessary for a definition/declaration, so this must be an expression
				// statement.
				invalidate_qualifiers(walker, qualifiers);
				walker.append_colours(&mut start_colours);
				walker.append_syntax_diags(&mut start_diags);
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

		// Check whether we have a function definition/declaration, or whether this is an expression immediately
		// followed by a semi-colon.
		match token {
			Token::Ident(i) => match walker.lookahead_1() {
				Some(next) => match next.0 {
					Token::LParen => {
						// We have a function definition/declaration.
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
				walker.append_syntax_diags(&mut start_diags);
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
				walker.append_syntax_diags(&mut start_diags);
				nodes.push(Node {
					span: start.span,
					ty: NodeTy::Expr(start),
				});
				return;
			}
			_ => {}
		}

		// We don't have a function definition/declaration, so this must be a variable definition/declaration or an
		// expression statement.

		// We attempt to parse an expression for the identifier(s).
		let (ident_expr, mut ident_diags, mut ident_colours) =
			match expr_parser(walker, Mode::BreakAtEq, [Token::Semi]) {
				(Some(e), diags, colours) => (e, diags, colours),
				(None, _, _) => {
					// We have an expression followed by neither another expression nor a semi-colon. We treat this
					// as an expression statement since that's the closest possible match.
					invalidate_qualifiers(walker, qualifiers);
					walker.append_colours(&mut start_colours);
					walker.append_syntax_diags(&mut start_diags);
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
			// to one or more identifiers for a variable definition/declaration. We treat the first expression as
			// an expression statement, and the second expression as invalid.
			invalidate_qualifiers(walker, qualifiers);
			walker.append_colours(&mut start_colours);
			walker.append_syntax_diags(&mut start_diags);
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
		start_diags.retain(|e| {
			if let Syntax::Expr(ExprDiag::FoundOperandAfterOperand(_, _)) = e {
				false
			} else {
				true
			}
		});
		type_.qualifiers = qualifiers;
		walker.append_colours(&mut start_colours);
		walker.append_syntax_diags(&mut start_diags);
		walker.append_colours(&mut ident_colours);
		walker.append_syntax_diags(&mut ident_diags);

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

		fn var_decl(
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
						ty: NodeTy::VarDecl {
							type_,
							ident,
							value,
						},
					}
				}
				_ => Node {
					span,
					ty: NodeTy::VarDecls(vars, value),
				},
			}
		}

		// Consume the `;` for a definition, or a `=` for a declaration.
		let (token, token_span) = match walker.peek() {
			Some(t) => t,
			None => {
				// We have something that matches the start of a variable definition/declaration. Since we have
				// neither the `;` or `=`, we assume that this is a definition which is missing the semi-colon.
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
			// We have a variable definition.
			let semi_span = token_span;
			walker.push_colour(semi_span, SyntaxToken::Punctuation);
			walker.advance();
			nodes.push(var_def(type_, ident_info, semi_span.end));
			return;
		} else if *token == Token::Op(crate::lexer::OpTy::Eq) {
			// We have a variable declaration.
			let eq_span = token_span;
			walker.push_colour(eq_span, SyntaxToken::Operator);
			walker.advance();

			// Consume the value expression.
			let value_expr =
				match expr_parser(walker, Mode::Default, [Token::Semi]) {
					(Some(e), mut diags, mut colours) => {
						walker.append_colours(&mut colours);
						walker.append_syntax_diags(&mut diags);
						e
					}
					(None, _, _) => {
						walker.push_syntax_diag(Syntax::Stmt(
							StmtDiag::VarDeclExpectedValueAfterEq(
								eq_span.next_single_width(),
							),
						));
						nodes.push(var_decl(
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
						StmtDiag::VarDeclExpectedSemiAfterValue(
							value_span.next_single_width(),
						),
					));
					nodes.push(var_decl(
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
				nodes.push(var_decl(
					type_,
					ident_info,
					Some(value_expr),
					semi_span.end,
				));
				return;
			} else {
				let end_span = token_span;
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::VarDeclExpectedSemiAfterValue(
						end_span.next_single_width(),
					),
				));
				nodes.push(var_decl(
					type_,
					ident_info,
					Some(value_expr),
					end_span.end,
				));
				seek_next_stmt(walker);
				return;
			}
		} else {
			// We have something that matches the start of a variable definition/declaration. Since we have neither
			// the `;` or `=`, we assume that this is a definition which is missing the semi-colon.
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

	// We have an expression which cannot be parsed as a type, so this cannot start a definition/declaration; it
	// must therefore be a standalone expression statement.
	let expr = start;
	walker.append_colours(&mut start_colours);
	walker.append_syntax_diags(&mut start_diags);

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

/// Parses a function definition/declaration.
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
				// We have not yet finished parsing the parameter list, but we treat this as a valid definition
				// since that's the closest match.
				let span = Span::new(return_type.span.start, prev_span.end);
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ParamsExpectedRParen(
						prev_span.next_single_width(),
					),
				));
				nodes.push(Node {
					span,
					ty: NodeTy::FnDef {
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
				break token_span;
			}
			Token::Semi => {
				walker.push_colour(token_span, SyntaxToken::Punctuation);
				walker.advance();
				// We have not yet finished parsing the parameter list but we've encountered a semi-colon. We treat
				// this as a valid definition since that's the closest match.
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::ParamsExpectedRParen(
						prev_span.next_single_width(),
					),
				));
				nodes.push(Node {
					span: Span::new(return_type.span.start, token_span.end),
					ty: NodeTy::FnDef {
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
				// this as a potentially valid declaration since that's the closest match.
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

		// Consume the type.
		let type_ = match expr_parser(
			walker,
			Mode::TakeOneUnit,
			[Token::Semi, Token::LBrace],
		) {
			(Some(e), _, mut colours) => {
				if let Some(type_) = Type::parse(&e) {
					walker.append_colours(&mut colours);
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
			(None, _, _) => {
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
			(Some(e), _, colours) => (e, colours),
			(None, _, _) => {
				// We have a first expression and then something that is not an expression. We treat this as an
				// ident-less parameter, whatever the current token is will be dealt with in the next iteration.
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
			// to an identifier for the parameter. We treat the first type expression as an ident-less parameter,
			// and the second expression as invalid.
			let param_span = Span::new(param_span_start, type_.span.end);
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

	// Consume the `;` for a definition or a `{` for a declaration.
	let (token, token_span) = match walker.peek() {
		Some(t) => t,
		None => {
			// This branch will only be triggered if we exited the param loop with a `)`, it will not trigger if we
			// exit with a `{` because that token is not consumed.

			// We are missing a `;` for a definition. We treat this as a definition since that's the closest match.
			walker.push_syntax_diag(Syntax::Stmt(
				StmtDiag::FnExpectedSemiOrLBraceAfterParams(
					param_end_span.next_single_width(),
				),
			));
			nodes.push(Node {
				span: Span::new(return_type.span.start, param_end_span.end),
				ty: NodeTy::FnDef {
					return_type,
					ident,
					params,
				},
			});
			return;
		}
	};
	if *token == Token::Semi {
		// We have a definition.
		walker.push_colour(token_span, SyntaxToken::Punctuation);
		walker.advance();
		nodes.push(Node {
			span: Span::new(return_type.span.start, param_end_span.end),
			ty: NodeTy::FnDef {
				return_type,
				ident,
				params,
			},
		});
	} else if *token == Token::LBrace {
		// We have a declaration.
		let l_brace_span = token_span;
		walker.push_colour(l_brace_span, SyntaxToken::Punctuation);
		walker.advance();
		let body = parse_scope(walker, BRACE_SCOPE, l_brace_span);
		nodes.push(Node {
			span: Span::new(return_type.span.start, body.span.end),
			ty: NodeTy::FnDecl {
				return_type,
				ident,
				params,
				body,
			},
		});
	} else {
		// We are missing a `;` for a definition. We treat this as a definition since that's the closest match.
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::FnExpectedSemiOrLBraceAfterParams(
				param_end_span.next_single_width(),
			),
		));
		nodes.push(Node {
			span: Span::new(return_type.span.start, param_end_span.end),
			ty: NodeTy::FnDef {
				return_type,
				ident,
				params,
			},
		});
		seek_next_stmt(walker);
	}
}

/// Parses a struct definition/declaration.
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
		(Some(e), _, mut colours) => match e.ty {
			ExprTy::Ident(i) => {
				walker.append_colours(&mut colours);
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
		(None, _, _) => {
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
			// We don't create a struct definition because it would result in two errors that would reduce clarity.
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
		// We have a definition (which is illegal).
		let span = Span::new(struct_span_start, token_span.end);
		walker.push_colour(token_span, SyntaxToken::Punctuation);
		walker
			.push_syntax_diag(Syntax::Stmt(StmtDiag::StructDefIsInvalid(span)));
		walker.advance();
		nodes.push(Node {
			span,
			ty: NodeTy::StructDef { qualifiers, ident },
		});
		return;
	} else {
		// We don't create a struct definition because it would result in two errors that would reduce clarity.
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::StructExpectedLBraceAfterIdent(
				ident.span.next_single_width(),
			),
		));
		return;
	};

	// Parse the contents of the body.
	let body = parse_scope(walker, BRACE_SCOPE, l_brace_span);
	for stmt in &body.contents {
		match &stmt.ty {
			NodeTy::VarDef { .. }
			| NodeTy::VarDecl { .. }
			| NodeTy::VarDefs(_)
			| NodeTy::VarDecls(_, _) => {}
			_ => {
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::StructInvalidStmtInBody(stmt.span),
				));
			}
		}
	}

	// Look for an optional instance identifier.
	let instance = match expr_parser(walker, Mode::TakeOneUnit, [Token::Semi]) {
		(Some(e), _, mut colours) => match e.ty {
			ExprTy::Ident(i) => {
				walker.append_colours(&mut colours);
				Omittable::Some(i)
			}
			_ => {
				walker.append_colours(&mut colours);
				walker.push_syntax_diag(Syntax::Stmt(
					StmtDiag::StructExpectedInstanceOrSemiAfterBody(e.span),
				));
				nodes.push(Node {
					span: Span::new(struct_span_start, body.span.end),
					ty: NodeTy::StructDecl {
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
		walker.push_syntax_diag(Syntax::Stmt(
			StmtDiag::StructExpectedSemiAfterBodyOrInstance(
				if let Omittable::Some(ref i) = instance {
					i.span.next_single_width()
				} else {
					body.span.next_single_width()
				},
			),
		));
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
		ty: NodeTy::StructDecl {
			qualifiers,
			ident,
			body,
			instance,
		},
	});
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
		(Some(e), mut diags, mut colours) => {
			walker.append_colours(&mut colours);
			walker.append_syntax_diags(&mut diags);
			Some(e)
		}
		(None, _, _) => {
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
						(Some(e), mut diags, mut colours) => {
							walker.append_colours(&mut colours);
							walker.append_syntax_diags(&mut diags);
							Some(e)
						}
						(None, _, _) => {
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

		let mut stmt = Vec::new();
		try_parse_definition_declaration_expr(
			walker,
			&mut stmt,
			vec![],
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
		}
		counter += 1;
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
		(Some(e), mut diags, mut colours) => {
			walker.append_colours(&mut colours);
			walker.append_syntax_diags(&mut diags);
			Some(e)
		}
		(None, _, _) => {
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
		(Some(e), mut diags, mut colours) => {
			walker.append_colours(&mut colours);
			walker.append_syntax_diags(&mut diags);
			Some(e)
		}
		(None, _, _) => {
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
				StmtDiag::WhileExpectedLParenAfterKw(span.next_single_width()),
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
		(Some(expr), mut diags, mut colours) => {
			walker.append_syntax_diags(&mut diags);
			walker.append_colours(&mut colours);
			Omittable::Some(expr)
		}
		(None, _, _) => Omittable::None,
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
fn parse_directive(walker: &mut Walker, stream: PreprocStream, dir_span: Span) {
	use crate::lexer::preprocessor::{self, DefineToken, UndefToken};

	match stream {
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
					(DefineToken::Ident(s), span) => (s, span),
					_ => unreachable!(),
				};
				walker.push_colour(ident.1, SyntaxToken::ObjectMacro);

				// Since object-like macros don't have parameters, we can perform the concatenation right here
				// since we know the contents of the macro body will never change.
				let body_tokens =
					preprocessor::concat_object_macro_body(walker, body_tokens);
				body_tokens.iter().for_each(|(t, s)| {
					walker.push_colour(*s, t.non_semantic_colour())
				});
				walker.register_macro(ident, body_tokens);
			} else {
				// We have a function-like macro.
				// TODO: Implement
			}
		}
		PreprocStream::Undef {
			kw: kw_span,
			mut tokens,
		} => {
			walker.push_colour(dir_span.first_char(), SyntaxToken::Directive);
			walker.push_colour(kw_span, SyntaxToken::Directive);

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
		}
		_ => {}
	}
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
