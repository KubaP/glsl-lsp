//! Contains types for representing source files.

use glast::{
	parser::{ParseResult, TokenTree},
	Span,
};
use tower_lsp::{
	lsp_types::{Position, Range, Url},
	Client,
};

/// A GLSL source file.
pub struct File {
	/// The uri of this file.
	pub uri: Url,
	/// The current version number of this file.
	pub version: i32,
	/// A character index-to-line conversion table.
	///
	/// - `0` - Line number, (same as vector index).
	/// - `1` - Character index which starts at the line number.
	pub lines: Vec<(usize, usize)>,
	/// The configuration of this file.
	pub config: FileConfig,
	/// The cached data of the parsing operation.
	pub cache: Option<(TokenTree, ParseResult)>,
	/// This will be `Some` if `self.config.conditional_compilation_state == Evaluate`.
	pub chosen_key: Option<Vec<usize>>,
}

impl File {
	/// Constructs a new file with the specified contents.
	pub fn new(
		uri: Url,
		version: i32,
		contents: String,
		mut config: FileConfig,
	) -> Self {
		let (cache, chosen_key) = match Self::parse(&mut config, &contents) {
			Some((a, b, chosen_key)) => (Some((a, b)), chosen_key),
			None => (None, None),
		};
		Self {
			uri,
			version,
			lines: Self::generate_line_table(&contents),
			config,
			cache,
			chosen_key,
		}
	}

	/// Updates the file with new content, and performs any necessary recalculations.
	pub fn update_contents(&mut self, version: i32, contents: String) {
		self.version = version;
		self.lines = Self::generate_line_table(&contents);
		let (cache, chosen_key) = match Self::parse(&mut self.config, &contents)
		{
			Some((a, b, chosen_key)) => (Some((a, b)), chosen_key),
			None => (None, None),
		};
		self.cache = cache;
		self.chosen_key = chosen_key;
	}

	/// Updates the configuration of the file, and re-parses it if necessary.
	pub fn update_config(&mut self, config: FileConfig) {
		self.config = config;
		let Some(cache) = &mut self.cache else { return; };
		let (parse_result, chosen_key) = match &self
			.config
			.conditional_compilation_state
		{
			ConditionalCompilationState::Off => {
				(cache.0.root(self.config.syntax_highlight_entire_file), None)
			}
			ConditionalCompilationState::Evaluate => {
				let (a, b) =
					cache.0.evaluate(self.config.syntax_highlight_entire_file);
				(a, Some(b))
			}
			ConditionalCompilationState::Key(key) => {
				match cache
					.0
					.with_key(key, self.config.syntax_highlight_entire_file)
				{
					Ok(p) => (p, None),
					Err(_) => return,
				}
			}
		};
		cache.1 = parse_result;
		self.chosen_key = chosen_key;
	}

	fn parse(
		config: &mut FileConfig,
		contents: &str,
	) -> Option<(TokenTree, ParseResult, Option<Vec<usize>>)> {
		let Ok(tree) = glast::parser::parse_from_str(contents) else { return None; };
		let (parse_result, chosen_key) = match &config
			.conditional_compilation_state
		{
			ConditionalCompilationState::Off => {
				(tree.root(config.syntax_highlight_entire_file), None)
			}
			ConditionalCompilationState::Evaluate => {
				let (a, b) = tree.evaluate(config.syntax_highlight_entire_file);
				(a, Some(b))
			}
			ConditionalCompilationState::Key(key) => {
				match tree.with_key(key, config.syntax_highlight_entire_file) {
					Ok(p) => (p, None),
					Err(_) => return None,
				}
			}
		};

		Some((tree, parse_result, chosen_key))
	}

	/// Converts a [`Span`] to an LSP [`Range`] type.
	pub fn span_to_lsp(&self, span: Span) -> Range {
		let mut start = (0, 0);
		let mut end = (0, 0);

		for (a, b) in self.lines.iter().zip(self.lines.iter().skip(1)) {
			if a.1 <= span.start && span.start < b.1 {
				start = (a.0, span.start - a.1);
			}
			if a.1 <= span.end && span.end < b.1 {
				end = (a.0, span.end - a.1);
				break;
			}
		}

		#[cfg(debug_assertions)]
		assert!(
			end.0 >= start.0,
			"[File::span_to_range] The `end` is on a line number earlier than the `start`."
		);

		Range {
			start: Position::new(start.0 as u32, start.1 as u32),
			end: Position::new(end.0 as u32, end.1 as u32),
		}
	}

	/// Converts a [`Span`]'s position to an LSP [`Position`] type.
	pub fn position_to_lsp(&self, position: usize) -> Position {
		let mut start = (0, 0);
		for (a, b) in self.lines.iter().zip(self.lines.iter().skip(1)) {
			if a.1 <= position && position < b.1 {
				start = (a.0, position - a.1);
			}
		}

		Position::new(start.0 as u32, start.1 as u32)
	}

	/// Converts an LSP [`Position`] to a [`Span`]'s position.
	pub fn position_from_lsp(&self, position: Position) -> usize {
		let (_, char_offset) = self.lines.get(position.line as usize).unwrap();

		*char_offset + position.character as usize
	}

	/// Generates a conversion table based of the contents string.
	fn generate_line_table(contents: &str) -> Vec<(usize, usize)> {
		let mut lines = Vec::new();
		lines.push((0, 0));

		let mut line = 1;
		let mut i = 0;
		let mut chars = contents.chars();
		loop {
			let c = match chars.next() {
				Some(c) => c,
				None => break,
			};

			if c == '\n' {
				// Push a new line at the position of the character after `\n`.
				i += 1;
				lines.push((line, i));
				line += 1;
			} else if c == '\r' {
				i += 1;

				let next = match chars.next() {
					Some(c) => c,
					None => {
						// Push a line at the position of the character after `\r`.
						lines.push((line, i));
						line += 1;
						break;
					}
				};

				// Push a new line at the position of the character after `\r\n`.
				if next == '\n' {
					i += 1;
					lines.push((line, i));
					line += 1;
				} else {
					// Push a line at the position of the character after `\r`.
					lines.push((line, i));
					line += 1;
				}
			} else {
				i += 1;
			}
		}
		// Add a final zero-sized line at the very end. This effectively treats the previous line that was just
		// added in the loop to extend from it's starting index to infinity.
		//
		// Note: We do this because in the `span_to_range()` method, we iterate over the lines in pairs, and
		// without this "final" line, we wouldn't be able to correctly translate a span on the very last line. The
		// reason why we iterate over in pairs is because that reduces copies; the alternative would be to keep
		// `previous_*` counters outside of the loop and write to them, but that has unnecessary overhead.
		lines.push((line, usize::MAX));

		lines
	}
}

/// A file configuration.
///
/// This stores all per-directory/per-file settings that are relevant to a file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileConfig {
	pub conditional_compilation_state: ConditionalCompilationState,
	pub syntax_highlight_entire_file: bool,
}

/// The state of conditional compilation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConditionalCompilationState {
	/// Conditional compilation is disabled.
	Off,
	/// Conditional compilation is evaluated.
	Evaluate,
	/// Conditional compilation is enabled using the specified key.
	Key(Vec<usize>),
}

/// Returns the up-to-date file configuration for a given uri. This takes into account fine-grained configuration
/// settings on a per-directory/per-file basis.
pub async fn get_file_config(client: &Client, uri: &Url) -> FileConfig {
	use tower_lsp::lsp_types::{
		request::WorkspaceConfiguration, ConfigurationItem, ConfigurationParams,
	};

	// Send the `workspace/configuration` request and wait for a response.
	let result = client
		.send_request::<WorkspaceConfiguration>(ConfigurationParams {
			items: vec![
				ConfigurationItem {
					scope_uri: Some(uri.clone()),
					section: Some("glsl.conditionalCompilation.state".into()),
				},
				ConfigurationItem {
					scope_uri: Some(uri.clone()),
					section: Some(
						"glsl.syntaxHighlighting.highlightEntireFile".into(),
					),
				},
			],
		})
		.await;

	// Panic: The client handler always returns a vector of the same length as the request.
	// See `configurationRequest()` in `main.ts`.
	let Ok(mut result) = result else { unreachable!(); };
	// Even though the vscode client package manifest sets a type for each configuration setting, the returned
	// value can be of any type, so we need to deal with incorrect types through a default value.
	let conditional_compilation_state =
		match result.remove(0).as_str().unwrap_or("") {
			"off" => ConditionalCompilationState::Off,
			"evaluate" => ConditionalCompilationState::Evaluate,
			_ => ConditionalCompilationState::Off,
		};
	let syntax_highlight_entire_file =
		result.remove(0).as_bool().unwrap_or(false);

	FileConfig {
		conditional_compilation_state,
		syntax_highlight_entire_file,
	}
}
