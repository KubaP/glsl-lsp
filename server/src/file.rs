use glast::Span;
use tower_lsp::{
	lsp_types::{Position, Range, Url},
	Client,
};

/// A GLSL source file.
#[derive(Debug)]
pub struct File {
	/// The url of this file.
	pub uri: Url,
	/// The version number of this file.
	pub version: i32,
	/// Contents of this file.
	pub contents: String,
	/// A character-index to line conversion table.
	///
	/// - `0` - Line number, (same as vector index).
	/// - `1` - Character index which starts at the line number.
	pub lines: Vec<(usize, usize)>,
}

impl File {
	/// Constructs a new file with the specified contents.
	pub fn new(uri: Url, version: i32, contents: String) -> Self {
		Self {
			uri,
			version,
			lines: Self::generate_line_table(&contents),
			contents,
		}
	}

	/// Updates the file with new content, and performs any necessary recalculations.
	pub fn update(&mut self, version: i32, contents: String) {
		self.version = version;
		self.lines = Self::generate_line_table(&contents);
		self.contents = contents;
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

	/// Converts a `Span`'s position to an LSP [`Position`] type.
	pub fn position_to_lsp(&self, position: usize) -> Position {
		let mut start = (0, 0);
		for (a, b) in self.lines.iter().zip(self.lines.iter().skip(1)) {
			if a.1 <= position && position < b.1 {
				start = (a.0, position - a.1);
			}
		}

		Position::new(start.0 as u32, start.1 as u32)
	}

	/// Converts an LSP [`Position`] to a `Span`'s position.
	pub fn position_from_lsp(&self, position: Position) -> usize {
		let (_, char_offset) = self.lines.get(position.line as usize).unwrap();

		*char_offset + position.character as usize
	}

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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileConfig {
	pub conditional_compilation_state: ConditionalState,
	pub syntax_highlight_entire_file: bool,
}

/// The state of conditional evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConditionalState {
	Off,
	Evaluate,
	Choice(Vec<usize>),
}

/// Returns the up-to-date file configuration for a given uri. This takes into account fine-grained configuration
/// values on a per-window/per-workspace/per-folder basis.
pub async fn get_file_config(client: &Client, uri: &Url) -> FileConfig {
	use tower_lsp::lsp_types::{
		request, ConfigurationItem, ConfigurationParams,
	};
	// Sends the `workspace/configuration` request.
	let result = client
		.send_request::<request::WorkspaceConfiguration>(ConfigurationParams {
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
	// Even though the vscode client configuration sets a type for each configuration setting, the returned
	// value can be of any type, so we need to deal with incorrect types through a default value.
	let conditional_compilation_state =
		match result.remove(0).as_str().unwrap_or("") {
			"off" => ConditionalState::Off,
			"evaluate" => ConditionalState::Evaluate,
			_ => ConditionalState::Off,
		};
	let syntax_highlight_entire_file =
		result.remove(0).as_bool().unwrap_or(false);

	FileConfig {
		conditional_compilation_state,
		syntax_highlight_entire_file,
	}
}
