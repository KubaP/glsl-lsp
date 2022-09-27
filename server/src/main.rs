use crate::state::State;
use glast::Span;
use tokio::sync::Mutex;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

mod diag;
mod extensions;
mod state;

#[derive(Debug)]
struct MyServer {
	client: Client,
	state: Mutex<State>,
}

#[tower_lsp::async_trait]
impl LanguageServer for MyServer {
	async fn initialize(
		&self,
		params: InitializeParams,
	) -> Result<InitializeResult> {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'initialize' request.",
			)
			.await;

		let mut state = self.state.lock().await;
		state.initialize(params);

		Ok(InitializeResult {
			server_info: None,
			capabilities: ServerCapabilities {
				// Sync the full text contents upon any change.
				text_document_sync: Some(TextDocumentSyncCapability::Kind(
					TextDocumentSyncKind::FULL,
				)),
				completion_provider: None,
				hover_provider: None,
				signature_help_provider: None,
				declaration_provider: None,
				definition_provider: None,
				type_definition_provider: None,
				implementation_provider: None,
				references_provider: None,
				document_highlight_provider: None,
				document_symbol_provider: None,
				code_action_provider: None,
				code_lens_provider: None,
				document_link_provider: None,
				color_provider: None,
				document_formatting_provider: None,
				document_range_formatting_provider: None,
				document_on_type_formatting_provider: None,
				rename_provider: None,
				folding_range_provider: None,
				execute_command_provider: None,
				selection_range_provider: None,
				linked_editing_range_provider: None,
				call_hierarchy_provider: None,
				semantic_tokens_provider: None,
				moniker_provider: None,
				workspace_symbol_provider: None,
				workspace: None,
				experimental: None,
			},
		})
	}

	async fn initialized(&self, _params: InitializedParams) {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'initialized' message.",
			)
			.await;
	}

	async fn shutdown(&self) -> Result<()> {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'shutdown' message.",
			)
			.await;
		Ok(())
	}

	async fn did_open(&self, params: DidOpenTextDocumentParams) {
		self.client
			.log_message(MessageType::INFO, "Server received 'did_open' event.")
			.await;

		let TextDocumentItem {
			uri,
			language_id,
			version,
			text,
		} = params.text_document;

		// Ignore non-GLSL files.
		// PERF: This should be impossible because the client defines the language id's to trigger on.
		if language_id != "glsl" {
			return;
		}

		let mut state = self.state.lock().await;
		state.open_file(uri, version, text);
		state.publish_diagnostics(&self.client).await;
	}

	async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'did_change' event.",
			)
			.await;

		let mut state = self.state.lock().await;
		state.change_file(
			params.text_document.uri,
			params.text_document.version,
			params.content_changes.remove(0).text,
		);
		state.publish_diagnostics(&self.client).await;
	}

	async fn did_save(&self, _params: DidSaveTextDocumentParams) {
		self.client
			.log_message(MessageType::INFO, "Server received 'did_save' event.")
			.await;
	}

	async fn did_close(&self, _params: DidCloseTextDocumentParams) {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'did_close' event.",
			)
			.await;
	}
}

impl MyServer {
	async fn syntax_tree_content(
		&self,
		params: extensions::SyntaxTreeContentParams,
	) -> Result<extensions::SyntaxTreeContentResult> {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'glsl/syntaxTreeContent' event.",
			)
			.await;

		let mut state = self.state.lock().await;

		Ok(extensions::SyntaxTreeContentResult {
			cst: state.get_syntax_tree(
				params.text_document_uri,
				params.text_document_version,
			),
			highlight: Range::new(
				Position {
					line: 0,
					character: 0,
				},
				Position {
					line: 0,
					character: 2,
				},
			),
		})
	}

	async fn syntax_tree_highlight(
		&self,
		params: extensions::SyntaxTreeHighlightParams,
	) -> Result<extensions::SyntaxTreeHighlightResult> {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'glsl/syntaxTreeHighlight' event.",
			)
			.await;

		let state = self.state.lock().await;

		Ok(extensions::SyntaxTreeHighlightResult {
			highlight: state.get_syntax_tree_highlight(
				params.text_document_uri,
				params.text_document_version,
				params.cursor,
			),
		})
	}
}

#[tokio::main]
async fn main() {
	let stdin = tokio::io::stdin();
	let stdout = tokio::io::stdout();

	let (service, socket) = LspService::build(|client| MyServer {
		client,
		state: Mutex::new(State::new()),
	})
	.custom_method(
		extensions::SYNTAX_TREE_CONTENT,
		MyServer::syntax_tree_content,
	)
	.custom_method(
		extensions::SYNTAX_TREE_HIGHLIGHT,
		MyServer::syntax_tree_highlight,
	)
	.finish();

	Server::new(stdin, stdout, socket).serve(service).await;
}

/// A source file.
#[derive(Debug)]
pub struct File {
	/// The file url.
	uri: Url,
	/// The version number since the file was first opened in this session; this number increments on every change.
	version: i32,
	/// The file contents.
	contents: String,
	/// A character index-to-line conversion table.
	///
	/// - `0` - line number,
	/// - `1` - character index which starts at the line number.
	lines: Vec<(usize, usize)>,
}

impl File {
	/// Constructs a new `File` with the source string.
	pub fn new(uri: Url, version: i32, contents: String) -> Self {
		Self {
			uri,
			version,
			lines: Self::generate_line_table(&contents),
			contents,
		}
	}

	/// Updates the `File` with new content, and performs any necessary recalculations.
	pub fn update(&mut self, version: i32, contents: String) {
		self.version = version;
		self.lines = Self::generate_line_table(&contents);
		self.contents = contents;
	}

	/// Converts a [`Span`] to an LSP `Range` type.
	pub fn span_to_range(&self, span: Span) -> Range {
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
