mod diag;
mod extensions;
mod state;
mod syntax;

use crate::state::State;
use glast::Span;
use tokio::sync::Mutex;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

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
				semantic_tokens_provider: Some(
					SemanticTokensServerCapabilities::SemanticTokensOptions(
						SemanticTokensOptions {
							work_done_progress_options:
								WorkDoneProgressOptions {
									work_done_progress: None,
								},
							legend: SemanticTokensLegend {
								token_types: syntax::TOKEN_TYPES
									.into_iter()
									.map(|s| SemanticTokenType::new(s))
									.collect::<Vec<_>>(),
								token_modifiers: syntax::TOKEN_MODIFIERS
									.into_iter()
									.map(|s| SemanticTokenModifier::new(s))
									.collect::<Vec<_>>(),
							},
							range: None,
							full: Some(SemanticTokensFullOptions::Bool(true)),
						},
					),
				),
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
		if language_id != "glsl" {
			return;
		}

		let mut state = self.state.lock().await;
		state
			.open_file(&self.client, uri.clone(), version, text)
			.await;
		state.publish_diagnostics(uri, &self.client).await;
	}

	/// This event triggers even if the file is modified outside of vscode, so we don't need to actively watch
	/// files whilst we are running.
	async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'did_change' event.",
			)
			.await;

		let mut state = self.state.lock().await;
		state.change_file(
			params.text_document.uri.clone(),
			params.text_document.version,
			params.content_changes.remove(0).text,
		);
		state
			.publish_diagnostics(params.text_document.uri, &self.client)
			.await;
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

	async fn did_change_configuration(
		&self,
		params: DidChangeConfigurationParams,
	) {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'workspace/didChangeConfiguration' event.",
			)
			.await;

		let mut state = self.state.lock().await;
		state.update_configuration(&self.client, params).await;
	}

	async fn semantic_tokens_full(
		&self,
		params: SemanticTokensParams,
	) -> Result<Option<SemanticTokensResult>> {
		let _ = params;
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'textDocument/semanticTokens/full' event.",
			)
			.await;

		let state = self.state.lock().await;
		let result = state.provide_semantic_tokens(params.text_document.uri);

		Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
			result_id: None,
			data: result,
		})))
	}
}

impl MyServer {
	async fn ast_content(
		&self,
		params: extensions::AstContentParams,
	) -> Result<extensions::AstContentResult> {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'glsl/astContent' event.",
			)
			.await;

		let state = self.state.lock().await;
		Ok(extensions::AstContentResult {
			ast: state.provide_ast(params.text_document_uri),
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
	.custom_method(extensions::AST_CONTENT, MyServer::ast_content)
	.finish();

	Server::new(stdin, stdout, socket).serve(service).await;
}

/// A source file.
#[derive(Debug)]
pub struct File {
	/// The url of this file.
	uri: Url,
	/// The version number of this file.
	version: i32,
	/// Contents of this file.
	contents: String,
	/// A character-index to line conversion table.
	///
	/// - `0` - Line number, (same as vector index).
	/// - `1` - Character index which starts at the line number.
	lines: Vec<(usize, usize)>,
}

impl File {
	/// Constructs a new file with it's contents.
	pub fn new(uri: Url, version: i32, contents: String) -> Self {
		Self {
			uri,
			version,
			lines: Self::generate_line_table(&contents),
			contents,
		}
	}

	/// Updates the files with new content, and performs any necessary recalculations.
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
