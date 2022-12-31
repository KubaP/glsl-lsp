mod diag;
mod file;
mod lsp_extensions;
mod semantic;
mod server;

use crate::server::Server;
use tokio::sync::Mutex;
use tower_lsp::{
	jsonrpc::Result, lsp_types::*, Client, LanguageServer, LspService,
};

/* WARNING: Ensure that these match the values in `Cargo.toml` */
const SERVER_NAME: &str = "glsl-lsp";
const SERVER_VERSION: &str = "0.0.1";

/// The language server.
struct Lsp {
	/// Handle for communicating with the language client.
	client: Client,
	/// The actual server state.
	state: Mutex<Server>,
}

#[tower_lsp::async_trait]
impl LanguageServer for Lsp {
	// region: lifecycle events.
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
			server_info: Some(ServerInfo {
				name: SERVER_NAME.into(),
				version: Some(SERVER_VERSION.into()),
			}),
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
				code_lens_provider: Some(CodeLensOptions {
					// This is only necessary if splitting the CodeLens request into two. We send the CodeLens with
					// the command included so there's no need to resolve a CodeLens as a secondary step.
					resolve_provider: Some(false),
				}),
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
								token_types: semantic::TOKEN_TYPES
									.into_iter()
									.map(|s| SemanticTokenType::new(s))
									.collect::<Vec<_>>(),
								token_modifiers: semantic::TOKEN_MODIFIERS
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

	async fn initialized(&self, _: InitializedParams) {
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
	// endregion: lifecycle events.

	// region: `textDocument/*` events.
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
			.handle_file_open(&self.client, uri.clone(), version, text)
			.await;
		state.publish_diagnostics(&self.client, &uri).await;
	}

	async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'did_change' event.",
			)
			.await;

		let mut state = self.state.lock().await;
		state.handle_file_change(
			&params.text_document.uri,
			params.text_document.version,
			params.content_changes.remove(0).text,
		);
		state
			.publish_diagnostics(&self.client, &params.text_document.uri)
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
		let result = state
			.provide_semantic_tokens(&params.text_document.uri)
			.await;

		Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
			result_id: None,
			data: result,
		})))
	}
	// endregion: `textDocument/*` events.

	// region: `workspace/*` events.
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
		state
			.handle_configuration_change(&self.client, params)
			.await;
	}
	// endregion: `workspace/*` events.
}

// Custom events.
impl Lsp {
	/// Handles the `glsl/astContent` request.
	async fn ast_content(
		&self,
		params: lsp_extensions::AstContentParams,
	) -> Result<lsp_extensions::AstContentResult> {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'glsl/astContent' event.",
			)
			.await;

		let state = self.state.lock().await;
		Ok(lsp_extensions::AstContentResult {
			ast: state.provide_ast(&params.text_document_uri),
		})
	}
}

#[tokio::main]
async fn main() {
	let stdin = tokio::io::stdin();
	let stdout = tokio::io::stdout();

	let (service, socket) = LspService::build(|client| Lsp {
		client,
		state: Mutex::new(Server::new()),
	})
	.custom_method(lsp_extensions::AST_CONTENT, Lsp::ast_content)
	.finish();

	tower_lsp::Server::new(stdin, stdout, socket)
		.serve(service)
		.await;
}
