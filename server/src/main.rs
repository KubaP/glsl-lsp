mod diag;
mod extensions;
mod file;
mod state;
mod syntax;

use crate::state::State;
use tokio::sync::Mutex;
use tower_lsp::{
	jsonrpc::Result, lsp_types::*, Client, LanguageServer, LspService, Server,
};

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
			.handle_file_open(&self.client, uri.clone(), version, text)
			.await;
		state.publish_diagnostics(&self.client, uri).await;
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
		state.handle_file_change(
			params.text_document.uri.clone(),
			params.text_document.version,
			params.content_changes.remove(0).text,
		);
		state
			.publish_diagnostics(&self.client, params.text_document.uri)
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
		state
			.handle_configuration_change(&self.client, params)
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
			.provide_semantic_tokens(&self.client, params.text_document.uri)
			.await;

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
