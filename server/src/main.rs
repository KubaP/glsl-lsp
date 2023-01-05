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
const SERVER_VERSION: &str = "0.0.2";

/// The language server.
struct Lsp {
	/// Handle for communicating with the language client.
	client: Client,
	/// The actual server state.
	state: Mutex<Server>,
}

/// Logs an INFO message.
macro_rules! info {
	($self:expr, $msg:expr) => {
		$self
			.client
			.log_message(tower_lsp::lsp_types::MessageType::INFO, $msg)
			.await;
	};
}

#[tower_lsp::async_trait]
impl LanguageServer for Lsp {
	// region: lifecycle events.
	async fn initialize(
		&self,
		params: InitializeParams,
	) -> Result<InitializeResult> {
		info!(self, format!("Server version: {SERVER_VERSION}"));
		info!(self, "Received `initialize` request");

		let mut state = self.state.lock().await;
		state.initialize(params);

		Ok(InitializeResult {
			server_info: Some(ServerInfo {
				name: SERVER_NAME.into(),
				version: Some(SERVER_VERSION.into()),
			}),
			capabilities: ServerCapabilities {
				position_encoding: Some(match state.span_encoding {
					glast::SpanEncoding::Utf8 => PositionEncodingKind::UTF8,
					glast::SpanEncoding::Utf16 => PositionEncodingKind::UTF16,
					glast::SpanEncoding::Utf32 => PositionEncodingKind::UTF32,
				}),
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
					// This is only necessary if splitting the code lens request into two. We send the code lens
					// with the commands included so there's no need to resolve a code lens as a secondary step.
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
				inlay_hint_provider: None,
				workspace_symbol_provider: None,
				workspace: None,
				experimental: None,
			},
			// Legacy unofficial position encoding communication.
			offset_encoding: None,
		})
	}

	async fn initialized(&self, _: InitializedParams) {
		info!(self, "Received `initialized` notification");
	}

	async fn shutdown(&self) -> Result<()> {
		info!(self, "Received `shutdown` request");
		Ok(())
	}
	// endregion: lifecycle events.

	// region: `textDocument/*` events.
	async fn did_open(&self, params: DidOpenTextDocumentParams) {
		info!(self, "Received `textDocument/didOpen` notification");

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
		info!(self, "Received `textDocument/didChange` notification");

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
		info!(self, "Received `textDocument/didSave` notification");
	}

	async fn did_close(&self, _params: DidCloseTextDocumentParams) {
		info!(self, "Received `textDocument/didClose` notification");
	}

	async fn semantic_tokens_full(
		&self,
		params: SemanticTokensParams,
	) -> Result<Option<SemanticTokensResult>> {
		info!(self, "Received `textDocument/semanticTokens/full` request");

		let state = self.state.lock().await;
		let result = state.provide_semantic_tokens(&params.text_document.uri);

		Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
			result_id: None,
			data: result,
		})))
	}

	async fn code_lens(
		&self,
		params: CodeLensParams,
	) -> Result<Option<Vec<CodeLens>>> {
		info!(self, "Received `textDocument/codelens` request");

		let state = self.state.lock().await;
		let lenses = state.provide_code_lens(&params.text_document.uri);

		if lenses.is_empty() {
			Ok(None)
		} else {
			Ok(Some(lenses))
		}
	}
	// endregion: `textDocument/*` events.

	// region: `workspace/*` events.
	async fn did_change_configuration(
		&self,
		params: DidChangeConfigurationParams,
	) {
		info!(
			self,
			"Received `workspace/didChangeConfiguration` notification"
		);

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
		info!(self, "Received `glsl/astContent` request");

		let state = self.state.lock().await;
		Ok(lsp_extensions::AstContentResult {
			ast: state.provide_ast(&params.text_document_uri),
		})
	}

	/// Handles the `glsl/evalConditional` notification.
	async fn eval_conditional(
		&self,
		params: lsp_extensions::EvalConditionalParams,
	) {
		info!(self, "Received `glsl/evalConditional` notification");

		let mut state = self.state.lock().await;
		state
			.handle_conditional_eval(
				&self.client,
				&params.text_document_uri,
				params.choice,
			)
			.await;
	}
}

#[tokio::main]
async fn main() {
	// The binary accepts a `--version` flag which just prints the current version to stdout and exits. This is
	// useful for the language client to query the version of the server without hardcoding it in.
	let _ = clap::Command::new(SERVER_NAME)
		.version(SERVER_VERSION)
		.get_matches();

	let stdin = tokio::io::stdin();
	let stdout = tokio::io::stdout();

	let (service, socket) = LspService::build(|client| Lsp {
		client,
		state: Mutex::new(Server::new()),
	})
	.custom_method(lsp_extensions::AST_CONTENT, Lsp::ast_content)
	.custom_method(lsp_extensions::EVAL_CONDITIONAL, Lsp::eval_conditional)
	.finish();

	tower_lsp::Server::new(stdin, stdout, socket)
		.serve(service)
		.await;
}
