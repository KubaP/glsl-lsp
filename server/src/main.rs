use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

#[derive(Debug)]
struct MyServer {
	client: Client,
}

#[tower_lsp::async_trait]
impl LanguageServer for MyServer {
	async fn initialize(
		&self,
		_params: InitializeParams,
	) -> Result<InitializeResult> {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'initialize' request.",
			)
			.await;

		Ok(InitializeResult {
			server_info: None,
			capabilities: ServerCapabilities {
				// Sync the full text content on any change.
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
				"Client-Server connection initialized.",
			)
			.await;
	}

	async fn shutdown(&self) -> Result<()> {
		Ok(())
	}

	async fn did_open(&self, params: DidOpenTextDocumentParams) {
		self.client
			.log_message(MessageType::INFO, "Server received 'did_open' event.")
			.await;
		self.client
			.log_message(MessageType::LOG, format!("{params:?}"))
			.await;
		self.on_open(TextDocumentItem {
			uri: params.text_document.uri,
			text: params.text_document.text,
			version: params.text_document.version,
			language_id: "glsl".into(),
		})
		.await;
	}

	async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
		self.client
			.log_message(
				MessageType::INFO,
				"Server received 'did_change' event.",
			)
			.await;
		self.client
			.log_message(MessageType::LOG, format!("{params:?}"))
			.await;
		self.on_change(TextDocumentItem {
			uri: params.text_document.uri,
			text: std::mem::take(&mut params.content_changes[0].text),
			version: params.text_document.version,
			language_id: "glsl".into(),
		})
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
}

impl MyServer {
	async fn on_open(&self, params: TextDocumentItem) {}

	async fn on_change(&self, params: TextDocumentItem) {}
}

#[tokio::main]
async fn main() {
	let stdin = tokio::io::stdin();
	let stdout = tokio::io::stdout();

	let (service, socket) =
		LspService::build(|client| MyServer { client }).finish();

	Server::new(stdin, stdout, socket).serve(service).await;
}
