//! The server logic/implementation.

use crate::file::{
	get_file_config, ConditionalCompilationState, File, FileConfig,
};
use glast::parser::ParseResult;
use std::collections::HashMap;
use tower_lsp::{
	lsp_types::{
		request::SemanticTokensRefresh, DidChangeConfigurationParams,
		InitializeParams, SemanticToken, Url,
	},
	Client,
};

/// The server state.
#[derive(Debug)]
pub struct Server {
	/// Currently open files, (and any files previously opened within this session).
	files: HashMap<Url, (File, FileConfig)>,

	/// The state of diagnostic-related functionality.
	diag_state: DiagState,
	/// The state of semantic highlighting.
	highlighting_state: SemanticHighlightState,
	/// The state of document-related functionality.
	document_state: DocumentState,
}

/// The state of support for diagnostic-related functionality, as reported by the client.
#[derive(Debug, Default)]
pub struct DiagState {
	/// Whether the client supports diagnostics at all.
	pub enabled: bool,
	/// Whether the client supports showing related information in diagnostics.
	pub supports_related_information: bool,
	/// Whether the client supports versioning file changes.
	pub supports_versioning: bool,
}

/// The state of support for semantic highlighting, as reported by the client.
#[derive(Debug, Default)]
pub struct SemanticHighlightState {
	/// Whether the client supports the `textDocument/semanticTokens/full` request, i.e. semantic tokens for the
	/// whole file.
	pub enabled: bool,
	/// Wether the client supports semantic tokens spanning multiple lines.
	pub supports_multiline: bool,
}

/// The state of support for document-related functionality, as reported by the client.
#[derive(Debug, Default)]
pub struct DocumentState {
	/// Whether the client supports CodeLens.
	pub supports_code_lens: bool,
}

impl Server {
	/// Constructs a new server state. By default, all functionality is disabled until the client initiates
	/// communication and sends over its capabilities to [`initialize()`](Self::initialize()).
	pub fn new() -> Self {
		Self {
			files: HashMap::new(),
			diag_state: Default::default(),
			highlighting_state: Default::default(),
			document_state: Default::default(),
		}
	}

	/// Initializes the server state, taking into account the reported capabilities from the client.
	pub fn initialize(&mut self, params: InitializeParams) {
		use tower_lsp::lsp_types::{
			CodeLensClientCapabilities, PublishDiagnosticsClientCapabilities,
			SemanticTokensClientCapabilities, SemanticTokensFullOptions,
		};

		if let Some(cap) = params.capabilities.text_document {
			if let Some(PublishDiagnosticsClientCapabilities {
				// Linking a diagnostic to a different character position.
				related_information,
				// Extra tag information, such as `deprecated`.
				tag_support: _,
				// Document versioning which is bumped on every change.
				version_support,
				// Link to external document explaining the error, e.g. compiler error index.
				code_description_support: _,
				// Extra data payload.
				data_support: _,
			}) = cap.publish_diagnostics
			{
				self.diag_state.enabled = true;
				self.diag_state.supports_related_information =
					related_information.unwrap_or(false);
				self.diag_state.supports_versioning =
					version_support.unwrap_or(false);
			}

			if let Some(SemanticTokensClientCapabilities {
				dynamic_registration: _,
				// Which request types the client supports (might send out).
				requests,
				// The token types the client natively supports.
				token_types: _,
				/// The token modifiers the client natively supports.
					token_modifiers: _,
				// Guaranteed to be `vec!["relative"]`
				formats: _,
				// Whether the client supports overlapping tokens.
				overlapping_token_support: _,
				// Whether the client supports tokens spanning multiple lines.
				multiline_token_support,
			}) = cap.semantic_tokens
			{
				if let Some(SemanticTokensFullOptions::Bool(b)) = requests.full
				{
					self.highlighting_state.enabled = b;
				} else if let Some(SemanticTokensFullOptions::Delta {
					..
				}) = requests.full
				{
					self.highlighting_state.enabled = true;
				}
				if let Some(b) = multiline_token_support {
					self.highlighting_state.supports_multiline = b;
				}
			}

			if let Some(CodeLensClientCapabilities {
				dynamic_registration: _,
			}) = cap.code_lens
			{
				self.document_state.supports_code_lens = true;
			}
		}
	}

	// region: `textDocument/*` events.
	/// Handles the `textDocument/didOpen` notification.
	pub async fn handle_file_open(
		&mut self,
		client: &Client,
		uri: Url,
		version: i32,
		contents: String,
	) {
		if let Some((file, _)) = self.files.get_mut(&uri) {
			// We have encountered this file before. Check if the version is the same; if so, that means the
			// file was closed and has now been reopened without any edits and hence doesn't need updating.
			if !file.version == version {
				file.update(version, contents);
			}
		} else {
			// We have not encountered this file before.
			let file_config = get_file_config(client, &uri).await;
			self.files.insert(
				uri.clone(),
				(File::new(uri, version, contents), file_config),
			);
		}
	}

	/// Handles the `textDocument/didChange` notification.
	pub fn handle_file_change(
		&mut self,
		uri: Url,
		version: i32,
		contents: String,
	) {
		match self.files.get_mut(&uri) {
			Some((file, _)) => file.update(version, contents),
			None => unreachable!("[Server::handle_file_change] Received a file `uri: {uri}` that has not been opened yet"),
		}
	}

	/// Sends the `textDocument/publishDiagnostics` notification.
	pub async fn publish_diagnostics(&self, client: &Client, uri: Url) {
		if !self.diag_state.enabled {
			return;
		}

		let Some((file, file_config)) = self.files.get(&uri) else {
			unreachable!("[Server::publish_diagnostics] Received a file `uri: {uri}` that has not been opened yet");
		};

		let Ok(tree) = glast::parser::parse_from_str(&file.contents) else { return; };
		let ParseResult {
			syntax_diags,
			semantic_diags,
			disabled_code_regions,
			..
		} = match &file_config.conditional_compilation_state {
			ConditionalCompilationState::Off => {
				tree.root(file_config.syntax_highlight_entire_file)
			}
			ConditionalCompilationState::Evaluate => {
				tree.evaluate(file_config.syntax_highlight_entire_file)
			}
			ConditionalCompilationState::Key(key) => {
				match tree.parse_by_order_of_appearance(
					key,
					file_config.syntax_highlight_entire_file,
				) {
					Ok(p) => p,
					Err(_) => return,
				}
			}
		};
		let mut diags = Vec::new();
		crate::diag::convert(
			syntax_diags,
			semantic_diags,
			&mut diags,
			file,
			self.diag_state.supports_related_information,
		);
		for span in disabled_code_regions {
			crate::diag::disable_region(
				span,
				&file_config.conditional_compilation_state,
				&mut diags,
				file,
			);
		}
		client
			.publish_diagnostics(
				file.uri.clone(),
				diags,
				self.diag_state.supports_versioning.then_some(file.version),
			)
			.await;
	}

	/// Fulfils the `textDocument/semanticTokens/full` request.
	pub async fn provide_semantic_tokens(
		&self,
		client: &Client,
		uri: Url,
	) -> Vec<SemanticToken> {
		if !self.highlighting_state.enabled {
			return vec![];
		}

		let Some((file, file_config)) = self.files.get(&uri) else {
			unreachable!("[Server::provide_semantic_tokens] Received a file `uri: {uri}` that has not been opened yet");
		};

		let Ok(tree) = glast::parser::parse_from_str(&file.contents) else { return vec![]; };
		let ParseResult { syntax_tokens, .. } =
			match &file_config.conditional_compilation_state {
				ConditionalCompilationState::Off => {
					tree.root(file_config.syntax_highlight_entire_file)
				}
				ConditionalCompilationState::Evaluate => {
					tree.evaluate(file_config.syntax_highlight_entire_file)
				}
				ConditionalCompilationState::Key(key) => {
					match tree.parse_by_order_of_appearance(
						key,
						file_config.syntax_highlight_entire_file,
					) {
						Ok(p) => p,
						Err(_) => return vec![],
					}
				}
			};
		self.publish_diagnostics(client, uri).await;
		crate::semantic::convert(
			syntax_tokens,
			file,
			self.highlighting_state.supports_multiline,
		)
	}
	// endregion: `textDocument/*` events.

	// region: `workspace/*` events.
	/// Handles the `workspace/didChangeConfiguration` notification.
	pub async fn handle_configuration_change(
		&mut self,
		client: &Client,
		params: DidChangeConfigurationParams,
	) {
		let Some(str) = params.settings.as_str() else { return; };
		let mut requires_updating = false;
		match str {
			"fileSettings" => {
				for (uri, (_, file_config)) in self.files.iter_mut() {
					let new_settings = get_file_config(client, uri).await;
					if new_settings != *file_config {
						requires_updating = true;
					}
					*file_config = new_settings;
				}
			}
			_ => panic!("[Server::handle_configuration_change] Unexpected settings value: `{str}`")
		}

		if requires_updating {
			let _ = client.send_request::<SemanticTokensRefresh>(()).await;
		}
	}
	// endregion: `workspace/*` events.

	// region: custom events.
	/// Fulfils the `glsl/astContent` request.
	pub fn provide_ast(&self, uri: Url) -> String {
		let Some((file, file_config)) = self.files.get(&uri)else{
			unreachable!("[Server::provide_ast] Received a file `uri: {uri}` that has not been opened yet");	
		};

		let Ok(tree) = glast::parser::parse_from_str(&file.contents) else { return "<ERROR PARSING FILE>".into(); };
		let ParseResult { ast, .. } =
			match &file_config.conditional_compilation_state {
				ConditionalCompilationState::Off => tree.root(false),
				ConditionalCompilationState::Evaluate => tree.evaluate(false),
				ConditionalCompilationState::Key(key) => {
					match tree.parse_by_order_of_appearance(key, false) {
						Ok(p) => p,
						Err(_) => return "<ERROR PARSING FILE>".into(),
					}
				}
			};
		glast::parser::print_ast(ast)
	}
	// endregion: custom events.
}