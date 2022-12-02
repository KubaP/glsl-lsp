use crate::File;
use std::collections::HashMap;
use tower_lsp::{
	lsp_types::{
		InitializeParams, PublishDiagnosticsClientCapabilities, SemanticToken,
		SemanticTokensClientCapabilities, SemanticTokensFullOptions, Url,
	},
	Client,
};

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
pub struct SemanticsState {
	/// Whether the client supports the `textDocument/semanticTokens/full` request, i.e. semantic tokens for the
	/// whole file.
	pub enabled: bool,
	/// Wether the client supports semantic tokens spanning multiple lines.
	pub supports_multiline: bool,
}

#[derive(Debug)]
pub struct State {
	/// The state of diagnostic-related functionality.
	diag_state: DiagState,
	/// The state of semantic highlighting.
	semantic_state: SemanticsState,

	/// Currently open files, (or previously opened within this session).
	files: HashMap<Url, File>,
}

impl State {
	/// Constructs a new server `State`. By default, all functionality is disabled until the client initiates
	/// communication and sends over it's capabilities (to [`initialize()`](Self::initialize())).
	pub fn new() -> Self {
		Self {
			diag_state: Default::default(),
			semantic_state: Default::default(),
			files: HashMap::new(),
		}
	}

	/// Initializes the server `State`, taking into account the reported capabilities from the client.
	pub fn initialize(&mut self, params: InitializeParams) {
		if let Some(cap) = params.capabilities.text_document {
			if let Some(PublishDiagnosticsClientCapabilities {
				// Linking a diagnostic to a different character position.
				related_information,
				// Extra tag information, such as `deprecated`.
				tag_support: _,
				// Document versioning which is bumped on every change.
				version_support,
				// Url to external document explaining the error, e.g. compiler error index.
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
					self.semantic_state.enabled = b;
				} else if let Some(SemanticTokensFullOptions::Delta {
					..
				}) = requests.full
				{
					self.semantic_state.enabled = true;
				}
				if let Some(b) = multiline_token_support {
					self.semantic_state.supports_multiline = b;
				}
			}
		}
	}

	/// Registers the opening of a new file.
	pub fn open_file(&mut self, uri: Url, version: i32, contents: String) {
		if let Some(file) = self.files.get_mut(&uri) {
			// We have encountered this file before. Check if the version is the same; if so, that means the
			// file was closed and has now been reopened without any edits and hence doesn't need updating.
			if !file.version == version {
				file.update(version, contents);
			}
		} else {
			// We have not encountered this file before.
			self.files
				.insert(uri.clone(), File::new(uri, version, contents));
		}
	}

	/// Registers the change to a file.
	pub fn change_file(&mut self, uri: Url, version: i32, contents: String) {
		match self.files.get_mut(&uri) {
			Some(file) => file.update(version, contents),
			None => unreachable!("[State::change_file] Received a file `uri: {uri}` that has not been opened yet"),
		}
	}

	/// Publishes diagnostics for the specified file.
	pub async fn publish_diagnostics(&self, uri: Url, client: &Client) {
		if !self.diag_state.enabled {
			return;
		}

		let Some(file) = self.files.get(&uri) else {
			unreachable!("[State::publish_diagnostics] Received a file `uri: {uri}` that has not been opened yet");
		};

		let (_, syntax, semantic, _) =
			glast::parser::parse_from_str(&file.contents)
				.unwrap()
				.root(false);
		let mut diags = Vec::new();
		crate::diag::convert(
			syntax,
			semantic,
			&mut diags,
			file,
			self.diag_state.supports_related_information,
		);
		client
			.publish_diagnostics(
				file.uri.clone(),
				diags,
				self.diag_state.supports_versioning.then_some(file.version),
			)
			.await;
	}

	/// Fulfils the `textDocument/semanticTokens/full` request.
	pub fn provide_semantic_tokens(&self, uri: Url) -> Vec<SemanticToken> {
		if !self.semantic_state.enabled {
			return vec![];
		}

		let Some(file) = self.files.get(&uri) else {
			unreachable!("[State::provide_semantic_tokens] Received a file `uri: {uri}` that has not been opened yet");
		};

		let (_, _, _, tokens) = glast::parser::parse_from_str(&file.contents)
			.unwrap()
			.root(true);
		crate::syntax::convert(
			tokens,
			file,
			self.semantic_state.supports_multiline,
		)
	}

	/// Fulfils the `glsl/astContent` request.
	pub fn provide_ast(&self, uri: Url) -> String {
		let Some(file) = self.files.get(&uri)else{
			unreachable!("[State::provide_ast] Received a file `uri: {uri}` that has not been opened yet");	
		};

		let (ast, _, _, _) = glast::parser::parse_from_str(&file.contents)
			.unwrap()
			.root(false);
		glast::parser::print_ast(ast)
	}
}
