use crate::{diag::DisabledReason, File};
use glast::parser::ParseResult;
use std::collections::HashMap;
use tower_lsp::{
	lsp_types::{
		request::SemanticTokensRefresh, DidChangeConfigurationParams,
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

#[derive(Debug, PartialEq, Eq)]
struct FileSettings {
	conditional_compilation_state: ConditionalState,
	syntax_highlight_entire_file: bool,
}

#[derive(Debug, PartialEq, Eq)]
enum ConditionalState {
	Off,
	Evaluate,
	Choice(Vec<usize>),
}

#[derive(Debug)]
pub struct State {
	/// The state of diagnostic-related functionality.
	diag_state: DiagState,
	/// The state of semantic highlighting.
	semantic_state: SemanticsState,

	/// Currently open files, (or previously opened within this session).
	files: HashMap<Url, (File, FileSettings)>,
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
	pub async fn open_file(
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
			let file_settings =
				Self::get_file_settings(client, uri.clone()).await;
			self.files.insert(
				uri.clone(),
				(File::new(uri, version, contents), file_settings),
			);
		}
	}

	/// Registers the change to a file.
	pub fn change_file(&mut self, uri: Url, version: i32, contents: String) {
		match self.files.get_mut(&uri) {
			Some((file, _)) => file.update(version, contents),
			None => unreachable!("[State::change_file] Received a file `uri: {uri}` that has not been opened yet"),
		}
	}

	pub async fn update_configuration(
		&mut self,
		client: &Client,
		params: DidChangeConfigurationParams,
	) {
		let Some(str) = params.settings.as_str() else { return; };
		let mut requires_updating = false;
		match str {
			"fileSettings" => {
				for (uri, (_, settings)) in self.files.iter_mut() {
					let new_settings = Self::get_file_settings(client, uri.clone()).await;
					if new_settings != *settings {
						requires_updating = true;
					}
					*settings = new_settings;
				}
			}
			_ => panic!("[State::update_configuration] Unexpected settings value: `{str}`")
		}

		if requires_updating {
			let _ = client.send_request::<SemanticTokensRefresh>(()).await;
		}
	}

	/// Returns the up-to-date file settings for a given uri. This takes into account fine-grained configuration
	/// values on a per-user/per-workspace/per-folder basis.
	async fn get_file_settings(client: &Client, uri: Url) -> FileSettings {
		// Get the configuration settings that are relevant for the specified file uri.
		use tower_lsp::lsp_types::{
			request, ConfigurationItem, ConfigurationParams,
		};
		let result = client
			.send_request::<request::WorkspaceConfiguration>(
				ConfigurationParams {
					items: vec![
						ConfigurationItem {
							scope_uri: Some(uri.clone()),
							section: Some(
								"glsl.conditionalCompilation.state".into(),
							),
						},
						ConfigurationItem {
							scope_uri: Some(uri),
							section: Some(
								"glsl.syntaxHighlighting.highlightEntireFile"
									.into(),
							),
						},
					],
				},
			)
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

		FileSettings {
			conditional_compilation_state,
			syntax_highlight_entire_file,
		}
	}

	/// Sends the `textDocument/publishDiagnostics` notification.
	pub async fn publish_diagnostics(&self, uri: Url, client: &Client) {
		if !self.diag_state.enabled {
			return;
		}

		let Some((file, file_settings)) = self.files.get(&uri) else {
			unreachable!("[State::publish_diagnostics] Received a file `uri: {uri}` that has not been opened yet");
		};

		let Ok(tree) = glast::parser::parse_from_str(&file.contents) else { return; };
		let ParseResult {
			syntax_diags,
			semantic_diags,
			disabled_code_spans,
			..
		} = match file_settings.conditional_compilation_state {
			ConditionalState::Off => tree.root(false),
			ConditionalState::Evaluate => tree.evaluate(false),
			ConditionalState::Choice(_) => todo!(),
		};
		let mut diags = Vec::new();
		crate::diag::convert(
			syntax_diags,
			semantic_diags,
			&mut diags,
			file,
			self.diag_state.supports_related_information,
		);
		for span in disabled_code_spans {
			crate::diag::disable_code(
				span,
				DisabledReason::ConditionalCompilationDisabled,
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
	pub fn provide_semantic_tokens(&self, uri: Url) -> Vec<SemanticToken> {
		if !self.semantic_state.enabled {
			return vec![];
		}

		let Some((file, file_settings)) = self.files.get(&uri) else {
			unreachable!("[State::provide_semantic_tokens] Received a file `uri: {uri}` that has not been opened yet");
		};

		let ParseResult { syntax_tokens, .. } =
			glast::parser::parse_from_str(&file.contents)
				.unwrap()
				.root(file_settings.syntax_highlight_entire_file);
		crate::syntax::convert(
			syntax_tokens,
			file,
			self.semantic_state.supports_multiline,
		)
	}

	/// Fulfils the `glsl/astContent` request.
	pub fn provide_ast(&self, uri: Url) -> String {
		let Some((file, file_settings)) = self.files.get(&uri)else{
			unreachable!("[State::provide_ast] Received a file `uri: {uri}` that has not been opened yet");	
		};

		let Ok(tree) = glast::parser::parse_from_str(&file.contents) else { return "<ERROR PARSING FILE>".into(); };
		let ParseResult { ast, .. } =
			match file_settings.conditional_compilation_state {
				ConditionalState::Off => tree.root(false),
				ConditionalState::Evaluate => tree.evaluate(false),
				ConditionalState::Choice(_) => todo!(),
			};
		glast::parser::print_ast(ast)
	}
}
