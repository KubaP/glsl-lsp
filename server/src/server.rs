//! The server logic/implementation.

use crate::{
	file::{get_file_config_settings, ConditionalCompilationState, File},
	lsp_extensions::EvalConditionalChoice,
};
use std::collections::HashMap;
use tower_lsp::{
	lsp_types::{
		request::{CodeLensRefresh, SemanticTokensRefresh},
		CodeLens, DidChangeConfigurationParams, InitializeParams,
		SemanticToken, Url,
	},
	Client,
};

/// The server state.
pub struct Server {
	/// Currently open files, (and any files previously opened within this session).
	files: HashMap<Url, File>,

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
		if let Some(file) = self.files.get_mut(&uri) {
			// We have encountered this file before. Check if the version is the same; if so, that means the
			// file was closed and has now been reopened without any edits and hence doesn't need updating.
			if !file.version == version {
				file.update_contents(version, contents);
			}
		} else {
			// We have not encountered this file before.
			let settings = get_file_config_settings(client, &uri).await;
			self.files.insert(
				uri.clone(),
				File::new(uri, version, contents, settings),
			);
		}
	}

	/// Handles the `textDocument/nge` notification.
	pub fn handle_file_change(
		&mut self,
		uri: &Url,
		version: i32,
		contents: String,
	) {
		match self.files.get_mut(uri) {
			Some(file) => file.update_contents(version, contents),
			None => unreachable!("[Server::handle_file_change] Received a file `uri: {uri}` that has not been opened yet"),
		}
	}

	/// Sends the `textDocument/publishDiagnostics` notification.
	pub async fn publish_diagnostics(&self, client: &Client, uri: &Url) {
		if !self.diag_state.enabled {
			return;
		}

		let Some(file) = self.files.get(uri) else {
			unreachable!("[Server::publish_diagnostics] Received a file `uri: {uri}` that has not been opened yet");
		};

		let Some((_, parse_result, _)) = &file.cache else { return; };

		let mut diags = Vec::new();
		crate::diag::convert(
			&parse_result.syntax_diags,
			&parse_result.semantic_diags,
			&mut diags,
			file,
			self.diag_state.supports_related_information,
		);
		for span in &parse_result.disabled_code_regions {
			crate::diag::disable_region(
				*span,
				&file.config.settings.conditional_comp_state,
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
	pub fn provide_semantic_tokens(&self, uri: &Url) -> Vec<SemanticToken> {
		if !self.highlighting_state.enabled {
			return vec![];
		}

		let Some(file) = self.files.get(uri) else {
			unreachable!("[Server::provide_semantic_tokens] Received a file `uri: {uri}` that has not been opened yet");
		};

		let Some((_, parse_result, _)) = &file.cache else { return Vec::new(); };

		crate::semantic::convert(
			&parse_result.syntax_tokens,
			file,
			self.highlighting_state.supports_multiline,
		)
	}

	/// Fulfils the `textDocument/codeLens` request.
	pub fn provide_code_lens(&self, uri: &Url) -> Vec<CodeLens> {
		use tower_lsp::lsp_types::Command;

		if !self.document_state.supports_code_lens {
			return Vec::new();
		}

		let Some(file) = self.files.get(uri) else {
			unreachable!("[Server::provide_code_lens] Received a file `uri: {uri}` that has not been opened yet");
		};

		if !file.config.settings.conditional_comp_code_lenses {
			return Vec::new();
		}

		let Some((token_tree, _, eval_chosen_key)) = &file.cache else { return Vec::new(); };
		let chosen_key = match &file.config.settings.conditional_comp_state {
			ConditionalCompilationState::Off => None,
			ConditionalCompilationState::Evaluate => eval_chosen_key.as_ref(),
			ConditionalCompilationState::Key(k) => Some(k),
		};

		// Lenses for individual directives.
		let mut lenses = token_tree
			.get_all_controlling_conditional_directives()
			.into_iter()
			.enumerate()
			.map(|(i, (_ty, span))| {
				let index = i + 1;

				let on_off = if let Some(chosen_key) = chosen_key {
					if chosen_key.contains(&index) {
						"off"
					} else {
						"on"
					}
				} else {
					"on"
				};

				CodeLens {
					range: file.span_to_lsp(span),
					command: Some(Command {
						title: if on_off == "on" {
							"Include".into()
						} else {
							"Exclude".into()
						},
						command: "glsl.evalConditional".into(),
						arguments: Some(vec![
							uri.to_string().into(),
							serde_json::json!({ on_off: index as u64 }),
						]),
					}),
					data: None,
				}
			})
			.collect::<Vec<_>>();

		// Lenses at the top of the file.
		if !token_tree
			.get_all_controlling_conditional_directives()
			.is_empty()
		{
			let eval = CodeLens {
				range: file.span_to_lsp(glast::Span::new(0, 0)),
				command: Some(Command {
					title: "Evaluate conditional compilation".into(),
					command: "glsl.evalConditional".into(),
					arguments: Some(vec![
						uri.to_string().into(),
						"eval".into(),
					]),
				}),
				data: None,
			};
			let disable = CodeLens {
				range: file.span_to_lsp(glast::Span::new(0, 0)),
				command: Some(Command {
					title: "Disable conditional compilation".into(),
					command: "glsl.evalConditional".into(),
					arguments: Some(vec![uri.to_string().into(), "off".into()]),
				}),
				data: None,
			};
			match &file.config.settings.conditional_comp_state {
				ConditionalCompilationState::Off => lenses.push(eval),
				ConditionalCompilationState::Evaluate => lenses.push(disable),
				ConditionalCompilationState::Key(_) => {
					lenses.push(eval);
					lenses.push(disable);
				}
			}
		}

		lenses
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
		let mut changed_files = Vec::new();
		match str {
			"fileSettings" => {
				for (uri, file) in self.files.iter_mut() {
					let new_settings = get_file_config_settings(client, uri).await;
					if new_settings != file.config.settings {
						changed_files.push(uri.clone());
						file.update_settings(new_settings);
					}
				}
			}
			_ => panic!("[Server::handle_configuration_change] Unexpected settings value: `{str}`")
		}

		for uri in changed_files.iter() {
			// We may have changed the conditional compilation state so we need to update greyed-out areas.
			self.publish_diagnostics(client, &uri).await;
		}
		if !changed_files.is_empty() {
			// We may have changed the conditional compilation state so we need to update syntax highlighting.
			let _ = client.send_request::<SemanticTokensRefresh>(()).await;
			// We may have changed the CodeLens visibility.
			let _ = client.send_request::<CodeLensRefresh>(()).await;
		}
	}
	// endregion: `workspace/*` events.

	// region: custom events.
	/// Fulfils the `glsl/astContent` request.
	pub fn provide_ast(&self, uri: &Url) -> String {
		let Some(file) = self.files.get(uri)else{
			unreachable!("[Server::provide_ast] Received a file `uri: {uri}` that has not been opened yet");	
		};

		let Some((_, parse_result, _)) = &file.cache else { return "<ERROR PARSING FILE>".into(); };
		glast::parser::print_ast(&parse_result.ast)
	}

	/// Handles the `glsl/evalConditional` notification.
	pub async fn handle_conditional_eval(
		&mut self,
		client: &Client,
		uri: &Url,
		choice: EvalConditionalChoice,
	) {
		let Some(file) = self.files.get_mut(uri) else {
			unreachable!("[Server::handle_conditional_eval] Received a file `uri: {uri}` that has not been opened yet");
		};

		// The only CodeLenses that are shown are ones that *will* change which conditional branches get parsed, so
		// we always need to re-parse the file.
		let mut new_settings = file.config.settings.clone();
		match choice {
			EvalConditionalChoice::Off => {
				new_settings.conditional_comp_state =
					ConditionalCompilationState::Off;
			}
			EvalConditionalChoice::Evaluate => {
				new_settings.conditional_comp_state =
					ConditionalCompilationState::Evaluate;
			}
			EvalConditionalChoice::ChoiceOn(branch_idx) => {
				let Some((token_tree, _, eval_chosen_key)) = &file.cache else { return; };
				let new_key = match &file.config.settings.conditional_comp_state
				{
					ConditionalCompilationState::Off => {
						token_tree.create_key(branch_idx as usize)
					}
					ConditionalCompilationState::Evaluate => {
						if let Some(chosen_key) = eval_chosen_key {
							token_tree.add_selection_to_key(
								chosen_key,
								branch_idx as usize,
							)
						} else {
							token_tree.create_key(branch_idx as usize)
						}
					}
					ConditionalCompilationState::Key(existing_key) => {
						token_tree.add_selection_to_key(
							existing_key,
							branch_idx as usize,
						)
					}
				};

				new_settings.conditional_comp_state =
					ConditionalCompilationState::Key(new_key);
			}
			EvalConditionalChoice::ChoiceOff(branch_idx) => {
				let Some((token_tree, _, eval_chosen_key)) = &file.cache else { return; };
				let new_key = match &file.config.settings.conditional_comp_state
				{
					ConditionalCompilationState::Off => return,
					ConditionalCompilationState::Evaluate => {
						if let Some(chosen_key) = eval_chosen_key {
							token_tree.remove_selection_from_key(
								chosen_key,
								branch_idx as usize,
							)
						} else {
							return;
						}
					}
					ConditionalCompilationState::Key(existing_key) => {
						token_tree.remove_selection_from_key(
							existing_key,
							branch_idx as usize,
						)
					}
				};

				new_settings.conditional_comp_state =
					ConditionalCompilationState::Key(new_key);
			}
		}

		let default_settings = get_file_config_settings(client, uri).await;
		if default_settings.conditional_comp_state
			== new_settings.conditional_comp_state
		{
			// We have made a change which has resulted in the new settings matching the default settings for this
			// file. That means we can reset the override.
			file.config.overrides.conditional_comp_state = false;
		}

		file.update_settings(new_settings);

		// We have modified the conditional compilation state, so we need to update greyed-out areas, syntax
		// highlighting, and CodeLenses.
		self.publish_diagnostics(client, uri).await;
		let _ = client.send_request::<SemanticTokensRefresh>(()).await;
		let _ = client.send_request::<CodeLensRefresh>(()).await;
	}
	// endregion: custom events.
}
