use crate::{diag, File};
use glsl_parser::error::SyntaxErr;
use tower_lsp::{lsp_types::InitializeParams, Client};

/// The state of support for diagnostic-related functionality, as reported by the client.
#[derive(Debug, Default)]
pub struct Diagnostics {
	/// Whether the client supports diagnostics at all.
	pub enabled: bool,
	/// Whether the client supports showing related information in diagnostics.
	pub related_information: bool,
	/// Whether the client supports versioning file changes.
	pub versioning: bool,
}

#[derive(Debug)]
pub struct State {
	/// The state of diagnostic-related feature support.
	diagnostics: Diagnostics,
}

impl State {
	/// Constructs a new server `State`.
	pub fn new() -> Self {
		Self {
			diagnostics: Default::default(),
		}
	}

	/// Initializes the server state, taking into account the reported capabilities from the client.
	pub fn initialize(&mut self, params: InitializeParams) {
		if let Some(cap) = params.capabilities.text_document {
			if let Some(cap) = cap.publish_diagnostics {
				// Overview of `PublishDiagnosticsClientCapabilities`:
				//
				// - `relatedInformation` - linking a diagnostic to a different character position,
				// - `tagSupport` - extra tag information, such as `deprecated`,
				// - `versionSupport` - document versioning which is bumped on every change,
				// - `codeDescription` - url to external document explaining the error, e.g. compiler error index,
				// - `dataSupport` - extra data payload.
				self.diagnostics.enabled = true;

				self.diagnostics.related_information =
					cap.related_information.unwrap_or(false);
				self.diagnostics.versioning =
					cap.version_support.unwrap_or(false);
			}
		}
	}

	/// Publish diagnostics given the necessary data. This function takes care of selectively enabling features
	/// depending on what the client supports.
	pub async fn publish_diagnostics(
		&self,
		client: &Client,
		file: &File,
		version: i32,
		errors: Vec<SyntaxErr>,
	) {
		if !self.diagnostics.enabled {
			return;
		}

		let mut diags = Vec::new();
		errors.into_iter().for_each(|err| {
			diag::to_diagnostic(err, &file, &mut diags, &self.diagnostics)
		});

		client
			.publish_diagnostics(
				file.uri.clone(),
				diags,
				self.diagnostics.versioning.then_some(version),
			)
			.await;
	}
}
