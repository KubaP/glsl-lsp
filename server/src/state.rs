use std::collections::HashMap;
use tower_lsp::lsp_types::{InitializeParams, Url};

use crate::File;

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

	/// Currently open files, (or previously opened within this session).
	files: HashMap<Url, File>,
}

impl State {
	/// Constructs a new server `State`. By default, all functionality is disabled until the client initiates
	/// communication and sends over it's capabilities (to [`initialize()`](Self::initialize)).
	pub fn new() -> Self {
		Self {
			diagnostics: Default::default(),
			files: HashMap::new(),
		}
	}

	/// Initializes the server `State`, taking into account the reported capabilities from the client.
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

	/// Registers the opening of a new file.
	pub fn open_file(&mut self, uri: Url, version: i32, contents: String) {
		match self.files.get_mut(&uri) {
			Some(file) => {
				// We have encountered this file before. Check if the version is the same; if so, that means the
				// file was closed and has now been reopened without any edits and hence doesn't need updating.
				if !file.version == version {
					file.update(version, contents);
				}
			}
			None => {
				// We have not encountered this file before.
				self.files
					.insert(uri.clone(), File::new(uri, version, contents));
			}
		}
	}

	/// Registers the change to a file.
	pub fn change_file(&mut self, uri: Url, version: i32, contents: String) {
		match self.files.get_mut(&uri) {
			Some(file) => file.update(version, contents),
			None => unreachable!("[State::change_file] Received a file `uri: {uri}` which has not been opened yet."),
		}
	}
}
