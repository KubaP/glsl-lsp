use crate::{diag, File};
use glsl_parser::cst::Cst;
use std::collections::HashMap;
use tower_lsp::{
	lsp_types::{InitializeParams, Position, Range, Url},
	Client,
};

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

	/// CSTs of requested files.
	/// MAYBE: Clear entries after a timeout?
	syntax_trees: HashMap<Url, (i32, Cst)>,
}

impl State {
	/// Constructs a new server `State`. By default, all functionality is disabled until the client initiates
	/// communication and sends over it's capabilities (to [`initialize()`](Self::initialize)).
	pub fn new() -> Self {
		Self {
			diagnostics: Default::default(),
			files: HashMap::new(),
			syntax_trees: HashMap::new(),
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

	/// Publishes diagnostics for the workspace. This function takes care of selectively enabling features
	/// depending on what the client supports.
	///
	/// *Note:* There is no workspace support yet. This currently publishes diagnostics for open or
	/// previously-opened files.
	pub async fn publish_diagnostics(&self, client: &Client) {
		if !self.diagnostics.enabled {
			return;
		}

		// Parse each file and convert any syntax errors into diagnostics and push them.
		//
		// Note: We don't cache any diagnostics to reuse them if the file doesn't change. Whilst this makes sense
		// right now, in the future when the cross-file analysis eventually gets implemented, any primitive caching
		// will be useless.
		for (_, file) in &self.files {
			let (_cst, errors) = glsl_parser::parser::parse(&file.contents);

			let mut diagnostics = Vec::new();
			errors.into_iter().for_each(|err| {
				diag::to_diagnostic(
					err,
					&file,
					&mut diagnostics,
					&self.diagnostics,
				)
			});

			client
				.publish_diagnostics(
					file.uri.clone(),
					diagnostics,
					self.diagnostics.versioning.then_some(file.version),
				)
				.await;
		}
	}

	/// Returns a formatted CST for the specified file.
	pub fn get_syntax_tree(&mut self, uri: Url, version: i32) -> String {
		let file = self.files.get(&uri).expect(
			&format!("[State::get_syntax_tree] Received a file `uri: {uri}` which has not been opened yet.")
		);

		// Parse the file and print the CST into a tree.
		let (cst, _) = glsl_parser::parser::parse(&file.contents);
		let string = "".to_owned();

		// If this file's CST was already cached then update it, otherwise insert a new entry.
		self.syntax_trees.insert(uri, (version, cst));

		string
	}

	/// Returns a `Range` of the CST node within the formatted string, which corresponds to the CST node that the
	/// cursor is over in the specified file.
	pub fn get_syntax_tree_highlight(
		&self,
		_uri: Url,
		_version: i32,
		_cursor: Position,
	) -> Range {
		// TODO: Implement

		Range::new(
			Position {
				line: 0,
				character: 0,
			},
			Position {
				line: 0,
				character: 4,
			},
		)
	}
}
