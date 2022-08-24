import { window, workspace } from "vscode";
import * as vscode from "vscode";
import * as client from "vscode-languageclient";

import { getActiveGLSLEditor, Context, isGLSLDocument, isGLSLEditor, getSyntaxTreeEditor } from "./context";
import * as extensions from "./extensions";
import { convertLspRangeToVscode } from "./util";

export type Cmd = (...args: any[]) => unknown;

// Note that these functions are command "factories". I.e. they can perform arbitrary set-up logic which may
// require the global context, and then they return the actual function which runs upon the command invocation.

export function syntaxTree(context: Context): Cmd {
	class SyntaxTreeProvider implements vscode.TextDocumentContentProvider {
		static scheme = "glsl-syntax-tree";
		static uri = vscode.Uri.parse(`${SyntaxTreeProvider.scheme}://syntaxtree/tree.glsl.cst`);

		readonly eventEmitter = new vscode.EventEmitter<vscode.Uri>();

		static outlineDecoration = window.createTextEditorDecorationType({
			isWholeLine: false,
			rangeBehavior: vscode.DecorationRangeBehavior.ClosedClosed,
			light: {
				border: "2px solid #000000",
			},
			dark: {
				border: "2px solid #FFFFFF",
			},
		});

		constructor() {
			// These are here because they are relevant to the functionality of the feature, and if this feature is
			// disposed, we want to dispose of these handlers too.
			context.subscribe(workspace.onDidChangeTextDocument(this.onDidChangeTextDocument, this));
			context.subscribe(window.onDidChangeActiveTextEditor(this.onDidChangeActiveTextEditor, this));
			context.subscribe(window.onDidChangeTextEditorSelection(this.onDidChangeTextEditorSelection, this));
		}

		get onDidChange(): vscode.Event<vscode.Uri> {
			return this.eventEmitter.event;
		}

		/// This function is ran for any `TextDocument` under the `glsl-syntax-tree` scheme.
		async provideTextDocumentContent(uri: vscode.Uri, token: vscode.CancellationToken): Promise<string> {
			// Get the active GLSL editor if there is one.
			const activeEditor = getActiveGLSLEditor();
			if (!activeEditor) return "";

			// If range-based queries are enabled, we pass the range of the selection in the currently active GLSL
			// editor to the server.
			const range =
				uri.query === "range=true" && !activeEditor.selection.isEmpty
					? context.client.code2ProtocolConverter.asRange(activeEditor.selection)
					: null;

			// Send the request to the server. Normally we would pass the `uri` of the current file, but since we
			// are currently within the `tree.glsl.cst` "special" file, we instead want to pass the uri of the
			// currently active GLSL file.
			const params = { textDocumentUri: activeEditor.document.uri.toString(), range };
			const { cst, highlight } = await context.client.sendRequest(
				extensions.syntaxTreeContent,
				params,
				token
			);

			// Add the decoration for the node outline.
			getSyntaxTreeEditor()?.setDecorations(SyntaxTreeProvider.outlineDecoration, [
				convertLspRangeToVscode(highlight),
			]);

			return cst;
		}

		// The following are grouped here because they are relevant, but they are not strictly part of the
		// `TextDocumentContentProvider` itself.

		/// Whenever the active document is changed, we want to update the contents of the `tree.glsl.cst` file if
		/// the new document is a GLSL file.
		private onDidChangeTextDocument(event: vscode.TextDocumentChangeEvent) {
			if (!getSyntaxTreeEditor()) {
				return;
			}
			if (isGLSLDocument(event.document)) {
				this.eventEmitter.fire(SyntaxTreeProvider.uri);
			}
		}

		/// Whenever the active editor is changed, we want to update the contents of the `tree.glsl.cst` file if
		/// the document in the new editor is a GLSL file.
		private onDidChangeActiveTextEditor(editor: vscode.TextEditor | undefined) {
			if (!getSyntaxTreeEditor()) {
				return;
			}
			if (editor && isGLSLEditor(editor)) {
				this.eventEmitter.fire(SyntaxTreeProvider.uri);
			}
		}

		/// Whenever the cursor is moved, we want to update the highlight within the `tree.glsl.cst` file to the
		/// relevant CST node if the current document is a GLSL file.
		private async onDidChangeTextEditorSelection(event: vscode.TextEditorSelectionChangeEvent) {
			const editor = event.textEditor;
			if (!isGLSLEditor(editor)) {
				return;
			}

			const syntaxEditor = getSyntaxTreeEditor();
			if (!syntaxEditor) {
				return;
			}

			// Send the request to the server.
			const cursor = client.Position.create(
				event.selections[0].start.line,
				event.selections[0].start.character
			);
			const params = { textDocumentUri: editor.document.uri.toString(), cursor };
			const { highlight } = await context.client.sendRequest(extensions.syntaxTreeHighlight, params);

			// Add the decoration for the node outline, and scroll the editor to keep the node in view.
			syntaxEditor.setDecorations(SyntaxTreeProvider.outlineDecoration, [
				convertLspRangeToVscode(highlight),
			]);
			syntaxEditor.revealRange(
				convertLspRangeToVscode(highlight),
				vscode.TextEditorRevealType.InCenterIfOutsideViewport
			);
		}
	}

	// Create the provider.
	const provider = new SyntaxTreeProvider();
	context.subscribe(workspace.registerTextDocumentContentProvider(SyntaxTreeProvider.scheme, provider));

	// The command logic.
	return async () => {
		// Construct the uri for the `tree.glsl.cst` file. We optionally enable range support if we have something
		// selected in the current file.
		const activeEditor = window.activeTextEditor;
		const rangeEnabled = !!activeEditor && !activeEditor.selection.isEmpty;
		const uri = rangeEnabled
			? vscode.Uri.parse(`${SyntaxTreeProvider.uri.toString()}?range=true`)
			: SyntaxTreeProvider.uri;

		// Open the `tree.glsl.cst` file, in a new editor.
		const document = await workspace.openTextDocument(uri);
		await window.showTextDocument(document, {
			viewColumn: vscode.ViewColumn.Two,
			preserveFocus: true,
		});

		// Once the editor is open, fire the event to get new document contents.
		provider.eventEmitter.fire(uri);
	};
}
