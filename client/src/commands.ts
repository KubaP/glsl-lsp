import * as vscode from "vscode";
import { window, workspace } from "vscode";

import { getActiveGLSLEditor, Context, isGLSLDocument, isGLSLEditor, getAstEditor } from "./context";
import * as lsp_extensions from "./lsp_extensions";

export type Cmd = (...args: any[]) => unknown;

// Note that these functions are command "factories"; i.e. they can perform arbitrary set-up logic which may
// require the global context, and then they return the actual function which runs upon the command invocation.

export function showAst(ctx: Context): Cmd {
	class AstProvider implements vscode.TextDocumentContentProvider {
		static scheme = "glsl-ast";
		static uri = vscode.Uri.parse(`${AstProvider.scheme}://ast/tree.ast.glsl`);

		readonly eventEmitter = new vscode.EventEmitter<vscode.Uri>();

		constructor() {
			// These are here because they are relevant to the functionality of the feature, and if this feature is
			// disposed, we want to dispose of these handlers too.
			ctx.subscribe(workspace.onDidChangeTextDocument(this.onDidChangeTextDocument, this));
			ctx.subscribe(window.onDidChangeActiveTextEditor(this.onDidChangeActiveTextEditor, this));
		}

		get onDidChange(): vscode.Event<vscode.Uri> {
			return this.eventEmitter.event;
		}

		/// This function is ran for any `TextDocument` under the `glsl-ast` scheme.
		async provideTextDocumentContent(_uri: vscode.Uri, token: vscode.CancellationToken): Promise<string> {
			// Get the active GLSL editor if there is one.
			const activeEditor = getActiveGLSLEditor();
			if (!activeEditor) return "";

			// Send the request to the server. Normally we would pass the `uri` of the current file, but since we
			// are currently within the `tree.ast.glsl` "special" file, we instead want to pass the uri of the
			// currently active GLSL file.
			const params = {
				textDocumentUri: activeEditor.document.uri.toString(),
				textDocumentVersion: activeEditor.document.version,
			};
			const { ast } = await ctx.client.sendRequest(lsp_extensions.astContent, params, token);

			return ast;
		}

		// The following are grouped here because they are relevant, but they are not strictly part of the
		// `TextDocumentContentProvider` itself.

		/// Whenever the active document is changed, we want to update the contents of the `tree.ast.glsl` file if
		/// the new document is a GLSL file.
		private onDidChangeTextDocument(event: vscode.TextDocumentChangeEvent) {
			if (!getAstEditor()) {
				return;
			}
			if (isGLSLDocument(event.document)) {
				this.eventEmitter.fire(AstProvider.uri);
			}
		}

		/// Whenever the active editor is changed, we want to update the contents of the `tree.ast.glsl` file if
		/// the document in the new editor is a GLSL file.
		private onDidChangeActiveTextEditor(editor: vscode.TextEditor | undefined) {
			if (!getAstEditor()) {
				return;
			}
			if (editor && isGLSLEditor(editor)) {
				this.eventEmitter.fire(AstProvider.uri);
			}
		}
	}

	// Create the provider.
	const provider = new AstProvider();
	ctx.subscribe(workspace.registerTextDocumentContentProvider(AstProvider.scheme, provider));

	// The command logic.
	return async () => {
		// Construct the uri for the `tree.ast.glsl` file. We optionally enable range support if we have something
		// selected in the current file.
		const uri = AstProvider.uri;

		// Open the `tree.ast.glsl` file, in a new editor to the right-hand side.
		const document = await workspace.openTextDocument(uri);
		await window.showTextDocument(document, {
			viewColumn: vscode.ViewColumn.Two,
			preserveFocus: true,
		});

		// Once the editor is open, fire the event to get new document contents.
		provider.eventEmitter.fire(uri);
	};
}

export function evaluateConditionals(ctx: Context): Cmd {
	// The command logic.
	return async () => {
		const activeEditor = getActiveGLSLEditor();
		if (!activeEditor) {
			return;
		}
		await vscode.commands.executeCommand("glsl.evalConditional", activeEditor.document.uri.toString(), "eval");
	};
}

export function disableConditionals(ctx: Context): Cmd {
	// The command logic.
	return async () => {
		const activeEditor = getActiveGLSLEditor();
		if (!activeEditor) {
			return;
		}
		await vscode.commands.executeCommand("glsl.evalConditional", activeEditor.document.uri.toString(), "off");
	};
}
