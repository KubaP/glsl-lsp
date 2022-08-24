import { window, workspace, ExtensionContext, Disposable } from "vscode";
import * as vscode from "vscode";
import { Executable, LanguageClient, LanguageClientOptions, ServerOptions } from "vscode-languageclient/node";

import { Cmd } from "./commands";

/**
 * The context/state of the client-side extension.
 */
export class Context {
	private ctx: ExtensionContext;
	client: LanguageClient;

	private constructor(ctx: ExtensionContext, client: LanguageClient) {
		this.ctx = ctx;
		this.client = client;
	}

	static async new(vscode_context: ExtensionContext, serverPath: string): Promise<Context> {
		// Create a output channel for logging information from the client, and for LSP tracing if `glsl.trace.server`
		// is set to `true`.
		const output = window.createOutputChannel("GLSL Client");

		// Define the options for the server process.
		const run: Executable = {
			command: serverPath,
			options: {
				env: {
					...process.env,
				},
			},
		};
		const serverOptions: ServerOptions = {
			run,
			debug: run,
		};

		let clientOptions: LanguageClientOptions = {
			// Register the server for .glsl documents.
			documentSelector: [{ scheme: "file", language: "glsl" }],
			synchronize: {
				// Notify the server about file changes to '.clientrc files contained in the workspace.
				fileEvents: workspace.createFileSystemWatcher("**/.clientrc"),
			},
			traceOutputChannel: output,
			// Note: We don't specify an `outputChannel` for the following reason. Messages from the server are
			// automatically sent to the `outputChannel` no matter what, hence we've called the `outputChannel`
			// `GLSL Language Server`. Meanwhile, messages from the client are instead sent to the
			// `traceOutputChannel` in order to separate them. We could log client messages to the `outputChannel`,
			// but then we wouldn't have a separation of messages and I think that's more important than
			// technicalities. By default the trace logging is disabled anyway, so the `traceOutputChannel` is
			// effectively just for client message logging.
		};

		// Create the language client. This also specifies the name of the output channel for messages from the
		// server. Note: `glsl` must match the name of the extension in order for the trace logging configuration
		// to work.
		const client = new LanguageClient("glsl", "GLSL Language Server", serverOptions, clientOptions);

		const context = new Context(vscode_context, client);
		return context;
	}

	subscribe(d: Disposable) {
		this.ctx.subscriptions.push(d);
	}

	registerCommand(name: string, cmd_factory: (_: Context) => Cmd) {
		const fullName = `glsl.${name}`;
		const command = cmd_factory(this);
		this.subscribe(vscode.commands.registerCommand(fullName, command));
	}
}

/**
 * Returns whether the `document` is a GLSL document.
 */
export function isGLSLDocument(document: vscode.TextDocument): boolean {
	// Note: The reason for checking the scheme is so that we only trigger in a normal text editor window, but
	// not, for example, in the diff viewer.
	return document.languageId === "glsl" && document.uri.scheme === "file";
}

/**
 * Returns wether the `editor` is currently focused on a GLSL document.
 */
export function isGLSLEditor(editor: vscode.TextEditor): boolean {
	return isGLSLDocument(editor.document);
}

/**
 * Returns the active `TextEditor` which has a focused GLSL document, if there is one.
 */
export function getActiveGLSLEditor(): vscode.TextEditor | undefined {
	const editor = vscode.window.activeTextEditor;
	return editor && isGLSLEditor(editor) ? editor : undefined;
}

/**
 * Returns the `TextEditor` which contains the `tree.glsl.cst` file, if there is one.
 */
export function getSyntaxTreeEditor(): vscode.TextEditor | undefined {
	return vscode.window.visibleTextEditors.find((value) => {
		return value.document.languageId === "glsl_syntax_tree";
	});
}
