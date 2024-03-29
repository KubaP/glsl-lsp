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
	logChannel: vscode.OutputChannel;

	private constructor(ctx: ExtensionContext, client: LanguageClient, logChannel: vscode.OutputChannel) {
		this.ctx = ctx;
		this.client = client;
		this.logChannel = logChannel;
	}

	/**
	 * Initializes our custom global context.
	 */
	static async new(vscode_context: ExtensionContext, serverPath: string): Promise<Context> {
		// Create a output channel for logging information from the server, and for LSP tracing if
		// `glsl.trace.server` is set to `true`.
		const serverOutput = window.createOutputChannel("GLSL Language Server");
		const traceOutputChannel = window.createOutputChannel("GLSL Language Server Trace");

		// vscode 1.74 adds a log output channel which has built-in formatting of objects and filtering of
		// different log levels. If we ever update to that version we can replace the existing solution.
		const clientOutput = window.createOutputChannel("GLSL Client");

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
			outputChannel: serverOutput,
			traceOutputChannel: traceOutputChannel,
		};

		// Create the language client. This also specifies the name of the output channel for messages from the
		// server. Note: `glsl-lsp` must match the name of the extension in order for the trace logging
		// configuration to work.
		const client = new LanguageClient("glsl-lsp", "GLSL Language Server", serverOptions, clientOptions);

		const ctx = new Context(vscode_context, client, clientOutput);
		ctx.subscribe(serverOutput);
		ctx.subscribe(traceOutputChannel);
		ctx.subscribe(clientOutput);
		return ctx;
	}

	subscribe(d: Disposable) {
		this.ctx.subscriptions.push(d);
	}

	/**
	 * Registers a command.
	 */
	registerCommand(name: string, cmd_factory: (_: Context) => Cmd) {
		const fullName = `glsl-lsp.${name}`;
		const command = cmd_factory(this);
		this.subscribe(vscode.commands.registerCommand(fullName, command));
	}

	/**
	 * Logs an INFO message to the output channel.
	 */
	info(...msg: [unknown, ...unknown[]]) {
		// The type [T, ...T[]] means a non-empty array.
		const message = msg
			.map((val) => {
				if (typeof val === "string") return val;
				return JSON.stringify(val, null, 4);
			})
			.join(" ");
		const time = new Date().toLocaleString();
		this.logChannel.appendLine(`INFO [${time}]: ${message}`);
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
 * Returns the `TextEditor` which contains the `tree.ast.glsl` file, if one is visible is one.
 */
export function getAstEditor(): vscode.TextEditor | undefined {
	return vscode.window.visibleTextEditors.find((value) => {
		return value.document.languageId === "glsl.ast";
	});
}
