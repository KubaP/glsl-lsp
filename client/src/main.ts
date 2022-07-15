import * as path from "path";
import {
	languages,
	workspace,
	EventEmitter,
	ExtensionContext,
	window,
	commands,
	ViewColumn,
	WebviewPanel,
	WorkspaceEdit,
	Selection,
	Uri,
	InlayHintsProvider,
	TextDocument,
	CancellationToken,
	Range,
	InlayHint,
	TextDocumentChangeEvent,
	Position,
	InlayHintLabelPart,
	Location,
	ProviderResult,
} from "vscode";
import {
	Disposable,
	Executable,
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	TransportKind,
} from "vscode-languageclient/node";

let client: LanguageClient;

export async function activate(context: ExtensionContext) {
	// Create a output channel for logging information from the client.
	const outputChannel = window.createOutputChannel("GLSL Client");

	// TODO: Decide on the path for the final distribution.
	// For debugging/development purposes, the environment variable `__GLSL_DEBUG_SERVER_PATH` specifies the path
	// to the server binary. This is appropriately set in the relevant `launch.json` configurations.
	const command = process.env.__GLSL_DEBUG_SERVER_PATH ?? context.asAbsolutePath(path.join("server.exe"));

	// Define the options for the server process.
	const run: Executable = {
		command,
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
		traceOutputChannel: outputChannel,
	};

	// Create the language client and start it. This also specifies the name of the output channel for messages
	// from the server.
	client = new LanguageClient("glsl-language-client", "GLSL Language Server", serverOptions, clientOptions);
	client.start();
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
