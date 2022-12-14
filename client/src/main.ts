import * as path from "path";
import * as vscode from "vscode";
import { ExtensionContext } from "vscode";
import { ConfigurationRequest } from "vscode-languageclient";

import * as commands from "./commands";
import { Context } from "./context";
import { configurationRequest, onDidChangeConfiguration } from "./lsp";

// Global context variable.
let ctx: Context | undefined;

export async function activate(context: ExtensionContext) {
	// TODO: Decide on the path for the final distribution.
	// For debugging/development purposes, the environment variable `__GLSL_DEBUG_SERVER_PATH` specifies the path
	// to the server binary. This is appropriately set in the relevant `launch.json` configurations.
	const serverPath = process.env.__GLSL_DEBUG_SERVER_PATH ?? context.asAbsolutePath(path.join("server.exe"));

	// Create our custom context object.
	ctx = await Context.new(context, serverPath);

	// Register commands.
	ctx.registerCommand("showAst", commands.ast);

	// Register LSP handlers.
	ctx.client.onRequest(ConfigurationRequest.method, configurationRequest);
	vscode.workspace.onDidChangeConfiguration((e) => onDidChangeConfiguration(e, ctx.client));

	// Start the client.
	ctx.client.start();
}

export function deactivate(): Thenable<void> | undefined {
	if (!ctx.client) {
		return undefined;
	}
	return ctx.client.stop();
}
