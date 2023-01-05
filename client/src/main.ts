import * as path from "path";
import * as vscode from "vscode";
import { ExtensionContext } from "vscode";
import { ConfigurationRequest } from "vscode-languageclient";

import * as commands from "./commands";
import { Context } from "./context";
import * as lsp from "./lsp";

// Global context variable.
let ctx: Context | undefined;

export async function activate(context: ExtensionContext) {
	// For debugging/development purposes, the environment variable `__GLSL_DEBUG_SERVER_PATH` specifies the path
	// to the server binary. This is appropriately set in the relevant `launch.json` configurations. For release
	// purposes, the build process replaces the `${GLSL_SERVER_PATH}` with a platform-specific binary name.
	const serverPath =
		process.env.__GLSL_DEBUG_SERVER_PATH ?? context.asAbsolutePath(path.join("..", "${GLSL_SERVER_PATH}"));

	// Create our custom context object.
	ctx = await Context.new(context, serverPath);

	// Register commands.
	ctx.registerCommand("showAst", commands.showAst);
	ctx.registerCommand("evaluateConditionals", commands.evaluateConditionals);
	ctx.registerCommand("disableConditionals", commands.disableConditionals);

	// Register LSP handlers.
	ctx.client.onRequest(ConfigurationRequest.method, lsp.configurationRequest);
	ctx.subscribe(vscode.workspace.onDidChangeConfiguration((e) => lsp.onDidChangeConfiguration(e, ctx.client)));
	ctx.registerCommand("evalConditional", lsp.evalConditional);

	// Start the client.
	ctx.client.start();
}

export function deactivate(): Thenable<void> | undefined {
	if (!ctx.client) {
		return undefined;
	}
	return ctx.client.stop();
}
