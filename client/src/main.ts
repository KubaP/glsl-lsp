import { spawnSync } from "child_process";
import * as path from "path";
import * as vscode from "vscode";
import { ExtensionContext } from "vscode";
import { ConfigurationRequest } from "vscode-languageclient";

import * as commands from "./commands";
import { Context } from "./context";
import * as lsp from "./lsp";

// Global extension context.
let ctx: Context | undefined;

/* WARNING: Ensure that this matches the value in `package.json` */
export const EXTENSION_VERSION = "0.0.2";
export let serverVersion = "<server not found>";

export async function activate(context: ExtensionContext) {
	// For debugging/development purposes, the environment variable `__GLSL_DEBUG_SERVER_PATH` specifies the path
	// to the server binary. This is appropriately set in the relevant `launch.json` configurations. For release
	// purposes, the build process replaces the `${GLSL_SERVER_PATH}` with a platform-specific binary name.
	const serverPath = process.env.__GLSL_DEBUG_SERVER_PATH ?? context.asAbsolutePath("${GLSL_SERVER_PATH}");

	serverVersion = spawnSync(serverPath, ["--version"], { encoding: "utf-8" })
		.stdout?.slice("glsl-lsp ".length)
		.trim();

	// Create our custom context object.
	ctx = await Context.new(context, serverPath);

	ctx.info(`Extension version: ${EXTENSION_VERSION}`);

	// Register commands.
	ctx.registerCommand("evaluateConditionals", commands.evaluateConditionals);
	ctx.registerCommand("disableConditionals", commands.disableConditionals);
	ctx.registerCommand("showAst", commands.showAst);
	ctx.registerCommand("showVersion", commands.showVersion);

	// Register LSP handlers.
	ctx.client.onRequest(ConfigurationRequest.method, lsp.configurationRequest);
	ctx.subscribe(vscode.workspace.onDidChangeConfiguration((e) => lsp.onDidChangeConfiguration(e, ctx.client)));
	ctx.registerCommand("evalConditional", lsp.evalConditional);

	// Start the client.
	ctx.client.start();
	ctx.info("Starting language client/server");
	ctx.info("Using `glsl-lsp` server binary located at:", serverPath);
	ctx.info(`Server version: ${serverVersion}`);
}

export function deactivate(): Thenable<void> | undefined {
	if (!ctx.client) {
		return undefined;
	}
	return ctx.client.stop();
}
