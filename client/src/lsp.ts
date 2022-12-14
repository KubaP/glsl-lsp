import { ConfigurationParams, LSPAny, DidChangeConfigurationNotification } from "vscode-languageclient";
import { Executable, LanguageClient, LanguageClientOptions, ServerOptions } from "vscode-languageclient/node";
import { CancellationToken, Uri, ConfigurationChangeEvent, workspace } from "vscode";

/**
 * Fulfils the `workspace/configuration` request.
 */
export function configurationRequest(params: ConfigurationParams, _token: CancellationToken): LSPAny[] {
	let values = [];
	for (const { scopeUri, section } of params.items) {
		const val = workspace.getConfiguration(section, scopeUri ? Uri.parse(scopeUri) : null);
		values.push(val);
	}
	return values;
}

/**
 * Sends the `workspace/didConfigurationChange` notification.
 */
export async function onDidChangeConfiguration(e: ConfigurationChangeEvent, client: LanguageClient) {
	// Ignore configuration changes that aren't relevant to our extension.
	if (!e.affectsConfiguration("glsl")) {
		return;
	}

	// These configuration settings are applied on a per-file basis. We send this notification which in turn
	// prompts the server to update the per-file settings for each opened file. The reason we don't send the
	// updated values is because the values can be configured on a per-file basis, so which value would we send? It
	// must be the server who requests the updated setting because it can do it for each file and it knows the uri
	// of each file.
	if (
		e.affectsConfiguration("glsl.syntaxHighlighting.highlightEntireFile") ||
		e.affectsConfiguration("glsl.conditionalCompilation.state")
	) {
		await client.sendNotification(DidChangeConfigurationNotification.method, {
			settings: "fileSettings",
		});
	}
}
