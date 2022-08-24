import * as vscode from "vscode";
import * as client from "vscode-languageclient";

/**
 * Converts `lsp.Range` to `vscode.Range`.
 */
export function convertLspRangeToVscode(input: client.Range): vscode.Range {
	return new vscode.Range(
		new vscode.Position(input.start.line, input.start.character),
		new vscode.Position(input.end.line, input.end.character)
	);
}

/**
 * Converts `vscode.Range` to `lsp.Range`.
 */
export function convertVscodeRangeToLsp(input: vscode.Range): client.Range {
	return client.Range.create(
		client.Position.create(input.start.line, input.start.character),
		client.Position.create(input.end.line, input.end.character)
	);
}
