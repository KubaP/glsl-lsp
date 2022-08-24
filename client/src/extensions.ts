import * as client from "vscode-languageclient";

// This file contains custom extensions to the Langauge Server Protocol. It is a mirror of
// `server/src/extensions.rs`

export interface SyntaxTreeParams {
	textDocumentUri: client.DocumentUri;
	range: client.Range | null;
}
export const syntaxTree = new client.RequestType<SyntaxTreeParams, string, void>("glsl/syntaxTree");
