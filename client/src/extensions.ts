import * as client from "vscode-languageclient";

// This file contains custom extensions to the Langauge Server Protocol. It is a mirror of
// `server/src/extensions.rs`

export interface SyntaxTreeContentParams {
	textDocumentUri: client.DocumentUri;
	range: client.Range | null;
}
export interface SyntaxTreeContentResult {
	cst: string;
	highlight: client.Range;
}
export const syntaxTreeContent = new client.RequestType<SyntaxTreeContentParams, SyntaxTreeContentResult, void>(
	"glsl/syntaxTreeContent"
);

export interface SyntaxTreeHighlightParams {
	textDocumentUri: client.DocumentUri;
	cursor: client.Position;
}
export interface SyntaxTreeHighlightResult {
	highlight: client.Range;
}
export const syntaxTreeHighlight = new client.RequestType<
	SyntaxTreeHighlightParams,
	SyntaxTreeHighlightResult,
	void
>("glsl/syntaxTreeHighlight");
