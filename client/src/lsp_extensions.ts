import * as client from "vscode-languageclient";

/* This file contains custom LSP extensions. It is a mirror of `/server/src/lsp_extensions.rs` */

export interface AstContentParams {
	textDocumentUri: client.DocumentUri;
	textDocumentVersion: number;
}
export interface AstContentResult {
	ast: string;
}
export const astContent = new client.RequestType<AstContentParams, AstContentResult, void>("glsl/astContent");

export interface EvalConditionalParams {
	textDocumentUri: client.DocumentUri;
	choice: "off" | "eval" | { on: number } | { off: number };
}
export const evalConditional = new client.NotificationType<EvalConditionalParams>("glsl/evalConditional");
