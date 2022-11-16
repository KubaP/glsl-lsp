import * as client from "vscode-languageclient";

/* This file contains custom LSP extensions. It is a mirror of `/server/src/extensions.rs` */

export interface AstContentParams {
	textDocumentUri: client.DocumentUri;
	textDocumentVersion: number;
}
export interface AstContentResult {
	ast: string;
}
export const astContent = new client.RequestType<AstContentParams, AstContentResult, void>("glsl/astContent");
