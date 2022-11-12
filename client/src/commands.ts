import * as vscode from "vscode";

export type Cmd = (...args: any[]) => unknown;

// Note that these functions are command "factories". I.e. they can perform arbitrary set-up logic which may
// require the global context, and then they return the actual function which runs upon the command invocation.
