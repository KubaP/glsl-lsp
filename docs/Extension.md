# Extension
This document outlines some information about the client-server extension as a whole and the Language Server Protocol implementation. Whilst a number of protocol events are standardized in their meaning and purpose, some events allow for custom messages, and there are even entire protocol extensions in use. This document should give enough information to implement a client from scratch that will work correctly with the server.

## Configuration
For a canonical list of all settings in the extension configuration, see the `contributes.configuration` section of [/client/package.json](../client/package.json). Each entry (setting) includes a key, the type (and optionally valid values), and a comprehensive description. Pay attention to the `scope` property; a scope of `"resource"` means that the configuration can apply on a per-directory/per-file basis.

### `workspace/configuration`
The `workspace/configuration` request from the server to the client is handled in the following manner:
- Each `ConfigurationItem` has a `section` that matches one of the setting keys, and an optional `scopeUri` which gets resolved as accurately as possible, (for example, in vscode, a folder may have a `settings.json` file which overrides any globally-set settings).
- The value of that key is returned. Note that whilst a key has a specified type, any type may be returned and the server will handle it gracefully.

### `workspace/didChangeConfiguration`
The `workspace/didChangeConfiguration` notification from the client to the server has the following behaviour:

#### Per-file configuration
Any modification to: 
- `glsl.conditionalCompilation.state`
- `glsl.conditionalCompilation.codeLens`
- `glsl.syntaxHighlighting.highlightEntireFile`

at any uri scope will return:
```typescript
{
    settings: "fileSettings"
}
```
This signifies that the server should send `workspace/configuration` requests to update the relevant per-directory/per-file settings for each file.

The reason why the new setting value(s) are not sent directly is because, at least in vscode, the on-configuration-change event only provides the key but not the new value nor the uri scope, so we need the server to request the updated values on a per-file basis.

## Protocol Extensions
This extension uses custom protocol extensions for extra functionality. Some of these are quite important for the full functionality of the extension, but others are *"nice to have"* features. All of these extensions are implemented in the Visual Studio Code client; if you are unsure what purpose a certain extension has, or what payloads are sent from the client to the server, use that as a reference.

### AstContent
This is a *Request*-type method from the client to the server. This method is called when:
- The `GLSL: Show AST` command is invoked and the current document is a GLSL document.
- The currently document or editor is changed to a GLSL document, and there is a `tree.ast.glsl` editor visible.
```
name: glsl/astContent
```

The request sent to the server:
```typescript
interface AstContentParams {
    /// The `Uri` of the currently active GLSL document.
    textDocumentUri: Uri;
    /// The version of the currently active GLSL document.
    textDocumentVersion: i32;
}
```

The result returned by the server:
```typescript
interface AstContentResult {
    /// The pretty-printed AST contents for the document.
    ast: string;
}
```

### EvalConditional
This is a *Notification*-type method from the client to the server. This method is called when:
- A conditional compilation-related CodeLens is triggered.
- A conditional compilation-related command is executed.
```
name: glsl/evalConditional
```

The notification sent to the server:
```typescript
export interface EvalConditionalParams {
    /// The `Uri` of the GLSL document in which the CodeLens was triggered.
    textDocumentUri: Uri;
    /// The evaluation choice.
    ///
    /// - `"off"` - Disable conditional compilation.
    /// - `"eval"` - Evaluate conditional compilation.
    /// - `{ "on"|"off": u64 }` - Enable conditional compilation with a key.
    ///   This value is a chronological index of the controlling conditional directive to include (`on`) or 
    ///   exclude (`off`).
    choice: "off" | "eval" | { "on": u64 } | { "off": u64 };
}
```
