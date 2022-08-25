## Protocol Extensions
These are the custom Language Server Protocol extensions used by this client-server.

### SyntaxTreeContent
This is a `Request`-type method. This method is called when:
- the `GLSL: Show Syntax Tree` command is invoked and the current document is a GLSL document,
- the current document or editor is changed to a GLSL document, and there is a visible `tree.glsl.cst` editor.

```
name: glsl/syntaxTreeContent
```

```javascript
SyntaxTreeContentParams {
    /// The `Uri` of the currently active GLSL file.
    textDocumentUri: string,
    /// The version of the currently active GLSL file.
    textDocumentVersion: i32,
    /// An optional `Range` of the GLSL file. If this is `null`,
    /// the CST for the entire file is returned,
    /// otherwise only the relevant snippet.
    range: Range | null,
}
```

The return value:

```javascript
SyntaxTreeContentResult {
    /// The Concrete Syntax Tree text contents,
    /// for the file (or a range of the file).
    cst: string,
    /// The `Range` of the CST Node in the text contents,
    /// of the syntax element that the current cursor position
    /// is over in the GLSL file.
    highlight: Range,
}
```

### SyntaxTreeHighlight
This is a `Request`-type method. This method id called when:
- the current document or editor is a GLSL document and the cursor was moved, and there is a visible `tree.glsl.cst` editor.

```
name: glsl/syntaxTreeHighlight
```

```javascript
SyntaxTreeHighlightParams {
    /// The `Uri` of the currently active GLSL file.
    textDocumentUri: string,
    /// The version of the currently active GLSL file.
    textDocumentVersion: i32,
    /// The position of the cursor in the file.
    cursor: Position,
}
```

The return value:

```javascript
SyntaxTreeHighlightResult {
    /// The `Range` of the CST Node in the text contents,
    /// of the syntax element that the current cursor position
    /// is over in the GLSL file.
    highlight: Range,
}
```