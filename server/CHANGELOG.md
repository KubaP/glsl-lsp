# Changelog

## 0.0.2 - 2023-01-05
### Fixed
- Use of incorrect prefix in workspace configuration requests, which resulted in broken behaviour.

## 0.0.1 - 2023-01-05
### Added
- Handling of the basic text document open/change/save/close notifications. Currently only full syncing is supported.
- Handling of the `textDocument/semanticToken/full` request.
- Publishing of diagnostics whenever a file is (re)parsed, including support for fading-out regions of code that are disabled because of conditional compilation.
- Handling of the `textDocument/codeLens` request, to produce CodeLens for conditional compilation control that are displayed above individual directives as well as at the top of the file, (if conditional directives are present).
- Handling of the `workspace/didChangeConfiguration` notification, to refresh any per-file configurations when they change, and update semantic tokens, diagnostics, or CodeLens if the file needs to be re-parsed.
- The custom `glsl/astContent` event that allows the client to request a pretty-printed string of the AST of a file.
- The custom `glsl/evalConditional` event that is necessary for the conditional compilation CodeLens to work.
- Support for negotiating position encodings, including support for `utf-8`, `utf-16`, and `utf-32`.
- The production of the following semantic token types:
    - `punctuation` - A punctuation symbol.
    - `boolean` - A boolean.
    - `builtInType` - A primitive type.
    - `subroutine` - A subroutine.
    - `layoutQualifier` - A valid layout qualifier identifier.
    - `ident` - An identifier which has not gone through name resolution and never will. This token is only used for any identifiers within macro bodies.
    - `unresolvedReference` - An unresolved identifier. This could be an unresolved variable identifier, an unresolved type name, or an illegal layout qualifier identifier.
    - `invalid` - An invalid character.
    - `lineContinuator` - A line-continuator character (`\`).
    - `escapeSequence` - An escape sequence character.
    - `objectMacro` - An object-like macro identifier. This is used at the macro definition, and at any call sites.
    - `functionMacro` - A function-like macro identifier. This is used at the macro definition, and at any call sites.
    - `directive` - A general bit of text in a directive.
    - `directiveConcat` - The macro concatenation operator (`##`).
    - `directiveHash` - The hash `#` symbol in a directive.
    - `directiveName` - The name of the directive, e.g. `version` or `ifdef`.
    - `directiveVersion` - The GLSL version in a `#version` directive.
    - `directiveProfile` - The GLSL profile in a `#version` directive.
    - `directiveExtName` - The extension name in a `#extension` directive.
    - `directiveExtBehaviour` - The extension behaviour in a `#extension` directive.
    - `directiveLineNumber` - The line number in a `#line` directive.
    - `directiveError` - The message in an `#error` directive.
    - `directivePragma` - The compiler option in a `#pragma` directive.
- The production of the following semantic token modifiers:
    - `macroSignature` - Tokens within the macro signature, e.g. the `BAR(A, B)` within `#define BAR(A, B) foo`.
    - `macroBody` - Tokens within the macro body, e.g. the `foo + bar` within `#define FOO foo + bar`.
    - `undefine` - Tokens within the `#undef` directive; not applied to the `#undef` part.
    - `conditional` - Tokens within a conditional directive; not applied to the `#if`/`#elif`/etc. part.