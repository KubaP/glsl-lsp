# Changelog

## 0.0.2 - 2023-01-06
### Fixed
- Language server not starting because of incorrect path.

## 0.0.1 - 2023-01-05
### Added
- **GLSL**: Support for parsing all GLSL 450 & 460 language constructs.
- **GLSL**: Some semantic highlighting support; currently identifiers are not resolved to more concrete types.
- **GLSL**: Reporting of syntax error.
- **GLSL**: Reporting of some semantic diagnostics, (mainly limited to macro expansion).
- **GLSL**: Fading-out of regions of code if they are excluded from conditional compilation.
- **GLSL**: Ability to display CodeLens above conditional compilation directives, for easy control over the evaluation of conditional compilation.
- Basic GLSL grammar and language configuration; features such as auto-closing brackets, commenting-out shortcuts, word patterns, etc.
- `glsl-lsp.syntaxHighlighting.highlightEntireFile` setting to control syntax highlighting behaviour.
- `glsl-lsp.conditionalCompilation.state` setting to control the default state of conditional compilation.
- `glsl-lsp.conditionalCompilation.codeLens` setting to control the visibility of conditional compilation-related CodeLens.
- `glsl-lsp.evaluateConditionals`/`glsl-lsp.disableConditionals` commands to control the state of conditional compilation for the current file.
- `glsl-lsp.showAst` command to show a pretty-printed AST of the current file. This command is mainly for debugging the extension itself.
- `glsl-lsp.showVersion` command to show a pop-up with relevant information for reporting issues/bugs.
- The following custom semantic token types:
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
- The following custom semantic token modifiers:
    - `macroSignature` - Tokens within the macro signature, e.g. the `BAR(A, B)` within `#define BAR(A, B) foo`.
    - `macroBody` - Tokens within the macro body, e.g. the `foo + bar` within `#define FOO foo + bar`.
    - `undefine` - Tokens within the `#undef` directive; not applied to the `#undef` part.
    - `conditional` - Tokens within a conditional directive; not applied to the `#if`/`#elif`/etc. part.