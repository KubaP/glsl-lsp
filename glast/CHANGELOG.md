# Changelog

## 0.1.0 - 2023-01-05
This release contains a major refactor of the entire public API and a large improvement in functionality.

The lexer functionality is now finished, and fully supports all features not limited to but including lexing all preprocessor directives, correct handling of line-continuators, and ability to switch grammar on-the-fly when encountering version directives. The API now returns extra metadata about the source string, and errors are handled properly in the return type.

The parser functionality is majorly overhauled, and almost fully finished. All GLSL 450 & 460 language constructs are correctly parsed now. Support for macro expansion has been added, including dealing with weird edge cases. Support for conditional compilation has been added, including handling edge cases and full control over which conditional branches are included.

Syntax diagnostics are now produced for nearly all errors, and some semantic diagnostics have been added for macro-related expansion. Syntax highlighting tokens have also received an overhaul.

### Added
- Support for preprocessor directives, both in the token stream and AST.
- Support for comments. Comments can now be included anywhere within the source string and the parser will correctly handle them.
- Support for all GLSL 450 & 460 language constructs, and correct error handling of currently unsupported GLSL versions.
- A lot more syntax diagnostics to cover more specific cases, as well as some semantic diagnostics.
- Macro expansion within the parser. The parser now correctly expands arbitrarily-complex macros.
- Conditional compilation support within the parser. The parser now correctly handles conditional compilation, with complete freedom to include/exclude conditional branches. This involves a new API around the `TokenTree` struct, as well as some new concepts.
- Functionality to produce syntax highlighting tokens for the parsed AST.
- Functionality to pretty-print the AST.
- *Internal*: More unit tests.

### Changed
- Reorganized and overhauled the crate into a different structure. Lots of functions/types/modules have been renamed and moved around for better clarity.

### Fixed
- Lexer incorrectly dealing with a line-continuator if it's the first character in the source string.
- Lexer incorrectly treating an invalid line-continuator as valid.
- Lexer incorrectly dealing with a preprocessor directive if it follows a block comment on the same line, e.g. `/* comment */ #version 450 core`.
- Many bugs in the expression parser which resulted in panics or incorrect results.
- Many bugs in the parser which resulted in panics or infinite-loops.

### Removed
- Unnecessary debug logging functionality.
- The distinction between the CST and AST. This approach was incompatible with macro expansion and conditional compilation; now there is just an AST production phase in the parser, along with auxiliary syntax highlighting data.

## 0.0.1 - 2022-09-28
### Added
- Initial release, with full token functionality, mostly complete CST functionality, and mostly unfinished AST functionality.