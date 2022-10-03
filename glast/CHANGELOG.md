# Changelog

## Draft
### Added
- Support for comments within expressions. Comments can now be arbitrarily inserted anywhere within expressions and the parser will properly handle them and represent them within the CST.

### Fixed
- Lexer incorrectly dealing with a line-continuator if it's the first character in the source string.
- Lexer incorrectly dealing with a preprocessor directive if it follows a block comment on the same line, e.g. `/* comment */ #version 450 core`.

## 0.0.1 - 2022-09-28
### Added
- Initial release, with full token functionality, mostly complete CST functionality, and mostly unfinished AST functionality.