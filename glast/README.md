# glast
*glast* is a crate for parsing and manipulating **gl**sl **a**bstract **s**yntax **t**rees, and a lot more.

The current aims of this crate are to allow for parsing and analysis of the OpenGL Shading Language version 4.50 and 4.60. This includes parsing source strings into ASTs, generating syntax highlighting information, as well as performing analysis such as type-checking.

Unlike other similar crates, *glast* is designed also for IDEs in mind, so it handles syntactical errors gracefully and has excellent recovery strategies.

⚠ This crate is still heavily **work-in-progress**.

## Status
All GLSL 4.50/4.60 features are implemented, apart from:
- Subroutines - Not started yet.
- Function-like macros - Framework implemented but currently only supports object-like macros.
- Some preprocessor directives are unsupported.

## Future Goals
- Add a visitor api for easy traversal of the AST.
- Start working on the analysis-part of the crate, e.g. name resolution.
- Support older versions of GLSL, such as 1.10, 3.00 and 3.30 amongst others.

## License
This project is licensed under the **MIT** license - see [LICENSE](LICENSE) for details.
