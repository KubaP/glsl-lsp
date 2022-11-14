# glast
*glast* is a crate for parsing and manipulating **gl**sl **a**bstract **s**yntax **t**rees, and a lot more.

The current aims of this crate are to allow for parsing and analysis of the OpenGL Shading Language version 4.50 and 4.60. This includes parsing source strings into ASTs, generating syntax highlighting information, as well as performing analysis such as type-checking.

Unlike other similar crates and libraries, *glast* is designed to be fully specification compliant. That means it correctly handles complex behaviours such as macro expansion and conditional compilation. *glast* is also made for IDEs in mind, meaning it handles syntactical errors gracefully and has excellent error recovery strategies, and also produces information relevant to syntax highlighting.

⚠ This crate is still heavily **work-in-progress**.

## Status
All GLSL 4.50/4.60 features are implemented, apart from:
- Some preprocessor directives are not fully supported.
- The lexer assumes version 4.50 without checking.

## Future Goals
- Start working on the analysis part of the crate, e.g. name resolution.
- Add a visitor API for easy traversal of the AST.
- Support older versions of GLSL, such as 1.10, 3.00 and 3.30 amongst others.

## License
This project is licensed under the **MIT** license - see [LICENSE](LICENSE) for details.
