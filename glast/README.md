# glast
*glast* is a crate for parsing and manipulating **gl**sl **a**bstract **s**yntax **t**rees, and a lot more.

The current aims of this project are to allow for parsing and analysis of the OpenGL Shading Language version 4.50 and 4.60. This includes parsing source strings into abstract or concrete syntax trees, as well as performing analysis such as type-checking.

⚠ This crate is still heavily **work-in-progress**. ⚠

## Status
- `token` - All functionality is pretty much finished, though a slight re-work of directive parsing is due.
- `cst` - Support for dealing correctly with comments is work-in-progress. Support for preprocessor directives hasn't started yet. Aside from these two things the rest of the functionality is finished.
- `ast` - No real work started yet.

## Plan of Work
- Fully implement support for comments in the parser.
- Implement support for preprocessor directives.
- Start working on the AST functionality, such as name resolution.

## Future Goals
- Support older versions of GLSL, such as 1.10, 3.00 and 3.30 amongst others.

## License
This project is licensed under the **MIT** license - see [LICENSE](LICENSE) for details.
