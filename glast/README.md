# glast
*glast* is a crate for parsing and manipulating **gl**sl **a**bstract **s**yntax **t**rees, and a lot more.

⚠ This crate is still heavily **work-in-progress**.

The aims of this crate are to allow for parsing and analysis of the OpenGL Shading Language. This includes parsing source strings into ASTs, generating file formatting and syntax highlighting information, as well as performing analysis such as name resolution and type checking.

Unlike other similar crates and libraries, *glast* is designed to be 100% specification compliant. That means it correctly handles complex behaviours such as macro expansion and conditional compilation, even under some extremely unusual edge-cases.

*glast* is also made for IDEs in mind, meaning it handles syntax errors gracefully and has excellent error recovery strategies to produce "best effort" results. It also produces excellent syntax and semantic diagnostics.

## Current status
#### Lexer
|Feature|Status|
|-|-|
|Parsing of tokens|✔|
|Parsing of directives|✔|
|Handling the line-continuation character|✔|
|Switching GLSL version grammar on-the-fly|✔|
|100% specification compliant behaviour|✔ [1]|

[1]: Minor discrepancy that would almost never be hit. See [Issue#4](https://github.com/KubaP/glsl-lsp/issues/4).

#### Parser
|Feature|Status|
|-|-|
|Parsing of GLSL language constructs|✔|
|Parsing all GLSL versions|⚠ [2]|
|Correct expansion of macros|✔|
|Handling conditional compilation|✔|
|Producing syntax errors and relevant semantic diagnostics|✔|
|Producing syntax highlighting information|✔|
|Producing information for file formatting|❌|
|Visitor API|❌|
|100% specification compliant behaviour|⚠ [3]|

[2]: Only GLSL 450 & 460 are currently supported.

[3]: Certain behaviours not fully compliant.

#### Analyzer
❌ Work not started yet.

## License
This project is licensed under the **MIT** license - see [LICENSE](LICENSE) for details.
