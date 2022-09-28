# glsl-lsp
This repository contains a heavily **work-in-progress** project aiming to provide a language extension for the OpenGL Shading Language.

Currently targetting versions `450`/`460` initially, but there are plans to support older versions in the future, such as `330 es`.

⚠ Current state of functionality: Most syntax errors are reported, but the parser doesn't properly support all valid notations.

## Structure
| Folder               | Contents                                                          |
| -------------------- | ----------------------------------------------------------------- |
| [`/glast`](/glast)   | A library for parsing GLSL, specifically created for this project |
| [`/client`](/client) | The VS Code language client extension                             |
| [`/server`](/server) | The server implementing the Langauge Server Protocol              |