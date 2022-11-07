# glsl-lsp
This repository contains a heavily **work-in-progress** project aiming to provide a language extension for the OpenGL Shading Language.

This is targetting versions `450`/`460` initially, but there are plans to support older versions in the future, such as `330 es`.

⚠ Current state of functionality: Working on a big refactor of the parser library; lsp is broken.

## Structure
| Folder               | Contents                                                          |
| -------------------- | ----------------------------------------------------------------- |
| [`/glast`](/glast)   | A library for parsing GLSL, specifically created for this project |
| [`/client`](/client) | The VS Code language client extension                             |
| [`/server`](/server) | The Language Server Protocol Implementation                       |