# glsl-lsp
This repository contains a heavily **work-in-progress** project aiming to provide a language extension for the OpenGL Shading Language.

This is targetting versions `450`/`460` initially, but there are plans to support older versions in the future, including but not limited to `110`, `300 es`, `330` and `410`.

⚠ **Current state of functionality**: Basic syntax highlighting and syntactical error reporting. Currently not packaged so you have to build from source.

## Structure
| Folder               | Contents                                                          |
| -------------------- | ----------------------------------------------------------------- |
| [`/glast`](/glast)   | A library for parsing GLSL, specifically created for this project |
| [`/client`](/client) | The VS Code language client extension                             |
| [`/server`](/server) | The Language Server Protocol implementation                       |

## License
See each individual project for it's license.
