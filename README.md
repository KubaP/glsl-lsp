# glsl-lsp
This repository contains a heavily **work-in-progress** project aiming to provide a language extension for the OpenGL Shading Language.

This project is targeting GLSL `450` & `460` initially, but there are plans to support older versions in the future, including but not limited to `110`, `300 es`, `330` and `410`.

**An extension for Visual Studio Code is available on the [marketplace](https://marketplace.visualstudio.com/items?itemName=kuba-p.glsl-lsp).**

⚠ Current state of functionality: Basic semantic highlighting and syntax diagnostics reporting. Advanced support for macro expansion and conditional compilation.

## Structure
|Folder|Contents|
|-|-|
|[`/glast`](/glast)|A library for parsing GLSL, specifically created for this project|
|[`/client`](/client)|The client extension for Visual Studio Code|
|[`/server`](/server)|The Language Server Protocol implementation|
|[`/docs`](/docs)|Project documentation|
|[`/build`](/build)|Build & release scripts|

## Build Instructions
For instructions on how to build the project for debugging or release purposes, see [/build/Instructions.md](/build/Instructions.md).

## Contribution
Contributions are always welcome, be it code, tests, documentation or bug reports, feature requests, etc. <!-- Please see the [contribution guide]() for more details.--> For help, please file an [issue](https://github.com/KubaP/glsl-lsp/issues).

## License
See each individual project for its license.
