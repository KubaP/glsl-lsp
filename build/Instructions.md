# Build Instructions
## Development
For development purposes, launch configurations for Visual Studio Code are provided in the `\.vscode\launch.json` file:
- `Extension` - Launches the Visual Studio Code extension development host.
- `Attach Server` - Attaches a debugger to a running server.
- `Extension release` - Launches the Visual Studio Code extension development host, but using a release build of the server.
- `Lib tests` - For debugging glast crate tests.

## Release
To build the Visual Studio Code extension locally, navigate to the root of the repo and run the following steps. All noted shell commands are in Powershell.

Prerequisites:
- `npm` 8.0.0+
- `node` 10.0.0+
- `pwsh` 7.0.0+

|`$TARGET`|`$EXEC`|`$VSCE_TARGET`|
|-|-|-|
|`x86_64-pc-windows-msvc`|`glsl-lsp.exe`|`win32-x64`|
|`x86_64-unknown-linux-gnu`|`glsl-lsp`|`linux-x64`|
|`x86_64-apple-darwin`|`glsl-lsp`|`darwin-x64`|

`$VERSION` is the current version of the extension found in the client [package manifest](/client/package.json).

### 1. Build server
```powershell
cd .\server
cargo build --release --target=$TARGET
```
This will create a binary at `\server\target\$TARGET\release\$EXEC`.

### 2. Build client & package
```powershell
cd ..
.\build\release-vscode-1.ps1 -Target $TARGET

cd .\publish\kuba-p.glsl\$VERSION
npm install
npm run build
npm run buildGrammar

vsce package --target $VSCE_TARGET
```
This will create the extension file at `\publish\kuba-p.glsl\$VERSION\glsl-$VSCE_TARGET-$VERSION.vsix`.
