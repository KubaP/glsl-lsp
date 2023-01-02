param (
	[string]
	$WorkingDirectory,

	[string]
	[ValidateSet("x86_64-pc-windows-msvc", "x86_64-unknown-linux-gnu", "x86_64-apple-darwin")]
	$Target
)

# Import helper functions.
. "$PSScriptRoot\helpers.ps1"

# Make any errors stop this build process.
$ErrorActionPreference = "Stop"

Write-Header "Copying over server binary" "Blue"
switch ($Target) {
	"x86_64-pc-windows-msvc" { $serverPath = "glsl-lsp.exe" }
	"x86_64-unknown-linux-gnu" { $serverPath = "glsl-lsp" }
	"x86_64-apple-darwin" { $serverPath = "glsl-lsp" }
}
Copy-Item -Path "$WorkingDirectory\server\target\$TARGET\release\$serverPath" `
	-Destination "$WorkingDirectory\publish\$serverPath" -Verbose
