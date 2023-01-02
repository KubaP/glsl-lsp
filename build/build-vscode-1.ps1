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

# Output the version number which is used in the release action.
$metadata = Get-Content -Path "$WorkingDirectory\client\package.json"
$match = [regex]::Matches($metadata, '"version": "(.*?)"')

$version = $match.Groups[1].Value
"::set-output name=EXT_VERSION::$version"

# Clean up anything from previous builds.
Write-Header "Cleaning up previous build artifacts" "Green"
if (Test-Path "$WorkingDirectory\publish") {
	Remove-Item -Path "$WorkingDirectory\publish" -Recurse -Force
}

$script:CLIENT_SRC_DIR = Get-Item -Path "$WorkingDirectory\client" -Verbose
$script:PUBLISH_DIR = New-Item -Path "$WorkingDirectory\" -Name "publish" -ItemType Directory -Force -Verbose

# First, copy the contents of the client project into the output folder.
# Filter out folders and files which shouldn't be part of the final package.
Write-Header "Copying over files" "Blue"
Get-ChildItem -Path $script:CLIENT_SRC_DIR | Where-Object {
	@(
		"node_modules",
		"out"
	) -notcontains $_.Name
} | ForEach-Object {
	$newPath = Join-Path $script:PUBLISH_DIR $_.FullName.Substring($script:CLIENT_SRC_DIR.FullName.Length)
	Copy-Item -Path $_.FullName -Destination $newPath -Recurse -Verbose
}

# Second, we need to set the path of the server executable. The name of the binary depends on the platform.
Write-Header "Fixing platform-specific path" "Blue"
switch ($Target) {
	"x86_64-pc-windows-msvc" { $serverPath = "glsl-lsp.exe" }
	"x86_64-unknown-linux-gnu" { $serverPath = "glsl-lsp" }
	"x86_64-apple-darwin" { $serverPath = "glsl-lsp" }
}
$script = Get-Content -Path "$WorkingDirectory\publish\src\main.ts"
$script = $script -replace "\`${GLSL_SERVER_PATH}", $serverPath
Out-File -FilePath "$WorkingDirectory\publish\src\main.ts" -InputObject $script -Verbose