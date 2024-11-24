param (
	[string]
	[ValidateSet("x86_64-pc-windows-msvc", "x86_64-unknown-linux-gnu", "x86_64-apple-darwin", "aarch64-apple-darwin")]
	$Target
)

$script:ROOT = Join-Path $PSScriptRoot ".."

# Make any errors stop this build process.
$ErrorActionPreference = "Stop"

# Output the version number which is used in the release action.
$metadata = Get-Content -Path (Join-Path $script:ROOT "server" "Cargo.toml")
$match = [regex]::Matches($metadata, 'version = "(.*?)"')
$version = $match.Groups[1].Value
"::set-output name=VERSION::$version"

Write-Host "Package Version: $version"
Write-Host "Commit SHA: $env:GITHUB_SHA"

# Clean up anything from previous builds.
Write-Host "Cleaning up previous build artifacts"
if (Test-Path (Join-Path $script:ROOT "publish")) {
	Remove-Item -Path (Join-Path $script:ROOT "publish") -Recurse -Force
}

# Copy over the relevant file(s) to `\publish\glsl-lsp-$TARGET-$VERSION` and create an archive at
# `\publish\glsl-lsp-$TARGET-$VERSION.zip`.
New-Item -Path $script:ROOT -Name "publish" -ItemType Directory -Force -Verbose
$script:DEST = New-Item -Path (Join-Path $script:ROOT "publish") -Name "glsl-lsp-$Target-$version" `
	-ItemType Directory -Force -Verbose
switch ($Target) {
	"x86_64-pc-windows-msvc" {
		Copy-Item -Path (Join-Path $script:ROOT "server" "target" $Target "release" "glsl-lsp.exe") `
			-Destination (Join-Path $script:DEST "glsl-lsp.exe") -Verbose
		Copy-Item -Path (Join-Path $script:ROOT "server" "target" $Target "release" "glsl_lsp.pdb") `
			-Destination (Join-Path $script:DEST "glsl_lsp.pdb") -Verbose
	}
	"x86_64-unknown-linux-gnu" {
		Copy-Item -Path (Join-Path $script:ROOT "server" "target" $Target "release" "glsl-lsp") `
			-Destination (Join-Path $script:DEST "glsl-lsp") -Verbose
	}
	"x86_64-apple-darwin" {
		Copy-Item -Path (Join-Path $script:ROOT "server" "target" $Target "release" "glsl-lsp") `
			-Destination (Join-Path $script:DEST "glsl-lsp") -Verbose 
	}
	"aarch64-apple-darwin" {
		Copy-Item -Path (Join-Path $script:ROOT "server" "target" $Target "release" "glsl-lsp") `
			-Destination (Join-Path $script:DEST "glsl-lsp") -Verbose 
	}
}
Compress-Archive -Path (Join-Path $script:ROOT "publish" "glsl-lsp-$Target-$version") `
	-DestinationPath (Join-Path $script:ROOT "publish" "glsl-lsp-$Target-$version.zip") -Verbose