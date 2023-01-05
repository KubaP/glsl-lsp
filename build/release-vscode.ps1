param (
	[string]
	[ValidateSet("x86_64-pc-windows-msvc", "x86_64-unknown-linux-gnu", "x86_64-apple-darwin")]
	$Target
)

$script:ROOT = Join-Path $PSScriptRoot ".."

# Make any errors stop this build process.
$ErrorActionPreference = "Stop"

# Output the version number which is used in the release action.
$metadata = Get-Content -Path (Join-Path $script:ROOT "client" "package.json")
$match = [regex]::Matches($metadata, '"version": "(.*?)"')
$ext_version = $match.Groups[1].Value
"::set-output name=EXT_VERSION::$ext_version"

Write-Host "Package Version: $ext_version"
Write-Host "Commit SHA: $env:GITHUB_SHA"

# Clean up anything from previous builds.
Write-Host "Cleaning up previous build artifacts" "Green"
if (Test-Path (Join-Path $script:ROOT "publish")) {
	Remove-Item -Path (Join-Path $script:ROOT "publish") -Recurse -Force
}

# Copy over relevant files to `\publish\kuba-p.glsl-lsp\$EXT_VERSION`.
$script:SRC_DIR = Get-Item -Path (Join-Path $script:ROOT "client")
New-Item -Path $script:ROOT -Name "publish" -ItemType Directory -Force -Verbose
New-Item -Path (Join-Path $script:ROOT "publish") -Name "kuba-p.glsl-lsp" -ItemType Directory -Force -Verbose
$script:OUT_DIR = New-Item -Path (Join-Path $script:ROOT "publish" "kuba-p.glsl-lsp") -Name "$ext_version" `
	-ItemType Directory -Force -Verbose
Get-ChildItem -Path $script:SRC_DIR | Where-Object {
	@(
		"package.json",
		"package-lock.json",
		"tsconfig.json",
		".vscodeignore",
		"src",
		"syntaxes",
		"glsl.language-configuration.json",
		"glsl.ast.language-configuration.json",
		"README.md",
		"LICENSE",
		"CHANGELOG.md"
	) -contains $_.Name
} | ForEach-Object {
	$newPath = Join-Path $script:OUT_DIR $_.FullName.Substring($script:SRC_DIR.FullName.Length)
	Copy-Item -Path $_.FullName -Destination $newPath -Recurse -Verbose
}

# Set the name of the binary in the source code, since it depends on platform.
switch ($Target) {
	"x86_64-pc-windows-msvc" { $serverPath = "glsl-lsp.exe" }
	"x86_64-unknown-linux-gnu" { $serverPath = "glsl-lsp" }
	"x86_64-apple-darwin" { $serverPath = "glsl-lsp" }
}
$script = Get-Content -Path (Join-Path $script:OUT_DIR "src" "main.ts")
$script = $script -replace "\`${GLSL_SERVER_PATH}", $serverPath
Out-File -FilePath (Join-Path $script:OUT_DIR "src" "main.ts") -InputObject $script -Verbose

# Copy over the server binary.
Copy-Item -Path (Join-Path $script:ROOT "server" "target" $Target "release" $serverPath) `
	-Destination (Join-Path $script:OUT_DIR $serverPath ) -Verbose