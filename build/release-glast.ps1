$script:ROOT = Join-Path $PSScriptRoot ".."

# Make any errors stop this build process.
$ErrorActionPreference = "Stop"

# Output the version number which is used in the release action.
$metadata = Get-Content -Path (Join-Path $script:ROOT "glast" "Cargo.toml")
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

# Copy over source files to `\publish\glast\$VERSION` and create an archive at `\publish\glast-$VERSION.zip`.
$script:SRC_DIR = Get-Item -Path (Join-Path $script:ROOT "glast")
New-Item -Path $script:ROOT -Name "publish" -ItemType Directory -Force -Verbose
New-Item -Path (Join-Path $script:ROOT "publish") -Name "glast" -ItemType Directory -Force -Verbose
$script:OUT_DIR = New-Item -Path (Join-Path $script:ROOT "publish" "glast") -Name "$version" `
    -ItemType Directory -Force -Verbose
Get-ChildItem -Path $script:SRC_DIR | Where-Object {
    @(
        "Cargo.toml",
        "src",
        "tests",
        "README.md",
        "LICENSE",
        "CHANGELOG.md"
    ) -contains $_.Name
} | ForEach-Object {
    $newPath = Join-Path $script:OUT_DIR $_.FullName.Substring($script:SRC_DIR.FullName.Length)
    Copy-Item -Path $_.FullName -Destination $newPath -Recurse -Verbose
}

# Zip up the content.
Compress-Archive -Path (Join-Path $script:ROOT "publish" "glast") `
    -DestinationPath (Join-Path $script:ROOT "publish" "glast-$version.zip") -Verbose
