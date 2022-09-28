param (
    [String]
    $Version
)

Write-Host "Version: $Version"
Write-Host "Commit SHA: $env:GITHUB_SHA"

# Tag the commit.
#git tag "glast/v$Version" "$env:GITHUB_SHA"
#git push origin "glast/v$Version"

# Prepare the release artefact.

$script:SRC_DIR = Get-Item -Path "$PSScriptRoot/../glast"
New-Item -Path "$PSScriptRoot/../" -Name "out" -ItemType Directory -Force -Verbose
New-Item -Path "$PSScriptRoot/../out/" -Name "glast" -ItemType Directory -Force -Verbose
New-Item -Path "$PSScriptRoot/../out/glast/" -Name "$Version" -ItemType Directory -Force -Verbose
$script:OUT_DIR = Get-Item -Path "$PSScriptRoot/../out"

# Copy the contents of the `glast` project into an output directory.
# Filter out folders and files which shouldn't be part of the final output.
Get-ChildItem -Path $script:SRC_DIR | Where-Object {
    @(
        "Cargo.lock",
        "target"
    ) -notcontains $_.Name
} | ForEach-Object {
    $newPath = Join-Path (Join-Path $script:OUT_DIR "glast/$Version" ) $_.FullName.Substring($script:SRC_DIR.FullName.Length)
    Copy-Item -Path $_.FullName -Destination $newPath -Recurse -Verbose
}

# Zip up the files.
Compress-Archive -Path (Join-Path $script:OUT_DIR "glast") `
    -DestinationPath (Join-Path $script:OUT_DIR "glast-v$Version.zip") -Verbose