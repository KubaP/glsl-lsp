# Output the version number which is used in the release action.
$metadata = Get-Content -Path "$PSScriptRoot/../glast/Cargo.toml" -ErrorAction Stop
$match = [regex]::Matches($metadata, 'version = "(.*?)"')
"::set-output name=VERSION::$($match.Groups[1].Value)"

$version = $match.Groups[1].Value

Write-Host "Package Version: $version"
Write-Host "Commit SHA: $env:GITHUB_SHA"

# Tag the commit - not necessary; the release action does it for us.
# git tag "glast/v$version" "$env:GITHUB_SHA"
# git push origin "glast/v$version"

# Prepare the release artefact.
$script:SRC_DIR = Get-Item -Path "$PSScriptRoot/../glast"
New-Item -Path "$PSScriptRoot/../" -Name "out" -ItemType Directory -Force -Verbose
New-Item -Path "$PSScriptRoot/../out/" -Name "glast" -ItemType Directory -Force -Verbose
New-Item -Path "$PSScriptRoot/../out/glast/" -Name "$version" -ItemType Directory -Force -Verbose
$script:OUT_DIR = Get-Item -Path "$PSScriptRoot/../out"

# Copy the contents of the `glast` project into an output directory.
# Filter out folders and files which shouldn't be part of the final output.
Get-ChildItem -Path $script:SRC_DIR | Where-Object {
    @(
        "Cargo.toml",
        "src",
        "tests"
    ) -contains $_.Name
} | ForEach-Object {
    $newPath = Join-Path (Join-Path $script:OUT_DIR "glast/$version" ) $_.FullName.Substring($script:SRC_DIR.FullName.Length)
    Copy-Item -Path $_.FullName -Destination $newPath -Recurse -Verbose -ErrorAction Stop
}

# Zip up the content.
Compress-Archive -Path (Join-Path $script:OUT_DIR "glast") `
    -DestinationPath (Join-Path $script:OUT_DIR "glast-v$version.zip") -Verbose -ErrorAction Stop
