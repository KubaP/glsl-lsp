# This script outputs the version number which is used in the github actions workflow to later label the git tag.

$metadata = Get-Content -Path "$PSScriptRoot/../glast/Cargo.toml" -ErrorAction Stop
$match = [regex]::Matches($metadata, 'version = "(.*?)"')
"::set-output name=version::$($match.Groups[1].Value)"
