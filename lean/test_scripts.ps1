#requires -Version 7.0
# Small process-runner tests. No Lean proof compilation or kernel replay.
Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
foreach ($file in @('252-common.ps1','build252.ps1','check252.ps1','ext/ext-common.ps1','ext/buildext.ps1','ext/checkext.ps1')) {
    $tokens = $null; $errors = $null
    $null = [Management.Automation.Language.Parser]::ParseFile(
        (Join-Path $PSScriptRoot $file), [ref]$tokens, [ref]$errors)
    if ($errors.Count) { throw "Parse errors in ${file}: $errors" }
}
. (Join-Path $PSScriptRoot '252-common.ps1')
$temporary = Join-Path ([IO.Path]::GetTempPath()) ('nonsofic-script-test-' + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $temporary | Out-Null
$context = [pscustomobject]@{
    SourceRoot = $PSScriptRoot; EvidenceRoot = $temporary; LeanPath = 'test path with spaces'
}
$shell = (Get-Process -Id $PID).Path
$log = Join-Path $temporary 'runner.log'
Invoke-252Command $context $shell @('-NoLogo','-NoProfile','-Command',
    "[Console]::Out.Write('argument with spaces'); [Console]::Error.Write('stderr captured'); exit 0") `
    'success' $log 10 256
if ((Get-Content -LiteralPath (Join-Path $temporary 'success.stdout.txt') -Raw) -ne 'argument with spaces') {
    throw 'Native argument or stdout handling failed.'
}
if ((Get-Content -LiteralPath (Join-Path $temporary 'success.stderr.txt') -Raw) -ne 'stderr captured') {
    throw 'Stderr capture failed.'
}
foreach ($case in @(
    @{ Name = 'nonzero'; Command = 'exit 7'; Timeout = 10; Memory = 256 },
    @{ Name = 'timeout'; Command = 'Start-Sleep -Seconds 15'; Timeout = 1; Memory = 256 },
    @{ Name = 'guard'; Command = 'Start-Sleep -Seconds 15'; Timeout = 10; Memory = 1 }
)) {
    $failed = $false
    try {
        Invoke-252Command $context $shell @('-NoLogo','-NoProfile','-Command',$case.Command) `
            $case.Name $log $case.Timeout $case.Memory
    } catch { $failed = $true }
    if (-not $failed) { throw "Failure not propagated: $($case.Name)" }
}
$lines = Get-Content -LiteralPath $log -Raw
foreach ($pattern in @('nonzero exit=7', 'stop=timeout', 'stop=working-set guard')) {
    if (-not $lines.Contains($pattern)) { throw "Missing failure evidence: $pattern" }
}
$failed = $false
try {
    Invoke-252Command $context (Join-Path $temporary 'missing-executable') @() 'missing' $log 10 256
} catch { $failed = $true }
if (-not $failed) { throw 'Missing executable was not rejected.' }
Write-Host 'PASS: script parsing, argument handling, stdout/stderr capture, nonzero exits, timeout, memory guard and launch failure.'
Write-Host "Test evidence: $temporary"
