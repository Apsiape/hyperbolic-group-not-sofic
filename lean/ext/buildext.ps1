#requires -Version 7.0
# Compile the transfer formalization (namespace Approx252) against the upstream objects built by ../build252.ps1.
# Same preflight, bounded runner and evidence layout as the upstream scripts; rebuilds every module.
[CmdletBinding()]
param(
    [Parameter(Mandatory)][string]$SourceRoot,
    [Parameter(Mandatory)][string]$ToolchainBin,
    [string]$MathlibRoot = '',
    [string]$OutputRoot = (Join-Path $PSScriptRoot '../build/obj'),
    [string]$ExtOutputRoot = (Join-Path $PSScriptRoot '../build/ext-obj'),
    [string]$EvidenceRoot = (Join-Path $PSScriptRoot '../build/evidence'),
    [ValidateRange(1,3600)][int]$TimeoutSeconds = 600,
    [ValidateRange(32,8192)][int]$MaxWorkingSetMiB = 4096,
    [switch]$PreflightOnly
)
. (Join-Path $PSScriptRoot 'ext-common.ps1')
$context = Get-ExtContext $SourceRoot $ToolchainBin $MathlibRoot $OutputRoot $ExtOutputRoot $EvidenceRoot
if ($PreflightOnly) {
    Write-Host 'Extension preflight passed: pinned upstream checks, upstream objects present, sources free of sorry/admit/axiom.'
    return
}
$log = Start-252Evidence $context 'buildext.log'
$moduleDir = Join-Path $context.ExtOutputRoot 'Approx252'
New-Item -ItemType Directory -Force -Path $moduleDir | Out-Null
foreach ($module in $context.ExtModules) {
    $arguments = @('-DautoImplicit=false', '-R', $PSScriptRoot,
        '-o', (Join-Path $moduleDir "$module.olean"), '-i', (Join-Path $moduleDir "$module.ilean"),
        (Join-Path $PSScriptRoot "Approx252/$module.lean"))
    Invoke-252Command $context $context.Lean $arguments "ext_$module" $log $TimeoutSeconds $MaxWorkingSetMiB
}
# Check.lean prints the axiom report; require exactly the standard axioms for every listed theorem.
$report = Get-Content -LiteralPath (Join-Path $context.EvidenceRoot 'ext_Check.stdout.txt') -Raw
$lines = @($report -split "`r?`n" | Where-Object { $_ -match 'depends on axioms' })
$expected = 8
if ($lines.Count -ne $expected) { throw "Expected $expected axiom reports, found $($lines.Count)." }
foreach ($line in $lines) {
    if ($line -notmatch 'depends on axioms: \[propext, Classical\.choice, Quot\.sound\]$') {
        throw "Nonstandard axioms: $line"
    }
}
if ($report -match 'sorryAx') { throw 'The axiom report mentions sorryAx.' }
Add-Content -LiteralPath $log -Value "SUCCESS: $($context.ExtModules.Count) extension modules compiled; $expected axiom reports standard."
