#requires -Version 7.0
# Compile all pinned modules and the audit file; rebuild rather than silently reuse.
[CmdletBinding()]
param(
    [Parameter(Mandatory)][string]$SourceRoot,
    [Parameter(Mandatory)][string]$ToolchainBin,
    [string]$MathlibRoot = '',
    [string]$OutputRoot = (Join-Path $PSScriptRoot 'build/obj'),
    [string]$EvidenceRoot = (Join-Path $PSScriptRoot 'build/evidence'),
    [ValidateRange(1,3600)][int]$TimeoutSeconds = 600,
    [ValidateRange(32,8192)][int]$MaxWorkingSetMiB = 4096,
    [switch]$PreflightOnly
)
. (Join-Path $PSScriptRoot '252-common.ps1')
$context = Get-252Context $SourceRoot $ToolchainBin $OutputRoot $EvidenceRoot $MathlibRoot
if ($PreflightOnly) {
    Write-Host 'Build preflight passed: pinned sources, toolchain, cached dependencies and all 29 module imports checked.'
    return
}
$log = Start-252Evidence $context 'build252.log'
$moduleDir = Join-Path $context.OutputRoot 'OAI/GroupTheory/Hyperbolic'
New-Item -ItemType Directory -Force -Path $moduleDir | Out-Null
foreach ($module in $context.Modules) {
    $arguments = @('-DautoImplicit=false', '-o', (Join-Path $moduleDir "$module.olean"),
        '-i', (Join-Path $moduleDir "$module.ilean"), "OAI/GroupTheory/Hyperbolic/$module.lean")
    Invoke-252Command $context $context.Lean $arguments $module $log $TimeoutSeconds $MaxWorkingSetMiB
}
$audit = Join-Path $PSScriptRoot 'Check252.lean'
$arguments = @('-DautoImplicit=false', '-R', $PSScriptRoot, '-o', (Join-Path $context.OutputRoot 'Check252.olean'),
    '-i', (Join-Path $context.OutputRoot 'Check252.ilean'), $audit)
Invoke-252Command $context $context.Lean $arguments 'Check252' $log $TimeoutSeconds $MaxWorkingSetMiB
Add-Content -LiteralPath $log -Value 'SUCCESS: all 29 upstream modules and Check252 compiled.'
