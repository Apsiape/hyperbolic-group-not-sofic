#requires -Version 7.0
# Replay upstream modules individually. No all-modules batch or implicit skip.
[CmdletBinding()]
param(
    [Parameter(Mandatory)][string]$SourceRoot,
    [Parameter(Mandatory)][string]$ToolchainBin,
    [string]$MathlibRoot = '',
    [string]$OutputRoot = (Join-Path $PSScriptRoot 'build/obj'),
    [string]$EvidenceRoot = (Join-Path $PSScriptRoot 'build/evidence'),
    [string[]]$Modules = @(),
    [ValidateRange(1,3600)][int]$TimeoutSeconds = 600,
    [ValidateRange(32,8192)][int]$MaxWorkingSetMiB = 4096,
    [switch]$PreflightOnly
)
. (Join-Path $PSScriptRoot '252-common.ps1')
$context = Get-252Context $SourceRoot $ToolchainBin $OutputRoot $EvidenceRoot $MathlibRoot
if ($Modules.Count -eq 0) { $Modules = $context.Modules }
foreach ($module in $Modules) {
    if ($module -notin $context.Modules) { throw "Unknown module: $module" }
    $object = Join-Path $context.OutputRoot "OAI/GroupTheory/Hyperbolic/$module.olean"
    if (-not (Test-Path -LiteralPath $object -PathType Leaf)) { throw "Compile first; missing object: $object" }
}
if ($PreflightOnly) {
    Write-Host "Kernel-check preflight passed for $($Modules.Count) compiled module(s); no replay performed."
    return
}
$log = Start-252Evidence $context 'leanchecker.log'
foreach ($module in $Modules) {
    Invoke-252Command $context $context.Checker @("OAI.GroupTheory.Hyperbolic.$module") `
        "kernel_$module" $log $TimeoutSeconds $MaxWorkingSetMiB
}
Add-Content -LiteralPath $log -Value "SUCCESS: $($Modules.Count) upstream module(s) replayed individually."
