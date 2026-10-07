#requires -Version 7.0
# Replay the three extension modules individually in the kernel with leanchecker. Compile first with buildext.ps1.
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
$proofModules = @($context.ExtModules | Where-Object { $_ -ne 'Check' })
foreach ($module in $proofModules) {
    $object = Join-Path $context.ExtOutputRoot "Approx252/$module.olean"
    if (-not (Test-Path -LiteralPath $object -PathType Leaf)) { throw "Compile first; missing object: $object" }
}
if ($PreflightOnly) {
    Write-Host "Extension kernel-check preflight passed for $($proofModules.Count) compiled module(s); no replay performed."
    return
}
$log = Start-252Evidence $context 'leanchecker_ext.log'
foreach ($module in $proofModules) {
    Invoke-252Command $context $context.Checker @("Approx252.$module") "kernel_ext_$module" $log `
        $TimeoutSeconds $MaxWorkingSetMiB
}
Add-Content -LiteralPath $log -Value "SUCCESS: $($proofModules.Count) extension module(s) replayed individually."
