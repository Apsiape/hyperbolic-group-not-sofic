#requires -Version 7.0
# Shared preflight for the extension scripts: reuses the upstream checks of ../252-common.ps1, then requires the
# upstream objects, scans the extension sources and extends LEAN_PATH with the extension output directory.
Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
. (Join-Path $PSScriptRoot '../252-common.ps1')

function Get-ExtContext {
    param([string]$SourceRoot, [string]$ToolchainBin, [string]$MathlibRoot,
          [string]$OutputRoot, [string]$ExtOutputRoot, [string]$EvidenceRoot)
    $context = Get-252Context $SourceRoot $ToolchainBin $OutputRoot $EvidenceRoot $MathlibRoot
    foreach ($module in $context.Modules) {
        $object = Join-Path $context.OutputRoot "OAI/GroupTheory/Hyperbolic/$module.olean"
        if (-not (Test-Path -LiteralPath $object -PathType Leaf)) {
            throw "Build the upstream modules first (../build252.ps1); missing object: $object"
        }
    }
    $modules = @('PermModel', 'Sofic', 'NonSofic', 'Check')
    foreach ($module in $modules) {
        $file = Join-Path $PSScriptRoot "Approx252/$module.lean"
        if (-not (Test-Path -LiteralPath $file -PathType Leaf)) { throw "Missing source: $file" }
        $text = Get-Content -LiteralPath $file -Raw
        if ($text -match '(?m)\b(sorry|admit)\b' -or $text -match '(?m)^\s*axiom\s') {
            throw "Source contains sorry, admit or axiom: $file"
        }
    }
    $extOut = [IO.Path]::GetFullPath($ExtOutputRoot)
    $context | Add-Member -NotePropertyName ExtOutputRoot -NotePropertyValue $extOut
    $context | Add-Member -NotePropertyName ExtModules -NotePropertyValue $modules
    $context.LeanPath = (@($extOut) + @($context.LeanPath)) -join [IO.Path]::PathSeparator
    $context
}
