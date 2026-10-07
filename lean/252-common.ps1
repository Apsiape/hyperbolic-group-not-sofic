#requires -Version 7.0
# Shared preflight and bounded native-process runner. No sources are fetched or edited.
Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

function Get-252Context {
    param([string]$SourceRoot, [string]$ToolchainBin,
          [string]$OutputRoot, [string]$EvidenceRoot, [string]$MathlibRoot = '')
    $source = (Resolve-Path -LiteralPath $SourceRoot).Path
    $bin = (Resolve-Path -LiteralPath $ToolchainBin).Path
    $suffix = if ($IsWindows) { '.exe' } else { '' }
    $lean = Join-Path $bin "lean$suffix"
    $checker = Join-Path $bin "leanchecker$suffix"
    foreach ($exe in @($lean, $checker)) {
        if (-not (Test-Path -LiteralPath $exe -PathType Leaf)) { throw "Missing executable: $exe" }
    }
    $pin = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
    $head = & git -C $source rev-parse HEAD
    if ($LASTEXITCODE -ne 0 -or $head -ne $pin) { throw "Source checkout must be at $pin." }
    & git -C $source diff --quiet HEAD -- OAI/GroupTheory/Hyperbolic
    if ($LASTEXITCODE -ne 0) { throw 'Tracked Hyperbolic sources differ from the pinned commit.' }
    $toolchain = (Get-Content -LiteralPath (Join-Path $source 'lean-toolchain') -Raw).Trim()
    if ($toolchain -ne 'leanprover/lean4:v4.34.1') { throw "Unexpected toolchain: $toolchain" }
    $version = & $lean --version
    if ($LASTEXITCODE -ne 0 -or $version -notmatch '^Lean \(version 4\.34\.1(?:,|\))') {
        throw "Expected Lean 4.34.1; found: $version"
    }
    if ($MathlibRoot) {
        $mathlib = (Resolve-Path -LiteralPath $MathlibRoot).Path
        $packages = Join-Path $mathlib '.lake/packages'
    } else {
        $packages = Join-Path $source '.lake/packages'
        $mathlib = Join-Path $packages 'mathlib'
    }
    $mathlibHead = & git -C $mathlib rev-parse HEAD
    if ($LASTEXITCODE -ne 0 -or $mathlibHead -ne 'd13f23b723b8a846827a245b89c10fc7d3f11612') {
        throw 'Mathlib does not match the pinned commit.'
    }
    $deps = @(Join-Path $mathlib '.lake/build/lib/lean') + @(
        @('batteries','aesop','Qq','proofwidgets','plausible','LeanSearchClient','importGraph') |
            ForEach-Object { Join-Path $packages "$_/.lake/build/lib/lean" }
    )
    foreach ($dir in $deps) {
        if (-not (Test-Path -LiteralPath $dir -PathType Container)) { throw "Missing cached dependency: $dir" }
    }
    $orderPath = Join-Path $PSScriptRoot 'module-order.txt'
    $modules = @(Get-Content -LiteralPath $orderPath | Where-Object { $_.Trim() } | ForEach-Object { $_.Trim() })
    if ($modules.Count -ne 29 -or @($modules | Select-Object -Unique).Count -ne 29) {
        throw 'module-order.txt must contain 29 distinct modules.'
    }
    $seen = @{}
    foreach ($module in $modules) {
        if ($module -notmatch '^[A-Za-z][A-Za-z0-9_]*$') { throw "Invalid module name: $module" }
        $file = Join-Path $source "OAI/GroupTheory/Hyperbolic/$module.lean"
        if (-not (Test-Path -LiteralPath $file -PathType Leaf)) { throw "Missing source: $file" }
        foreach ($line in Get-Content -LiteralPath $file) {
            if ($line -match '^import ') {
                foreach ($match in [regex]::Matches($line, 'OAI\.GroupTheory\.Hyperbolic\.([A-Za-z][A-Za-z0-9_]*)')) {
                    $dependency = $match.Groups[1].Value
                    if (-not $seen.ContainsKey($dependency)) { throw "$module precedes dependency $dependency." }
                }
            }
        }
        $seen[$module] = $true
    }
    $separator = [IO.Path]::PathSeparator
    [pscustomobject]@{
        SourceRoot = $source; Lean = $lean; Checker = $checker; Modules = $modules
        OutputRoot = [IO.Path]::GetFullPath($OutputRoot)
        EvidenceRoot = [IO.Path]::GetFullPath($EvidenceRoot)
        LeanPath = (@([IO.Path]::GetFullPath($OutputRoot)) + $deps) -join $separator
        Version = $version; SourceCommit = $head; MathlibCommit = $mathlibHead
        OrderHash = (Get-FileHash -LiteralPath $orderPath -Algorithm SHA256).Hash
    }
}

function Start-252Evidence {
    param($Context, [string]$LogName)
    New-Item -ItemType Directory -Force -Path $Context.OutputRoot, $Context.EvidenceRoot | Out-Null
    $log = Join-Path $Context.EvidenceRoot $LogName
    Add-Content -LiteralPath $log -Value @(
        "RUN $([DateTime]::UtcNow.ToString('o'))", "SOURCE=$($Context.SourceCommit)",
        "MATHLIB=$($Context.MathlibCommit)", "TOOLCHAIN=$($Context.Version)",
        "MODULE_ORDER_SHA256=$($Context.OrderHash)", "LEAN_PATH=$($Context.LeanPath)"
    )
    $log
}

function Invoke-252Command {
    param($Context, [string]$Executable, [string[]]$Arguments,
          [string]$Label, [string]$Log, [int]$TimeoutSeconds, [int]$MaxWorkingSetMiB)
    $info = [Diagnostics.ProcessStartInfo]::new()
    $info.FileName = $Executable
    $info.WorkingDirectory = $Context.SourceRoot
    $info.UseShellExecute = $false
    $info.CreateNoWindow = $true
    $info.RedirectStandardOutput = $true
    $info.RedirectStandardError = $true
    $info.Environment['LEAN_PATH'] = $Context.LeanPath
    foreach ($argument in $Arguments) { $info.ArgumentList.Add($argument) }
    $process = [Diagnostics.Process]::new()
    $process.StartInfo = $info
    $watch = [Diagnostics.Stopwatch]::StartNew()
    $peak = 0L
    $stopReason = ''
    $started = $false
    try {
        $started = $process.Start()
        if (-not $started) { throw "Could not start $Label." }
        $stdoutTask = $process.StandardOutput.ReadToEndAsync()
        $stderrTask = $process.StandardError.ReadToEndAsync()
        while (-not $process.WaitForExit(200)) {
            $process.Refresh()
            $peak = [Math]::Max($peak, $process.PeakWorkingSet64)
            if ($watch.Elapsed.TotalSeconds -ge $TimeoutSeconds) { $stopReason = 'timeout' }
            if ($process.WorkingSet64 -gt ([long]$MaxWorkingSetMiB * 1MB)) { $stopReason = 'working-set guard' }
            if ($stopReason) {
                if (-not $process.HasExited) { $process.Kill($true) }
                break
            }
        }
        $process.WaitForExit()
        $stdout = $stdoutTask.GetAwaiter().GetResult()
        $stderr = $stderrTask.GetAwaiter().GetResult()
        Set-Content -LiteralPath (Join-Path $Context.EvidenceRoot "$Label.stdout.txt") -Value $stdout -NoNewline
        Set-Content -LiteralPath (Join-Path $Context.EvidenceRoot "$Label.stderr.txt") -Value $stderr -NoNewline
        $line = '{0} exit={1} time={2:N1}s peakMiB={3:N0} stop={4}' -f `
            $Label, $process.ExitCode, $watch.Elapsed.TotalSeconds, ($peak / 1MB), $stopReason
        Add-Content -LiteralPath $Log -Value $line
        Write-Host $line
        if ($stopReason -or $process.ExitCode -ne 0) { throw "$Label failed; see $($Context.EvidenceRoot)." }
    } finally {
        if ($started -and -not $process.HasExited) { $process.Kill($true); $process.WaitForExit() }
        $process.Dispose()
    }
}
