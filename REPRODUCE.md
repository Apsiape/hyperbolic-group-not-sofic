# Reproducing the Lean evidence

The note uses theorems of OpenAI's Lean development for "A torsion-free hyperbolic group that is not residually
finite" (item 252 of OpenAI's mathematics release). This file separates the original audit evidence from the
commands for repeating it.

## Pinned sources

| Item | Value |
|---|---|
| Repository | https://github.com/openai/math |
| Commit | `adc7f1241b42e322a6451854ab7e4b4c146bf78a` (6 October 2026) |
| Lean development | `lean/OAI/GroupTheory/Hyperbolic/` (29 modules), namespace `OAI.Release075` |
| Toolchain | `leanprover/lean4:v4.34.1`, official `lean-4.34.1-windows.zip`, SHA-256 `457698d4e2132243e899ff32178d7ae63c16431d09ed9ad524d859c3581992af`; `lean --version` reports 4.34.1, commit 5045d00 |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1`), as pinned in the upstream `lean/lake-manifest.json` |

## Reproduction commands

Prerequisites: Git, Lean 4.34.1 with `lake` and `leanchecker`, and the pinned Mathlib cache. The scripts require
PowerShell 7 (`pwsh`), use the checked-in [module-order.txt](lean/module-order.txt), and accept paths rather than
requiring the original drive mapping. They never modify upstream sources and rebuild each module instead of
silently reusing an old object. New outputs go to ignored `lean/build/`, not to the historical `lean/evidence/`.

On Linux or macOS the standard upstream route is:

```sh
git clone https://github.com/openai/math oai-math
git -C oai-math checkout --detach adc7f1241b42e322a6451854ab7e4b4c146bf78a
cd oai-math/lean
lake exe cache get
lake build OAI.GroupTheory.Hyperbolic.Main
```

That builds the upstream inputs only. The commands below (PowerShell 7) also compile `lean/Check252.lean`, which
records the theorem statements and axiom reports of the inputs, and the note's own formalization in `lean/ext/`, and
they run the kernel checks.

On Windows, keep checkout and output paths short. An isolated Mathlib checkout avoids fetching the upstream
corpus's unrelated dependencies, including AINTLIB's Windows-incompatible file name. From this note's checkout,
prepare the two pinned checkouts using an existing Lean 4.34.1 installation:

```powershell
git clone https://github.com/openai/math C:/oai252
git -C C:/oai252 checkout --detach adc7f1241b42e322a6451854ab7e4b4c146bf78a
git clone https://github.com/leanprover-community/mathlib4 C:/ml252
git -C C:/ml252 checkout --detach d13f23b723b8a846827a245b89c10fc7d3f11612
Push-Location C:/ml252
try { lake exe cache get } finally { Pop-Location }

# Set this to the existing toolchain's bin directory.
$toolchainBin = 'C:/Lean/lean-4.34.1-windows/bin'
pwsh -NoProfile -File lean/build252.ps1 -SourceRoot C:/oai252/lean -ToolchainBin $toolchainBin -MathlibRoot C:/ml252 -PreflightOnly
pwsh -NoProfile -File lean/build252.ps1 -SourceRoot C:/oai252/lean -ToolchainBin $toolchainBin -MathlibRoot C:/ml252
pwsh -NoProfile -File lean/check252.ps1 -SourceRoot C:/oai252/lean -ToolchainBin $toolchainBin -MathlibRoot C:/ml252
# The note's own transfer (lean/ext), compiled against the objects just built, then kernel-checked:
pwsh -NoProfile -File lean/ext/buildext.ps1 -SourceRoot C:/oai252/lean -ToolchainBin $toolchainBin -MathlibRoot C:/ml252
pwsh -NoProfile -File lean/ext/checkext.ps1 -SourceRoot C:/oai252/lean -ToolchainBin $toolchainBin -MathlibRoot C:/ml252
```

If the full upstream project's dependencies are already cached under its `.lake/packages/`, omit `-MathlibRoot`.
Use `-OutputRoot` and `-EvidenceRoot` to choose short local output paths if needed; pass the same output root to
both scripts. `-Modules Model` on `check252.ps1` selects a single kernel replay. `-PreflightOnly` performs no proof
compilation or kernel replay; on the check script it also requires the selected `.olean` files to exist.
`Check252.stdout.txt` in the new evidence directory contains the audit output.

Resource requirements: the original compilation used about 3.2-3.6 GiB per process, and kernel replay about
2.6 GiB. Run sequentially on a host with sufficient available memory. The scripts default to a 600-second timeout
per invocation and a 4096-MiB working-set guard; `-TimeoutSeconds` and `-MaxWorkingSetMiB` adjust these explicitly.
The polling guard is not a hard committed-memory cap and can overshoot. Use an external job/container limit when
one is required. A workspace limited to 2 GiB can run the preflight/tests but should not run the full Lean build.

Script sanity checks (no Lean compilation):

```powershell
pwsh -NoProfile -File lean/test_scripts.ps1
```

**Full rebuild with these scripts (6 October 2026).** Against the original pinned cached checkout (omitting
`-MathlibRoot`), PowerShell 7.6.6 ran `build252.ps1`, `check252.ps1`, `ext/buildext.ps1` and `ext/checkext.ps1` from
scratch into empty output directories: 29 upstream modules and `Check252` compiled, 29 upstream kernel replays, four
extension modules compiled with the axiom-report check, and three extension kernel replays. All 66 steps exit 0;
only the two audit files produce output, and every axiom report is exactly `[propext, Classical.choice,
Quot.sound]`. Total time 19.3 minutes; peak about 3.6 GiB per compile and 2.6 GiB per replay. Logs and audit output:
`lean/evidence/rebuild-2026-10-06/`. The isolated-cache bootstrap above (a separate Mathlib checkout) has not been
executed.

## Original build procedure

The saved Windows audit used a short `subst` drive to avoid paths exceeding 260 characters. It:

1. ran `lake update` (manifest unchanged; the unrelated dependency AINTLIB contains a file name with colons, so it was
   checked out with that one file excluded; no Hyperbolic module imports it);
2. fetched the Mathlib cache with `.lake/packages/mathlib/.lake/build/bin/cache.exe get` (8,908 files), from a
   `subst` drive letter to stay under the path limit;
3. compiled the 29 modules one at a time, in dependency order, with the same toolchain and the lakefile's only option:
   `lean -DautoImplicit=false -o <M>.olean -i <M>.ilean OAI/GroupTheory/Hyperbolic/<M>.lean`, with `LEAN_PATH` set to
   the Mathlib, Batteries, Aesop, Qq, ProofWidgets, Plausible, LeanSearchClient and ImportGraph build directories plus
   the output directory. The module order is now included as `lean/module-order.txt`; the revised scripts replace
   the original machine-specific versions. The logs retain the original paths and results.

## Results (`lean/evidence/`)

- `build252.log` (original audit): 28 modules have recorded zero exits with empty output, about 16-29 s per module
  warm and 3.2-3.6 GB peak memory. `Model` (the first module, cold Mathlib import, 268 s) produced its `.olean` with
  no messages in the first run, but the script did not capture its exit code; the second run therefore skipped it.
  That gap is now closed twice: `model_recompile.log` records a separate recompile of `Model` (exit 0, no output),
  and the full rebuild in `rebuild-2026-10-06/` records exit 0 for every module.
- `leanchecker.log`: Lean's `leanchecker` replayed the declarations of each of the 29 modules in the kernel, one module
  per run; all exit 0 with no messages (about 2.6 GB peak). One batched run of all modules at once was stopped by our
  memory guard and is not part of the evidence.
- `check252.out`, from `lean/Check252.lean`: the elaborated statements of every declaration the note uses, and
  `#print axioms` for each, all exactly `[propext, Classical.choice, Quot.sound]`. The file also re-enters the
  comparator challenge's definitions of `TorsionFree` and `WordHyperbolic` in a fresh namespace, checks they agree
  with the repository's by `rfl`, and derives the 0/1 form of the rank-reduction lemma (`zeroOne_rank_reduction`).

A source scan of the 29 modules finds no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`,
`unsafe` or `opaque`.

## What the Lean development proves and does not prove

Proved, for the presented group `(d.presentation hr).GroupType` of every `MarkedLineData`: the triangle relations,
nontriviality of every rectangular word, torsion-freeness and word-hyperbolicity (thin geodesic triangles in a Cayley
graph); the budget is a field of the data, built by `exists_markedLineData` (with `r >= 100 * 100^20`, `r < q`); the
line certificate (any finite field, any dimension); rank reduction (integer matrices, squared row norms at most `r`);
and the main theorem `OAI.Release075.main`. Not formalized: the identification of the presented group with the
fundamental group of a triangle complex, the general criterion (paper Theorem 2.1), and the paper's Corollary 1.2
(non-linearity). The note uses none of these.

## The transfer

The note gives complete written proofs of the transfer in Sections 3-4, with two independent derivations reported
in the manuscript. The transfer is also formalized in `lean/ext/` (see its README), on top of OpenAI's development:

```lean
theorem Approx252.exists_torsionFree_wordHyperbolic_not_sofic :
    ∃ (G : Type) (_ : Group G), TorsionFree G ∧ WordHyperbolic G ∧ ¬ IsSofic G
```

with OpenAI's `TorsionFree` and `WordHyperbolic` and with `IsSofic` defined in `lean/ext/Approx252/Sofic.lean`
(normalized Hamming distance, separation `1 - ε`), since Mathlib has no definition of soficity. Its axioms are
exactly `[propext, Classical.choice, Quot.sound]`, and the three new modules pass the kernel replay.

What is machine-checked is this headline statement. The formal proof uses cruder constants than the note's
Theorem 1.2 (rectangle fraction `1/r²`, single threshold `1/(8 r² N q)`). Not formalized: the note's sharper
constants, Corollary 1.3 and its consequences, and the equivalence of this definition of soficity with other common
forms (the standard amplification theorem of Elek and Szabó).
