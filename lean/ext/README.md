# Lean formalization of the transfer (namespace `Approx252`)

This folder formalizes the note's own argument (Sections 3 and 4) on top of OpenAI's Lean development for "A
torsion-free hyperbolic group that is not residually finite", at the commit and toolchain pinned in `REPRODUCE.md`. Together with OpenAI's theorems it proves, in Lean,

```lean
theorem Approx252.exists_torsionFree_wordHyperbolic_not_sofic :
    ∃ (G : Type) (_ : Group G), TorsionFree G ∧ WordHyperbolic G ∧ ¬ IsSofic G
```

where `TorsionFree` and `WordHyperbolic` are OpenAI's `OAI.Release075` definitions (equal by `rfl` to their comparator
challenge statement) and `IsSofic` is defined here, because Mathlib v4.34.1 has no definition of soficity:

```lean
def dis (σ τ : Equiv.Perm Ω) : ℕ := (σ⁻¹ * τ).support.card          -- #{c | σ c ≠ τ c}
noncomputable def hammingDist {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : ℝ := (dis σ τ : ℝ) / n
def IsSofic (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (φ : G → Equiv.Perm (Fin n)),
    (∀ g ∈ F, ∀ h ∈ F, hammingDist (φ (g * h)) (φ g * φ h) ≤ ε) ∧
    (∀ g ∈ F, g ≠ 1 → 1 - ε ≤ hammingDist (φ g) 1)
```

## What exactly is machine-checked

- **Formalized:** the rank obstruction for approximate permutation models (`PermModel.lean`:
  `approx_rank_obstruction`, `no_model_of_line_blocks`, and `no_model_of_line_blocks_threshold`, whose single threshold
  is `ε ≤ 1/(8 r² N q)` for both the relator and the rectangle fractions); the passage from `IsSofic` to such models
  (`Sofic.lean`: `IsSofic.exists_approx`, `relator_support_le` with constant 5, `rectangle_fixCount_le` with constant
  8); and the conclusion for every `MarkedLineData` with `0 < r < q` and `200 ≤ q` (`NonSofic.lean`:
  `presentation_not_sofic`) and the existence theorem above.
- **Not formalized:** the equivalence of this definition of soficity (separation `1 - ε`, permutations, normalized
  Hamming distance) with other common forms (for example separation bounded below by a fixed constant, or maps that
  are not permutations). That equivalence is the standard amplification theorem of Elek and Szabó, cited in the
  note. The definition here is the form used in the note's Lemma 4.1. As with OpenAI's development, the
  identification of the presented group with π₁ of the triangle complex is not formalized and is not used.
- **Constants:** the Lean proof uses a cruder count of nondegenerate rectangle terms (`r⁴` instead of `r²(r-1)²`), so
  its rectangle threshold is `η ≤ 1/r²` and its explicit single threshold is `1/(8 r² N q)`, slightly weaker than the
  note's Theorem 1.2 (`1/(r-1)²` and `1/(4 r² N (q-1))`). The theorem `¬ IsSofic` does not depend on these constants.

## Evidence (`evidence/`)

- `buildext.log`: each module compiled with `lean -DautoImplicit=false` against the compiled OpenAI modules (same
  toolchain and options as `lean/build252.ps1`). An early `PermModel` build failed on an unknown identifier and was
  fixed; the final builds of `PermModel`, `Sofic` and `NonSofic`, in that order, exit 0 with no output.
- `leanchecker_ext.log`: Lean's `leanchecker` replayed each of the three modules in the kernel; all exit 0 with no
  messages (about 2.6 GB peak each).
- `check_out.txt`, from `Approx252/Check.lean`: `#print axioms` for every theorem listed above prints exactly
  `[propext, Classical.choice, Quot.sound]`; the file also prints the elaborated statements.

No file contains `sorry`, `admit` or `axiom`. The logs above are from the original development run; the full
rebuild with the scripts below is recorded in `../evidence/rebuild-2026-10-06/` (`buildext.log`,
`leanchecker_ext.log`, `ext_Check.stdout.txt`).

## Rebuilding

`buildext.ps1` and `checkext.ps1` take the same parameters as `../build252.ps1` and `../check252.ps1`
(`-SourceRoot`, `-ToolchainBin`, optional `-MathlibRoot`, `-OutputRoot`, `-EvidenceRoot`, `-TimeoutSeconds`,
`-MaxWorkingSetMiB`, `-PreflightOnly`) plus `-ExtOutputRoot` for the extension's objects. They reuse the upstream
preflight of `../252-common.ps1` (pinned commit, toolchain, Mathlib and module order), require the upstream objects
built by `../build252.ps1` in `-OutputRoot`, refuse sources containing `sorry`, `admit` or `axiom`, compile
`PermModel`, `Sofic`, `NonSofic` and `Check` in order, and fail unless the axiom report of `Check.lean` lists exactly
eight theorems, each with exactly `[propext, Classical.choice, Quot.sound]`. `checkext.ps1` then replays the three
proof modules in the kernel, one at a time. Run them after the upstream scripts, with the same roots:

```powershell
pwsh -NoProfile -File lean/build252.ps1  -SourceRoot C:/oai252/lean -ToolchainBin $toolchainBin -MathlibRoot C:/ml252
pwsh -NoProfile -File lean/check252.ps1  -SourceRoot C:/oai252/lean -ToolchainBin $toolchainBin -MathlibRoot C:/ml252
pwsh -NoProfile -File lean/ext/buildext.ps1 -SourceRoot C:/oai252/lean -ToolchainBin $toolchainBin -MathlibRoot C:/ml252
pwsh -NoProfile -File lean/ext/checkext.ps1 -SourceRoot C:/oai252/lean -ToolchainBin $toolchainBin -MathlibRoot C:/ml252
```
