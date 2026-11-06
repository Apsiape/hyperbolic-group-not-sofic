# Non-soficity of OpenAI's torsion-free hyperbolic group: Lean core

This directory proves selected results of the paper in Lean 4. It is the Lean core of the paper, not a formalization of the whole paper.

## What is checked

`Statements.lean` freezes the selected propositions, `Proofs.lean` proves them, and `Audit.lean` checks that they match the original declarations below and prints their axioms. A row credits only the form stated in it. `presentation_ineq`, `presentation_quant`, `linnell` and the residual-word results are universal over their displayed `MarkedLineData` inputs.

| Printed result | Lean name | Checked form |
|---|---|---|
| Theorem 1.1 | `Approx252.exists_torsionFree_wordHyperbolic_not_sofic` | Existential: some torsion-free word-hyperbolic group is nonsofic; the type does not identify the paper's particular group or data. |
| Theorem 3.1 | `NonSofic.presentation_ineq` | The printed sharp inequality, in counts: (r−1)²e ≤ D and Σδ_t ≥ Γ/4. |
| Theorem 1.2, general constant | `NonSofic.presentation_quant` | The printed ε₀ = 1/(4r²N(q−1)), for every displayed admissible datum, in counts (fixed-point counts e with (r−1)²e ≤ D, moved-point counts k with 4r²N(q−1)k < D). |
| Theorem 1.2, constant 1/(6rq) | `NonSofic.quant_lemma22` | Existential: for one choice of prime q, r = 200·200²⁰ and rerun construction data; not for every sufficiently large prime or every admissible datum. The rerun uses c = 200⁻²⁰ instead of 100⁻²⁰; since c·r = 200 ≥ 100, ε₀ = 1/(6rq) is unchanged. |
| Corollary 1.3, word | `NonSofic.exists_rect_word_killed_by_sofic_univ` | The printed universal-word conclusion, with the witness fixed as `residualWitness`. |
| Corollary 1.3, quotient | `NonSofic.quotient_not_sofic` | A stronger form: every homomorphism preserving all rectangular words has nonsofic target; surjectivity is not needed. |
| Lemma 6.2 | `NonSofic.LineFree.lineSubgroup_free` | The printed free basis: injectivity of the free-group lift of x_iuv·x_i00⁻¹ for (u,v) ≠ (0,0). |
| Theorem 6.1, ring form | `NonSofic.collapse` | The printed rank-collapse estimate in abstract ring form; the library supplies the Sylvester-rank adapter. |
| Theorem 6.1, group-ring form | `NonSofic.collapse_groupRing` | The printed estimate for every rank function on K[G], K a characteristic-q division ring. |
| Lemma 6.3 | `NonSofic.isUnit_map_of_zQuotientData` | An algebraic generalization: `ZQuotientData` and `PowersLeftIndep` imply invertibility of the normalized matrix (finite-dimensional proof; the degree is multiplicative-valued, so Lean's `1` means degree zero); φ(Y_i) = φ(Y′)φ(x_i00) gives the printed conclusion. |
| Theorem 1.4 | `NonSofic.linnell` | Stronger negations: every characteristic-q division ring and embedding G → Λ; `IsLinnell` and `IsStronglyHughesFree` omit injectivity and `SatisfiesHF` omits epicness of the target map. `DivisionRing/Sanity.lean` (`unit_isLinnell`, `int_hf_premises`) shows these notions and the (HF) premises are satisfiable, so the negations are not vacuous. |
| Corollary 6.5 | `NonSofic.not_isLinnell_of_split` | Partial, algebraic only: free normalized entries and a rank-sum premise obstruct `IsLinnell`; no splitting or asphericity. |
| Combined data statement (not a numbered result) | `NonSofic.headline_data` | Existential: for one datum, torsion-freeness, word-hyperbolicity, nonsoficity, the characteristic-q division-ring obstructions and the 1/(6rq) model obstruction. |
| Combined group statement (not a numbered result) | `NonSofic.headline` | Existential: one group with geometry, nonsoficity and the division-ring obstructions; not the quantitative, residual-word, free-subgroup or rank clauses. |

The numbered wrappers are `PaperProofs.<suffix>`, with frozen types `PaperStatements.<suffix>`, for the suffixes `theorem_1_1`, `theorem_3_1`, `theorem_1_2_general`, `theorem_1_2_lemma22`, `corollary_1_3_word`, `corollary_1_3_quotient`, `lemma_6_2`, `theorem_6_1`, `theorem_6_1_groupRing`, `lemma_6_3`, `theorem_1_4`, `corollary_6_5_algebraic`, `headline_data`, `headline`. The data-specific theorem `Approx252.presentation_not_sofic` proves `¬ IsSofic (d.presentation hr).GroupType` for `d : MarkedLineData q r` with 0 < r < q and 200 ≤ q; it is not identified with a particular external witness.

**Conventions:** the formal `IsSofic` uses normalized Hamming distance, multiplicativity error at most ε and separation at least 1−ε. No named literature hypothesis is assumed.

**Not formalized:** the identification of the selected Theorem 1.1 wrapper with the paper's particular group; the universal prime and original-data quantifiers of the 1/(6rq) result; Section 5 (hyperlinearity, including Propositions 5.1–5.3); Proposition 6.4 (free-product splitting and asphericity); the topological part of Corollary 6.5; Corollary 6.6 (bi-orderability); Proposition 6.7 (Euler characteristic and nonpositive immersions); Lemma 4.1 as a numbered statement (its transfer and constants 5 and 8 are present as `Approx252.relator_support_le` and `Approx252.rectangle_fixCount_le`); the identification of the presented group with the triangle complex's fundamental group; the Elek–Szabó equivalence of definitions of soficity.

## OpenAI's development

The group, its construction and the imported geometric and finite-field results are OpenAI's. The core vendors its 29-module development at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a` in `vendor/finite-lean/FiniteLean/GroupTheory/OAI/`, ported to Lean 4.35.0. `VENDOR.md` there records the port: `Model.lean` replaces `import Mathlib` by 184 explicit imports; `WordPaths.lean` and `BasedWords.lean` adapt `CategoryTheory.End` using `End.of`, `.asHom` and `End.ext`; `CyclicAction.lean` uses `.norm.asHom.hom`. No theorem or definition statement was changed by the port. The earlier Lean 4.34.1 package remains in the version 1.1.0 archive, DOI [10.5281/zenodo.23374284](https://doi.org/10.5281/zenodo.23374284).

## Trust base

- Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The pins are in `lean-toolchain`, `lake-manifest.json` and `UPSTREAM-PINS.json`; `LIBRARY-MODULES.txt` lists the vendored shared-library modules.
- Every declaration in the table, every numbered wrapper and the supporting roots listed in `AXIOMS.txt` depend only on Lean's three standard axioms, `propext`, `Classical.choice` and `Quot.sound`. `AXIOMS.txt` is the exact axiom output.
- The 28 table declarations and numbered wrappers, with their dependencies, pass two independent kernel checkers, `leanchecker` and `nanoda`.
- `evidence/KERNEL-REPLAY.json` records the kernel replay (export digest, checker binaries, exits) and the run of the reproduce commands on 6 November 2026. `evidence/replay.sh` runs leanchecker over the vendored library modules only; it is not the two-checker replay recorded in `KERNEL-REPLAY.json`.

## Reproduce

With the pinned Lean toolchain on PATH, Git available for fetching the pinned dependencies, one compiler job at a time and at least 4 GiB of free memory, run from `lean/`:

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake build
lake env lean -j1 -M6144 Audit.lean
```

In PowerShell use `$env:LEAN_NUM_THREADS = '1'` for the first line. `lake exe cache get` fetches the Mathlib build cache and `lake build` builds the core. `Audit.lean` prints the type of each checked declaration followed by its axioms; the axiom lines match `AXIOMS.txt`.
