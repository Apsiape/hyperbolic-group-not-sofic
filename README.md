# Non-soficity of OpenAI's torsion-free hyperbolic group

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23202475.svg)](https://doi.org/10.5281/zenodo.23202475)

Seth Douglas and Nidhal Mghirbi

Is every word-hyperbolic group sofic? OpenAI recently constructed a torsion-free word-hyperbolic group that is not
residually finite, with a Lean formalization ([openai/math](https://github.com/openai/math)). This repository holds
a short note showing that the same group is **not sofic**, together with a Lean formalization of that conclusion.

The idea: OpenAI's rank argument against finite quotients uses a finite quotient only through its permutation
matrices, and it survives approximation. A relation that holds on all but a small fraction of points costs a small
rank error, and a word with few fixed points costs a small trace error, so approximate permutation models are
excluded at a fixed positive accuracy, while soficity would provide them at every accuracy. The group and every
input to the argument are OpenAI's; the approximate argument, its constants and the formalization are ours.

## Contents

- [`paper/paper.pdf`](paper/paper.pdf) and [`paper/paper.tex`](paper/paper.tex): the note. Build with
  `python paper/build.py` and an existing LaTeX installation.
- [`lean/ext/`](lean/ext/README.md): the Lean formalization of the note's argument, on top of OpenAI's development.
- [`lean/`](lean/): an audit file for the imported theorems (`Check252.lean`), build and kernel-check scripts
  (PowerShell 7), the module order, and the evidence logs.
- [`REPRODUCE.md`](REPRODUCE.md): pinned sources, reproduction commands, and what each log records.

## What is machine-checked

The Lean theorem `Approx252.exists_torsionFree_wordHyperbolic_not_sofic` states

```lean
∃ (G : Type) (_ : Group G), TorsionFree G ∧ WordHyperbolic G ∧ ¬ IsSofic G
```

with OpenAI's definitions of torsion-free and word-hyperbolic and the standard definition of soficity (normalized
Hamming distance, separation `1 - ε`), which is defined in `lean/ext/` because Mathlib has none. It uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`. The note's sharper constants, its corollaries (for example,
that one fixed element dies in every sofic quotient), and the equivalence of this definition of soficity with other
common forms are proved in writing only.

A complete rebuild from scratch with the scripts in this repository compiled and kernel-checked all 29 modules of
OpenAI's development and the formalization; every step exits 0
([`lean/evidence/rebuild-2026-10-06/`](lean/evidence/rebuild-2026-10-06/)).

## Credit and license

The group, its construction and all imported theorems are OpenAI's: "A torsion-free hyperbolic group that is not
residually finite" (OpenAI Math Release, 23 September 2026) and its Lean development at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Their sources are not redistributed here.

The paper and documentation are licensed CC BY 4.0, the scripts MIT, and the Lean files Apache 2.0, since they
adapt parts of OpenAI's Apache-2.0 development; see [RIGHTS.md](RIGHTS.md) and [NOTICE](NOTICE). To cite this work, use
the DOI [10.5281/zenodo.23202475](https://doi.org/10.5281/zenodo.23202475) (version 1.0.0; all versions: [10.5281/zenodo.23202474](https://doi.org/10.5281/zenodo.23202474))
or see [CITATION.cff](CITATION.cff).
