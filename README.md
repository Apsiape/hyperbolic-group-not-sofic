# Non-soficity of OpenAI's torsion-free hyperbolic group

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23202474.svg)](https://doi.org/10.5281/zenodo.23202474)

Seth Douglas and Nidhal Mghirbi

Is every word-hyperbolic group sofic? OpenAI recently constructed a torsion-free word-hyperbolic group that is not
residually finite, with a Lean formalization ([openai/math](https://github.com/openai/math)). This repository holds
a short note showing that the same group is **not sofic**, together with a Lean formalization of that conclusion.

The idea: OpenAI's rank argument against finite quotients uses a finite quotient only through its permutation
matrices, and it survives approximation. A relation that holds on all but a small fraction of points costs a small
rank error, and a word with few fixed points costs a small trace error, so approximate permutation models are
excluded at a fixed positive accuracy, while soficity would provide them at every accuracy. The group and every
input to the argument are OpenAI's; the approximate argument, its constants and the formalization are ours.

Version 1.1.0 adds a second result from the same rectangles and the same finite-field certificate: for every
division ring K of the characteristic q fixed by the construction, the group ring K[G], and the group ring over K of
any group containing G, has no Linnell division ring. Freeness of certain line subgroups would force full rank, and
the certificate forces the rank to collapse; no zero divisor is exhibited. In characteristic two, OpenAI's
torsion-free groups with zero divisors, or with a group algebra that is not directly finite, already show that Linnell
division rings need not exist; the new result concerns G itself. The note also splits G as a free product of a free
group and a torsion-free hyperbolic group that again has no Linnell division ring in characteristic q, shows that G
is not bi-orderable, and records what the argument says about hyperlinearity.

## Version 1.2.0

November 2026. A preprint; it has not been peer reviewed.

This version replaces the earlier Lean 4.34.1 package by a source-only Lean core, which proves the printed sharp rank inequality, the general quantitative
obstruction, both residual-word conclusions, line-subgroup freeness and rank collapse, with existential forms of
Theorem 1.1 and of the 1/(6rq) result, using only Lean's three standard axioms and passing the leanchecker and
nanoda kernel checkers. [lean/README.md](lean/README.md) and Appendix B of the paper give the exact scope, what
is not formalized and the build commands. The mathematical statements, equations and existing section numbers
are unchanged.

## Contents and reproduction

- [Manuscript](paper/paper.pdf) and [LaTeX source](paper/paper.tex). Build with
  `python paper/build.py` and an existing LaTeX installation.
- [Lean core](lean/README.md): what is checked, trust base and build commands.
- [Reproduction](REPRODUCE.md): requirements and commands.
- [Release notes](RELEASE-NOTES-v1.2.0.md), [rights](RIGHTS.md) and [notice](NOTICE).

The previous Lean 4.34.1 package and its 6 October 2026 rebuild evidence remain in the
[version 1.1.0 archive](https://doi.org/10.5281/zenodo.23374284); they are not shipped again.
The new core vendors the required OpenAI-derived and shared-library sources.

## Version 1.1.0

- New section "Division rings": for every division ring K of characteristic q, the group ring over K of G, or of any
  group containing G, has no Linnell division ring, no strongly Hughes-free division ring, and no epic division ring
  satisfying condition (HF); every Sylvester matrix rank function makes the line matrices collapse. OpenAI's
  characteristic-two refutations and the authors' companion note on Kaplansky's conjectures for torsion-free hyperbolic groups are credited up front.
- New structural results: G is the free product of a free group and a finitely presented torsion-free hyperbolic
  group G♯ such that no group containing G♯ has a Linnell division ring in characteristic q; no group containing G is bi-orderable; G and G♯ embed in no fundamental group of
  a two-complex with nonpositive immersions.
- The hyperlinearity discussion is upgraded to three results: a barrier for unitary models with bounded denominators,
  the group von Neumann algebra as a countermodel for tracial arguments, and a criterion for a hyperlinear quotient
  that is not sofic.
- Citation edits: Alon, Hall, Knauer, Pinchasi and Yuster (Theorem 6) for the real-rank step; Schauz and Serre for
  the interpolation and the vanishing line sums; exact result numbers in Elek and Szabó and in Pestov; Elek and Szabó's
  "On sofic groups" for closure properties; Nica for Malcev's theorem; the Sandhu–Thom note cited with its authors and
  link.
- New appendix listing earlier sources for the inputs taken from OpenAI's paper, a new open-questions section, and a
  section on how the work was done. The non-soficity argument and its Lean formalization are unchanged.

## Version 1.0.1

Attribution update; no mathematical change. The note now cites Chapman and Peled's conditional construction of a
non-sofic hyperbolic group (arXiv:2509.21566), Soulé's torsion bound (with Sauer's restatement) as a second source for
the rank-reduction lemma, and the independent note circulated by Andreas Thom, based on Harjas Sandhu's construction,
which gives an explicit non-sofic hyperbolic group and a torsion-free hyperbolic group with no nontrivial sofic quotient.

## Credit and license

The group, its construction and all imported theorems are OpenAI's: "A torsion-free hyperbolic group that is not
residually finite" (OpenAI Math Release, 23 September 2026) and its Lean development at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The core now redistributes the required sources, ported to Lean 4.35.0; the changes and original licence are retained under `lean/vendor/finite-lean/FiniteLean/GroupTheory/OAI/`.

The paper and documentation are licensed CC BY 4.0, the scripts MIT, and the Lean files Apache 2.0, since they
adapt parts of OpenAI's Apache-2.0 development; see [RIGHTS.md](RIGHTS.md) and [NOTICE](NOTICE). To cite this work, use
the concept DOI [10.5281/zenodo.23202474](https://doi.org/10.5281/zenodo.23202474), which covers all versions
(version 1.1.0: [10.5281/zenodo.23374284](https://doi.org/10.5281/zenodo.23374284); version 1.0.1: [10.5281/zenodo.23345877](https://doi.org/10.5281/zenodo.23345877); version 1.0.0: [10.5281/zenodo.23202475](https://doi.org/10.5281/zenodo.23202475)),
or see [CITATION.cff](CITATION.cff).
