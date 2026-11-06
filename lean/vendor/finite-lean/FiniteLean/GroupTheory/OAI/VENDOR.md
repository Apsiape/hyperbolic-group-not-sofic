# Vendored sources

`FiniteLean/GroupTheory/OAI/GroupTheory/Hyperbolic/*.lean` are vendored from https://github.com/openai/math at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` (Apache-2.0, see `LICENSE-openai-math`), the commit pinned by
"Non-soficity of OpenAI's torsion-free hyperbolic group" v1.1.0 (`REPRODUCE.md`).

Port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679: the only intended change is replacing
`import Mathlib` in `Model.lean` by explicit Mathlib imports.
Any further change made for the port is listed below.

## Port changes

1. `Model.lean`: `import Mathlib` replaced by 184 explicit Mathlib imports (the import closure of the 29 modules'
   identifiers, plus tactic modules), including `Combinatorics.SimpleGraph.Metric` (`SimpleGraph.dist`),
   `Combinatorics.SimpleGraph.Coloring.Constructions`, `Analysis.InnerProductSpace.Orientation`,
   `Analysis.Matrix.Spectrum`, `Data.Real.StarOrdered`. No proof change.
2. Mathlib API change: `CategoryTheory.End X` is now a structure (`End.of`, `.asHom`) instead of `X ⟶ X`.
   - `WordPaths.lean`: `basedEdge` wraps morphisms with `End.of`; `fromFundamentalGroup` uses `.asHom`;
     `apply End.ext` after `MulOpposite.unop_injective` (6 places); `congrArg MulOpposite.unop` becomes
     `congrArg (fun x => (MulOpposite.unop x).asHom)` (1 place).
   - `BasedWords.lean`: `apply End.ext` after `MulOpposite.unop_injective` (5 places); same `congrArg` change (1 place).
3. Mathlib API change: `Rep.norm` is now an `End`; `CyclicAction.lean:118` uses `.norm.asHom.hom`.

No statement of any theorem or definition was changed. The four ported files can be compared with the originals at
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/Hyperbolic/.
