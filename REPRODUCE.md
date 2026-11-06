# Reproducing version 1.2.0

## Manuscript

Use an existing LaTeX installation with the packages named in `paper/paper.tex` and
Python 3. From the repository root run:

```sh
python paper/build.py
```

The script runs three bounded pdflatex passes, writes `paper/build/` and refreshes
`paper/paper.pdf`. It rejects warnings, undefined references and overfull/underfull boxes.
No software is installed by the script.

## Lean core

Use Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`,
as pinned in `lean/lean-toolchain`, `lean/lake-manifest.json` and `lean/UPSTREAM-PINS.json`.

The commands fetch the pinned dependencies with Git, so Git must be available.

From `lean/` run:

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake build
lake env lean -j1 -M6144 Audit.lean
```

For PowerShell the first line is `$env:LEAN_NUM_THREADS = '1'`. Keep one compiler job
active at a time and at least 4 GiB of free memory. `Audit.lean` prints the type of each
checked declaration followed by its axioms; the axiom lines match `lean/AXIOMS.txt`.
The [Lean README](lean/README.md) states what is checked and what is not formalized.

## Integrity

Check `SHA256SUMS` at the repository root and `lean/SHA256SUMS` against the shipped
bytes with a SHA-256 implementation. `.gitattributes` disables text conversion so
these bytes and pins are preserved. The certified manifest and toolchain retain their
original CRLF line endings; other shipped text uses LF.

The version 1.0 Lean package (Lean 4.34.1) and its 6 October 2026 rebuild evidence are
available in the [version 1.1.0 archive](https://doi.org/10.5281/zenodo.23374284).
