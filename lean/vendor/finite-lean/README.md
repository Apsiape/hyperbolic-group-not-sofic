# Shared-library source subset

This directory contains the group-theory modules listed in `../../LIBRARY-MODULES.txt`,
including the ported OpenAI development and its licence and `VENDOR.md`. It is the
transitive source subset needed by this paper, rather than the whole FiniteLean library.
Build it through the paper's `lean/` package as described in `../../README.md`.

The following is the scope of the full shared-library snapshot.
The entropy modules described here are not part of this paper's retained import closure.

The entropy results in this snapshot are finite dimensional. `QIT.mlog`, `QIT.relEnt` and `Houghton.vN` use natural logarithms (nats). The relative-entropy conjugation, joint-convexity and partial-trace theorems have the positive-definiteness assumptions shown by their types; extended-valued relative entropy for arbitrary singular states is outside this snapshot. Strong subadditivity is proved for all finite Hermitian positive-semidefinite trace-one density matrices. `QIT.integralRep` proves the `IntegralRep` interface; `relEnt_jointlyConvex_of` retains that interface as an explicit, internally dischargeable premise. The two compatibility bridges preserve the retained finite-matrix definitions exactly. No infinite-dimensional operator-entropy bridge is claimed.

## Build requirements

The commands fetch the pinned dependencies with Git.

Run from the paper's `lean/` directory with `LEAN_NUM_THREADS=1`:

```sh
lake exe cache get
lake build
lake env lean -j1 -M6144 Audit.lean
```
