import Lake
open Lake DSL
package FiniteLean where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"
lean_lib FiniteLean where
  srcDir := "vendor/finite-lean"
  globs := #[.submodules `FiniteLean]
lean_lib Approx252 where
  globs := #[.andSubmodules `Approx252]
lean_lib NonSofic where
  globs := #[.andSubmodules `NonSofic]
@[default_target]
lean_lib PaperCore where
  roots := #[`Statements, `Proofs, `Audit]
