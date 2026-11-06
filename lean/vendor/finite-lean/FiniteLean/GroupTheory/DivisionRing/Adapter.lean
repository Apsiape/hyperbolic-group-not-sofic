import FiniteLean.GroupTheory.DivisionRing.RankD
import FiniteLean.GroupTheory.RankCertificate

/-!
# Adapter: Sylvester rank functions are `RankFn`s

Every `SylvesterRankFunction R` (the paper's axioms, on `Fin`-indexed matrices) gives a
`RankFn R` (the interface used by `thm:collapse` in `NonSofic.CollapseCore`), with
`rk M := ρ.rkF M`, the rank after reindexing along `Fintype.equivFin`.
-/

namespace NonSofic

variable {R : Type*} [Ring R]

/-- Every Sylvester matrix rank function is a `RankFn`. -/
noncomputable def SylvesterRankFunction.toRankFn (ρ : SylvesterRankFunction R) : RankFn R where
  rk M := ρ.rkF M
  add_le A B := ρ.rkF_add_le A B
  mul_le_left A B := ρ.rkF_mul_le_left A B
  mul_le_right A B := ρ.rkF_mul_le_right A B
  le_card_width A := ρ.rkF_le_card_cols A
  sum_le_blockDiagonal Y := (ρ.rkF_blockDiagonal' Y).ge

@[simp]
theorem SylvesterRankFunction.toRankFn_rk (ρ : SylvesterRankFunction R) {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (M : Matrix m n R) :
    ρ.toRankFn.rk M = ρ.rkF M := rfl

theorem SylvesterRankFunction.toRankFn_rk_fin (ρ : SylvesterRankFunction R) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) R) : ρ.toRankFn.rk M = ρ.rk M :=
  ρ.rkF_fin M

/-- For `φ : R → D`, the `RankFn` of `M ↦ rank_D φ(M)`. -/
theorem rankFun_toRankFn_rk {D : Type*} [DivisionRing D] (φ : R →+* D) {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (M : Matrix m n R) :
    (rankFun φ).toRankFn.rk M = rankD (M.map φ) :=
  rankFun_rkF φ M

end NonSofic
