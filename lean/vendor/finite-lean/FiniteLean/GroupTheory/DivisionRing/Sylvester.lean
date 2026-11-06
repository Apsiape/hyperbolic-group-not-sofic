import Mathlib.Data.Matrix.Block
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Sylvester matrix rank functions

Section 5 ("Division rings") of Douglas–Mghirbi, *Non-soficity of OpenAI's torsion-free
hyperbolic group*, v1.1.0, subsection "Rank collapse".

A *Sylvester matrix rank function* on a ring `R` assigns to every matrix `M` over `R` a real
number `rk M ≥ 0` with
* `rk M = 0` for zero matrices,
* `rk 1 = 1` (the `1 × 1` identity),
* `rk (M₁ M₂) ≤ min (rk M₁) (rk M₂)`,
* `rk (M₁ ⊕ M₂) = rk M₁ + rk M₂`,
* `rk M₁ + rk M₂ ≤ rk [[M₁, M₃], [0, M₂]]`.

## Encoding

Matrices are `Matrix (Fin m) (Fin n) R`.  The block matrix `[[A, B], [C, D]]` of a
`Fin m₁ ⊕ Fin m₂` by `Fin n₁ ⊕ Fin n₂` block decomposition is encoded as
`blockFin A B C D := (fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm`,
a `Fin (m₁ + m₂)` by `Fin (n₁ + n₂)` matrix whose first `m₁` rows / `n₁` columns are the first
block (`Fin.castAdd`) and whose last ones are the second block (`Fin.natAdd`).

Since every axiom is invariant under reindexing (proved below), we extend `rk` to matrices
indexed by arbitrary finite types (`SylvesterRankFunction.rkF`) and prove all derived lemmas
in that generality: subadditivity, the column / row bounds, `rk (-M) = rk M`, invariance under
reindexing, `rk (P Z Q) ≤ rk Z`, block-diagonal additivity (`Matrix.blockDiagonal` with
`Fin N` blocks), finite sums, and the Kronecker bound `rk (H ⊗ Z) ≤ rk Z` for `H = f fᵀ`
with central scalar entries.
-/

namespace NonSofic

open Matrix

section blockFin

variable {R : Type*}

/-- The block matrix `[[A, B], [C, D]]`, indexed by `Fin (m₁ + m₂)` and `Fin (n₁ + n₂)` via
`finSumFinEquiv`. -/
def blockFin {m₁ m₂ n₁ n₂ : ℕ} (A : Matrix (Fin m₁) (Fin n₁) R) (B : Matrix (Fin m₁) (Fin n₂) R)
    (C : Matrix (Fin m₂) (Fin n₁) R) (D : Matrix (Fin m₂) (Fin n₂) R) :
    Matrix (Fin (m₁ + m₂)) (Fin (n₁ + n₂)) R :=
  (fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

@[simp]
theorem blockFin_castAdd_castAdd {m₁ m₂ n₁ n₂ : ℕ} (A : Matrix (Fin m₁) (Fin n₁) R)
    (B : Matrix (Fin m₁) (Fin n₂) R) (C : Matrix (Fin m₂) (Fin n₁) R)
    (D : Matrix (Fin m₂) (Fin n₂) R) (i : Fin m₁) (j : Fin n₁) :
    blockFin A B C D (Fin.castAdd m₂ i) (Fin.castAdd n₂ j) = A i j := by
  simp [blockFin]

@[simp]
theorem blockFin_castAdd_natAdd {m₁ m₂ n₁ n₂ : ℕ} (A : Matrix (Fin m₁) (Fin n₁) R)
    (B : Matrix (Fin m₁) (Fin n₂) R) (C : Matrix (Fin m₂) (Fin n₁) R)
    (D : Matrix (Fin m₂) (Fin n₂) R) (i : Fin m₁) (j : Fin n₂) :
    blockFin A B C D (Fin.castAdd m₂ i) (Fin.natAdd n₁ j) = B i j := by
  simp [blockFin]

@[simp]
theorem blockFin_natAdd_castAdd {m₁ m₂ n₁ n₂ : ℕ} (A : Matrix (Fin m₁) (Fin n₁) R)
    (B : Matrix (Fin m₁) (Fin n₂) R) (C : Matrix (Fin m₂) (Fin n₁) R)
    (D : Matrix (Fin m₂) (Fin n₂) R) (i : Fin m₂) (j : Fin n₁) :
    blockFin A B C D (Fin.natAdd m₁ i) (Fin.castAdd n₂ j) = C i j := by
  simp [blockFin]

@[simp]
theorem blockFin_natAdd_natAdd {m₁ m₂ n₁ n₂ : ℕ} (A : Matrix (Fin m₁) (Fin n₁) R)
    (B : Matrix (Fin m₁) (Fin n₂) R) (C : Matrix (Fin m₂) (Fin n₁) R)
    (D : Matrix (Fin m₂) (Fin n₂) R) (i : Fin m₂) (j : Fin n₂) :
    blockFin A B C D (Fin.natAdd m₁ i) (Fin.natAdd n₁ j) = D i j := by
  simp [blockFin]

/-- `fromBlocks` commutes with reindexing each block. -/
theorem fromBlocks_submatrix_sumMap {α : Type*} {l m n o l' m' n' o' : Type*}
    (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α)
    (e₁ : n' → n) (e₂ : o' → o) (f₁ : l' → l) (f₂ : m' → m) :
    fromBlocks (A.submatrix e₁ f₁) (B.submatrix e₁ f₂) (C.submatrix e₂ f₁) (D.submatrix e₂ f₂) =
      (fromBlocks A B C D).submatrix (Sum.map e₁ e₂) (Sum.map f₁ f₂) := by
  ext (i | i) (j | j) <;> rfl

end blockFin

theorem zero_submatrix {α : Type*} [Zero α] {l m n o : Type*} (e : l → m) (f : o → n) :
    (0 : Matrix m n α).submatrix e f = 0 := rfl

/-- Any submatrix (along arbitrary maps of index sets) is a product `P * M * Q`. -/
theorem submatrix_eq_mul_mul {R : Type*} [Semiring R] {m n m' n' : Type*} [Fintype m]
    [Fintype n] [DecidableEq m] [DecidableEq n] (M : Matrix m n R) (e : m' → m) (f : n' → n) :
    M.submatrix e f =
      (1 : Matrix m m R).submatrix e id * M * (1 : Matrix n n R).submatrix id f := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, ite_mul, mul_ite, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

/-- A Sylvester matrix rank function on a ring `R` (paper, Section 5, after
[FSP2026, Section 2.5]). The block matrices are encoded with `blockFin`. -/
structure SylvesterRankFunction (R : Type*) [Ring R] where
  /-- The rank of a matrix. -/
  rk : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) R → ℝ
  /-- `rk M ≥ 0`. -/
  rk_nonneg' : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) R), 0 ≤ rk M
  /-- `rk 0 = 0` for zero matrices of every size. -/
  rk_zero' : ∀ {m n : ℕ}, rk (0 : Matrix (Fin m) (Fin n) R) = 0
  /-- `rk 1 = 1` for the `1 × 1` identity matrix (the paper's normalization `rk(1) = 1`);
  `rk_one_fin` derives `rk 1ₙ = n`. -/
  rk_one' : rk (1 : Matrix (Fin 1) (Fin 1) R) = 1
  /-- `rk (M₁ M₂) ≤ min (rk M₁) (rk M₂)`. -/
  rk_mul_le' : ∀ {m n p : ℕ} (M₁ : Matrix (Fin m) (Fin n) R) (M₂ : Matrix (Fin n) (Fin p) R),
    rk (M₁ * M₂) ≤ min (rk M₁) (rk M₂)
  /-- `rk (M₁ ⊕ M₂) = rk M₁ + rk M₂`. -/
  rk_blockDiag' : ∀ {m₁ n₁ m₂ n₂ : ℕ} (M₁ : Matrix (Fin m₁) (Fin n₁) R)
    (M₂ : Matrix (Fin m₂) (Fin n₂) R), rk (blockFin M₁ 0 0 M₂) = rk M₁ + rk M₂
  /-- `rk M₁ + rk M₂ ≤ rk [[M₁, M₃], [0, M₂]]`. -/
  rk_blockTri' : ∀ {m₁ n₁ m₂ n₂ : ℕ} (M₁ : Matrix (Fin m₁) (Fin n₁) R)
    (M₂ : Matrix (Fin m₂) (Fin n₂) R) (M₃ : Matrix (Fin m₁) (Fin n₂) R),
    rk M₁ + rk M₂ ≤ rk (blockFin M₁ M₃ 0 M₂)

namespace SylvesterRankFunction

variable {R : Type*} [Ring R] (ρ : SylvesterRankFunction R)

/-! ### Elementary consequences on `Fin`-indexed matrices -/

theorem rk_mul_le_left {m n p : ℕ} (M₁ : Matrix (Fin m) (Fin n) R)
    (M₂ : Matrix (Fin n) (Fin p) R) : ρ.rk (M₁ * M₂) ≤ ρ.rk M₁ :=
  (ρ.rk_mul_le' M₁ M₂).trans (min_le_left _ _)

theorem rk_mul_le_right {m n p : ℕ} (M₁ : Matrix (Fin m) (Fin n) R)
    (M₂ : Matrix (Fin n) (Fin p) R) : ρ.rk (M₁ * M₂) ≤ ρ.rk M₂ :=
  (ρ.rk_mul_le' M₁ M₂).trans (min_le_right _ _)

theorem rk_submatrix_le {m n m' n' : ℕ} (M : Matrix (Fin m) (Fin n) R) (e : Fin m' → Fin m)
    (f : Fin n' → Fin n) : ρ.rk (M.submatrix e f) ≤ ρ.rk M := by
  rw [submatrix_eq_mul_mul]
  exact (ρ.rk_mul_le_left _ _).trans (ρ.rk_mul_le_right _ _)

/-- Invariance under reindexing rows and columns by equivalences. -/
theorem rk_submatrix_equiv {m n m' n' : ℕ} (M : Matrix (Fin m) (Fin n) R) (e : Fin m' ≃ Fin m)
    (f : Fin n' ≃ Fin n) : ρ.rk (M.submatrix e f) = ρ.rk M := by
  refine le_antisymm (ρ.rk_submatrix_le M e f) ?_
  have h : M = (M.submatrix e f).submatrix e.symm f.symm := by
    simp [Matrix.submatrix_submatrix]
  conv_lhs => rw [h]
  exact ρ.rk_submatrix_le _ _ _

theorem rk_one_fin (n : ℕ) : ρ.rk (1 : Matrix (Fin n) (Fin n) R) = n := by
  induction n with
  | zero =>
    have h : (1 : Matrix (Fin 0) (Fin 0) R) = 0 := by ext i j; exact i.elim0
    rw [h, ρ.rk_zero']; simp
  | succ n ih =>
    have h : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
        blockFin (1 : Matrix (Fin n) (Fin n) R) 0 0 (1 : Matrix (Fin 1) (Fin 1) R) := by
      rw [blockFin, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
    rw [h, ρ.rk_blockDiag', ih, ρ.rk_one']
    simp

/-! ### Extension to matrices indexed by arbitrary finite types -/

/-- The rank of a matrix indexed by finite types, computed after reindexing to `Fin`. By
`rkF_eq` the choice of reindexing does not matter. -/
noncomputable def rkF {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ R) : ℝ := by
  classical
  exact ρ.rk (M.submatrix (Fintype.equivFin ι).symm (Fintype.equivFin κ).symm)

/-- The rank of a matrix reindexed to `Fin` does not depend on the reindexing. -/
theorem rk_submatrix_eq_of_equiv {ι κ : Type*} {a b a' b' : ℕ} (M : Matrix ι κ R)
    (e : Fin a ≃ ι) (f : Fin b ≃ κ) (e' : Fin a' ≃ ι) (f' : Fin b' ≃ κ) :
    ρ.rk (M.submatrix e f) = ρ.rk (M.submatrix e' f') := by
  have h : M.submatrix e f = (M.submatrix e' f').submatrix (e.trans e'.symm) (f.trans f'.symm) := by
    ext i j; simp
  rw [h, ρ.rk_submatrix_equiv]

theorem rkF_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {a b : ℕ} (M : Matrix ι κ R)
    (e : Fin a ≃ ι) (f : Fin b ≃ κ) : ρ.rkF M = ρ.rk (M.submatrix e f) := by
  unfold rkF
  exact ρ.rk_submatrix_eq_of_equiv M _ _ e f

@[simp]
theorem rkF_fin {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) : ρ.rkF M = ρ.rk M := by
  rw [ρ.rkF_eq M (Equiv.refl _) (Equiv.refl _)]
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id]

theorem rkF_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ R) : 0 ≤ ρ.rkF M := by
  classical
  rw [ρ.rkF_eq M (Fintype.equivFin ι).symm (Fintype.equivFin κ).symm]
  exact ρ.rk_nonneg' _

/-- Invariance of `rkF` under reindexing by equivalences. -/
theorem rkF_submatrix_equiv {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [Fintype κ'] (M : Matrix ι κ R) (e : ι' ≃ ι) (f : κ' ≃ κ) :
    ρ.rkF (M.submatrix e f) = ρ.rkF M := by
  classical
  rw [ρ.rkF_eq (M.submatrix e f) (Fintype.equivFin ι').symm (Fintype.equivFin κ').symm,
    ρ.rkF_eq M ((Fintype.equivFin ι').symm.trans e) ((Fintype.equivFin κ').symm.trans f)]
  rfl

theorem rkF_reindex {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [Fintype κ'] (M : Matrix ι κ R) (e : ι ≃ ι') (f : κ ≃ κ') :
    ρ.rkF (Matrix.reindex e f M) = ρ.rkF M :=
  ρ.rkF_submatrix_equiv M e.symm f.symm

@[simp]
theorem rkF_zero {ι κ : Type*} [Fintype ι] [Fintype κ] : ρ.rkF (0 : Matrix ι κ R) = 0 := by
  classical
  rw [ρ.rkF_eq _ (Fintype.equivFin ι).symm (Fintype.equivFin κ).symm, zero_submatrix]
  exact ρ.rk_zero'

theorem rkF_mul_le_left {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (M₁ : Matrix ι κ R) (M₂ : Matrix κ μ R) : ρ.rkF (M₁ * M₂) ≤ ρ.rkF M₁ := by
  classical
  set a := (Fintype.equivFin ι).symm
  set b := (Fintype.equivFin κ).symm
  set c := (Fintype.equivFin μ).symm
  rw [ρ.rkF_eq _ a c, ρ.rkF_eq _ a b, ← Matrix.submatrix_mul_equiv M₁ M₂ a b c]
  exact ρ.rk_mul_le_left _ _

theorem rkF_mul_le_right {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (M₁ : Matrix ι κ R) (M₂ : Matrix κ μ R) : ρ.rkF (M₁ * M₂) ≤ ρ.rkF M₂ := by
  classical
  set a := (Fintype.equivFin ι).symm
  set b := (Fintype.equivFin κ).symm
  set c := (Fintype.equivFin μ).symm
  rw [ρ.rkF_eq _ a c, ρ.rkF_eq _ b c, ← Matrix.submatrix_mul_equiv M₁ M₂ a b c]
  exact ρ.rk_mul_le_right _ _

theorem rkF_mul_le {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (M₁ : Matrix ι κ R) (M₂ : Matrix κ μ R) : ρ.rkF (M₁ * M₂) ≤ min (ρ.rkF M₁) (ρ.rkF M₂) :=
  le_min (ρ.rkF_mul_le_left M₁ M₂) (ρ.rkF_mul_le_right M₁ M₂)

/-- `rk (P Z Q) ≤ rk Z`. -/
theorem rkF_mul_mul_le {ι κ μ ν : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
    (P : Matrix ι κ R) (Z : Matrix κ μ R) (Q : Matrix μ ν R) : ρ.rkF (P * Z * Q) ≤ ρ.rkF Z :=
  (ρ.rkF_mul_le_left _ _).trans (ρ.rkF_mul_le_right _ _)

theorem rkF_submatrix_le {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (M : Matrix ι κ R) (e : ι' → ι) (f : κ' → κ) : ρ.rkF (M.submatrix e f) ≤ ρ.rkF M := by
  classical
  rw [submatrix_eq_mul_mul]
  exact ρ.rkF_mul_mul_le _ _ _

theorem rkF_fromBlocks_eq {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype κ₁]
    [Fintype κ₂] {a₁ a₂ b₁ b₂ : ℕ} (A : Matrix ι₁ κ₁ R) (B : Matrix ι₁ κ₂ R)
    (C : Matrix ι₂ κ₁ R) (D : Matrix ι₂ κ₂ R) (e₁ : Fin a₁ ≃ ι₁) (e₂ : Fin a₂ ≃ ι₂)
    (f₁ : Fin b₁ ≃ κ₁) (f₂ : Fin b₂ ≃ κ₂) :
    ρ.rkF (fromBlocks A B C D) =
      ρ.rk (blockFin (A.submatrix e₁ f₁) (B.submatrix e₁ f₂) (C.submatrix e₂ f₁)
        (D.submatrix e₂ f₂)) := by
  rw [ρ.rkF_eq _ (finSumFinEquiv.symm.trans (Equiv.sumCongr e₁ e₂))
    (finSumFinEquiv.symm.trans (Equiv.sumCongr f₁ f₂)), blockFin, fromBlocks_submatrix_sumMap,
    Matrix.submatrix_submatrix]
  rfl

/-- `rk (M₁ ⊕ M₂) = rk M₁ + rk M₂` for blocks indexed by arbitrary finite types. -/
theorem rkF_fromBlocks_diag {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype κ₁]
    [Fintype κ₂] (M₁ : Matrix ι₁ κ₁ R) (M₂ : Matrix ι₂ κ₂ R) :
    ρ.rkF (fromBlocks M₁ 0 0 M₂) = ρ.rkF M₁ + ρ.rkF M₂ := by
  classical
  rw [ρ.rkF_fromBlocks_eq _ _ _ _ (Fintype.equivFin ι₁).symm (Fintype.equivFin ι₂).symm
    (Fintype.equivFin κ₁).symm (Fintype.equivFin κ₂).symm, zero_submatrix,
    zero_submatrix, ρ.rk_blockDiag', ← ρ.rkF_eq, ← ρ.rkF_eq]

/-- `rk M₁ + rk M₂ ≤ rk [[M₁, M₃], [0, M₂]]` for arbitrary finite index types. -/
theorem rkF_fromBlocks_tri {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype κ₁]
    [Fintype κ₂] (M₁ : Matrix ι₁ κ₁ R) (M₂ : Matrix ι₂ κ₂ R) (M₃ : Matrix ι₁ κ₂ R) :
    ρ.rkF M₁ + ρ.rkF M₂ ≤ ρ.rkF (fromBlocks M₁ M₃ 0 M₂) := by
  classical
  rw [ρ.rkF_fromBlocks_eq _ _ _ _ (Fintype.equivFin ι₁).symm (Fintype.equivFin ι₂).symm
    (Fintype.equivFin κ₁).symm (Fintype.equivFin κ₂).symm, zero_submatrix,
    ρ.rkF_eq M₁ (Fintype.equivFin ι₁).symm (Fintype.equivFin κ₁).symm,
    ρ.rkF_eq M₂ (Fintype.equivFin ι₂).symm (Fintype.equivFin κ₂).symm]
  exact ρ.rk_blockTri' _ _ _

/-- `rk (Iₙ) = n`. -/
@[simp]
theorem rkF_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ρ.rkF (1 : Matrix ι ι R) = Fintype.card ι := by
  rw [ρ.rkF_eq _ (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm,
    Matrix.submatrix_one_equiv, ρ.rk_one_fin]

/-- `rk M ≤` the number of columns. -/
theorem rkF_le_card_cols {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ R) :
    ρ.rkF M ≤ Fintype.card κ := by
  classical
  have h := ρ.rkF_mul_le_right M (1 : Matrix κ κ R)
  rwa [Matrix.mul_one, ρ.rkF_one] at h

/-- `rk M ≤` the number of rows. -/
theorem rkF_le_card_rows {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ R) :
    ρ.rkF M ≤ Fintype.card ι := by
  classical
  have h := ρ.rkF_mul_le_left (1 : Matrix ι ι R) M
  rwa [Matrix.one_mul, ρ.rkF_one] at h

/-- `rk (M₁ + M₂) ≤ rk M₁ + rk M₂`, via `M₁ + M₂ = (I I) (M₁ ⊕ M₂) (I I)ᵀ`. -/
theorem rkF_add_le {ι κ : Type*} [Fintype ι] [Fintype κ] (M₁ M₂ : Matrix ι κ R) :
    ρ.rkF (M₁ + M₂) ≤ ρ.rkF M₁ + ρ.rkF M₂ := by
  classical
  let P : Matrix ι (ι ⊕ ι) R := Matrix.of fun i j => Sum.elim (fun k => (1 : Matrix ι ι R) i k)
    (fun k => (1 : Matrix ι ι R) i k) j
  let Q : Matrix (κ ⊕ κ) κ R := Matrix.of fun a j => Sum.elim (fun k => (1 : Matrix κ κ R) k j)
    (fun k => (1 : Matrix κ κ R) k j) a
  have h : M₁ + M₂ = P * fromBlocks M₁ 0 0 M₂ * Q := by
    ext i j
    simp [P, Q, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, ite_mul,
      mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [h, ← ρ.rkF_fromBlocks_diag]
  exact ρ.rkF_mul_mul_le _ _ _

theorem rkF_neg_le {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ R) :
    ρ.rkF (-M) ≤ ρ.rkF M := by
  classical
  have h : -M = (-1 : Matrix ι ι R) * M := by rw [Matrix.neg_mul, Matrix.one_mul]
  rw [h]
  exact ρ.rkF_mul_le_right _ _

/-- `rk (-M) = rk M`. -/
@[simp]
theorem rkF_neg {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ R) :
    ρ.rkF (-M) = ρ.rkF M := by
  refine le_antisymm (ρ.rkF_neg_le M) ?_
  have h := ρ.rkF_neg_le (-M)
  rwa [neg_neg] at h

/-- The rank of a finite sum is at most the sum of the ranks. -/
theorem rkF_sum_le {α ι κ : Type*} [Fintype ι] [Fintype κ] (s : Finset α)
    (M : α → Matrix ι κ R) : ρ.rkF (∑ a ∈ s, M a) ≤ ∑ a ∈ s, ρ.rkF (M a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ρ.rkF_add_le _ _).trans (add_le_add le_rfl ih)

/-- Block-diagonal matrices with `N` blocks: the rank is the sum of the ranks of the blocks. -/
theorem rkF_blockDiagonal {m n : Type*} [Fintype m] [Fintype n] :
    ∀ {N : ℕ} (M : Fin N → Matrix m n R),
      ρ.rkF (Matrix.blockDiagonal M) = ∑ i, ρ.rkF (M i)
  | 0, M => by
    have h : Matrix.blockDiagonal M = 0 := by
      ext ⟨_, k⟩; exact k.elim0
    rw [h]; simp
  | N + 1, M => by
    classical
    let e : m × Fin N ⊕ m ≃ m × Fin (N + 1) :=
      (Equiv.sumCongr (Equiv.refl _) (Equiv.prodUnique m (Fin 1)).symm).trans
        ((Equiv.prodSumDistrib m (Fin N) (Fin 1)).symm.trans
          (Equiv.prodCongr (Equiv.refl m) finSumFinEquiv))
    let f : n × Fin N ⊕ n ≃ n × Fin (N + 1) :=
      (Equiv.sumCongr (Equiv.refl _) (Equiv.prodUnique n (Fin 1)).symm).trans
        ((Equiv.prodSumDistrib n (Fin N) (Fin 1)).symm.trans
          (Equiv.prodCongr (Equiv.refl n) finSumFinEquiv))
    have hne : ∀ k : Fin N, Fin.castAdd 1 k ≠ Fin.natAdd N 0 := by
      intro k hk
      have := congrArg Fin.val hk
      simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero, add_zero] at this
      exact absurd this (Nat.ne_of_lt k.isLt)
    have h : (Matrix.blockDiagonal M).submatrix e f =
        fromBlocks (Matrix.blockDiagonal fun i : Fin N => M (Fin.castAdd 1 i)) 0 0
          (M (Fin.natAdd N 0)) := by
      ext (⟨i, k⟩ | i) (⟨j, k'⟩ | j)
      · simp [e, f, Matrix.blockDiagonal_apply]
      · simp [e, f, Matrix.blockDiagonal_apply, hne]
      · simp [e, f, Matrix.blockDiagonal_apply, (hne _).symm]
      · simp [e, f, Matrix.blockDiagonal_apply]
    rw [← ρ.rkF_submatrix_equiv _ e f, h, ρ.rkF_fromBlocks_diag,
      rkF_blockDiagonal (fun i : Fin N => M (Fin.castAdd 1 i)), Fin.sum_univ_castSucc]
    rfl

/-- Block-diagonal matrices with blocks indexed by any finite type: the rank is the sum of the
ranks of the blocks. -/
theorem rkF_blockDiagonal' {m n o : Type*} [Fintype m] [Fintype n] [Fintype o] [DecidableEq o]
    (M : o → Matrix m n R) : ρ.rkF (Matrix.blockDiagonal M) = ∑ k, ρ.rkF (M k) := by
  set e : Fin (Fintype.card o) ≃ o := (Fintype.equivFin o).symm
  have h : (Matrix.blockDiagonal M).submatrix (Equiv.prodCongr (Equiv.refl m) e)
      (Equiv.prodCongr (Equiv.refl n) e) = Matrix.blockDiagonal (fun i => M (e i)) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp [Matrix.blockDiagonal_apply, e.injective.eq_iff]
  rw [← ρ.rkF_submatrix_equiv _ (Equiv.prodCongr (Equiv.refl m) e)
    (Equiv.prodCongr (Equiv.refl n) e), h, ρ.rkF_blockDiagonal]
  exact Equiv.sum_comp e (fun k => ρ.rkF (M k))

/-! ### Kronecker products with central scalar matrices -/

/-- The Kronecker product `(f fᵀ) ⊗ Z` of the rank-one matrix `f fᵀ` (entries in a ring `S`
mapped to `R` by `ι`) with `Z`, indexed by `o × m` and `o × n` as in `Matrix.kroneckerMap`:
the entry at `((i, k), (j, l))` is `ι (f i * f j) * Z k l`. -/
def kronOuter {S : Type*} [Semiring S] {o m n : Type*} (ι : S →+* R) (f : o → S)
    (Z : Matrix m n R) : Matrix (o × m) (o × n) R :=
  Matrix.of fun p q => ι (f p.1 * f q.1) * Z p.2 q.2

/-- `(f fᵀ) ⊗ Z = (f ⊗ I) Z (fᵀ ⊗ I)` when `ι` has central image. -/
theorem kronOuter_eq_mul_mul {S : Type*} [Semiring S] {o m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ι : S →+* R) (hι : ∀ (s : S) (x : R), ι s * x = x * ι s)
    (f : o → S) (Z : Matrix m n R) :
    kronOuter ι f Z =
      (Matrix.of fun (p : o × m) (k : m) => if p.2 = k then ι (f p.1) else 0) * Z *
        (Matrix.of fun (l : n) (q : o × n) => if l = q.2 then ι (f q.1) else 0) := by
  ext p q
  simp only [kronOuter, Matrix.of_apply, Matrix.mul_apply, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [map_mul, mul_assoc, mul_assoc, hι (f q.1) (Z p.2 q.2)]

/-- The Kronecker bound `rk ((f fᵀ) ⊗ Z) ≤ rk Z` (paper, proof of Theorem `thm:collapse`). -/
theorem rkF_kronOuter_le {S : Type*} [Semiring S] {o m n : Type*} [Fintype o] [Fintype m]
    [Fintype n] (ι : S →+* R) (hι : ∀ (s : S) (x : R), ι s * x = x * ι s) (f : o → S)
    (Z : Matrix m n R) : ρ.rkF (kronOuter ι f Z) ≤ ρ.rkF Z := by
  classical
  rw [kronOuter_eq_mul_mul ι hι f Z]
  exact ρ.rkF_mul_mul_le _ _ _

/-- The block-diagonal matrix `⊕ᵢ Yᵢ` with the block index first (matching `kronOuter`). -/
def blockDiagFst {o m n : Type*} [DecidableEq o] (Y : o → Matrix m n R) :
    Matrix (o × m) (o × n) R :=
  (Matrix.blockDiagonal Y).submatrix Prod.swap Prod.swap

theorem rkF_blockDiagFst {N : ℕ} {m n : Type*} [Fintype m] [Fintype n]
    (Y : Fin N → Matrix m n R) : ρ.rkF (blockDiagFst Y) = ∑ i, ρ.rkF (Y i) := by
  rw [blockDiagFst, ← ρ.rkF_blockDiagonal Y]
  exact ρ.rkF_submatrix_equiv _ (Equiv.prodComm _ _) (Equiv.prodComm _ _)

/-- The rank count in the proof of Theorem `thm:collapse`, abstracted: if
`-⊕ᵢ Yᵢ = Σ_z (f_z f_zᵀ) ⊗ Z_z` with central scalars, then `Σᵢ rk Yᵢ ≤ Σ_z rk Z_z`. -/
theorem sum_rkF_le_of_certificate {S : Type*} [Semiring S] {N : ℕ} {m n P : Type*} [Fintype m]
    [Fintype n] (ι : S →+* R) (hι : ∀ (s : S) (x : R), ι s * x = x * ι s)
    (Y : Fin N → Matrix m n R) (s : Finset P) (f : P → Fin N → S) (Z : P → Matrix m n R)
    (hcert : -blockDiagFst Y = ∑ z ∈ s, kronOuter ι (f z) (Z z)) :
    ∑ i, ρ.rkF (Y i) ≤ ∑ z ∈ s, ρ.rkF (Z z) := by
  rw [← ρ.rkF_blockDiagFst, ← ρ.rkF_neg, hcert]
  exact (ρ.rkF_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ρ.rkF_kronOuter_le ι hι _ _)

/-! ### `Fin`-indexed forms of the derived lemmas -/

theorem rk_add_le {m n : ℕ} (M₁ M₂ : Matrix (Fin m) (Fin n) R) :
    ρ.rk (M₁ + M₂) ≤ ρ.rk M₁ + ρ.rk M₂ := by
  have h := ρ.rkF_add_le M₁ M₂
  simp only [rkF_fin] at h
  exact h

theorem rk_neg {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) : ρ.rk (-M) = ρ.rk M := by
  have h := ρ.rkF_neg M
  simp only [rkF_fin] at h
  exact h

theorem rk_le_cols {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) : ρ.rk M ≤ n := by
  have h := ρ.rkF_le_card_cols M
  simp only [rkF_fin, Fintype.card_fin] at h
  exact h

theorem rk_le_rows {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) : ρ.rk M ≤ m := by
  have h := ρ.rkF_le_card_rows M
  simp only [rkF_fin, Fintype.card_fin] at h
  exact h

theorem rk_mul_mul_le {m n p q : ℕ} (P : Matrix (Fin m) (Fin n) R) (Z : Matrix (Fin n) (Fin p) R)
    (Q : Matrix (Fin p) (Fin q) R) : ρ.rk (P * Z * Q) ≤ ρ.rk Z := by
  have h := ρ.rkF_mul_mul_le P Z Q
  simp only [rkF_fin] at h
  exact h

theorem rk_sum_le {α : Type*} {m n : ℕ} (s : Finset α) (M : α → Matrix (Fin m) (Fin n) R) :
    ρ.rk (∑ a ∈ s, M a) ≤ ∑ a ∈ s, ρ.rk (M a) := by
  have h := ρ.rkF_sum_le s M
  simp only [rkF_fin] at h
  exact h

/-- The block-diagonal matrix with `N` blocks of size `r × r`, reindexed to `Fin (N * r)` via
`finProdFinEquiv` (block index first). -/
def blockDiagFin {N r : ℕ} (Y : Fin N → Matrix (Fin r) (Fin r) R) :
    Matrix (Fin (N * r)) (Fin (N * r)) R :=
  (blockDiagFst Y).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

theorem rk_blockDiagFin {N r : ℕ} (Y : Fin N → Matrix (Fin r) (Fin r) R) :
    ρ.rk (blockDiagFin Y) = ∑ i, ρ.rk (Y i) := by
  rw [← ρ.rkF_fin, blockDiagFin, ρ.rkF_submatrix_equiv, ρ.rkF_blockDiagFst]
  simp

/-- The Kronecker product `(f fᵀ) ⊗ Z` reindexed to `Fin (N * r)` by `finProdFinEquiv`
(block index first, as in `blockDiagFin`). -/
def kronOuterFin {S : Type*} [Semiring S] (ι : S →+* R) {N r c : ℕ} (f : Fin N → S)
    (Z : Matrix (Fin r) (Fin c) R) : Matrix (Fin (N * r)) (Fin (N * c)) R :=
  (kronOuter ι f Z).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

theorem kronOuterFin_apply {S : Type*} [Semiring S] (ι : S →+* R) {N r c : ℕ} (f : Fin N → S)
    (Z : Matrix (Fin r) (Fin c) R) (i j : Fin N) (k : Fin r) (l : Fin c) :
    kronOuterFin ι f Z (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) =
      ι (f i * f j) * Z k l := by
  simp [kronOuterFin, kronOuter]

/-- The Kronecker bound in `Fin` form: `rk ((f fᵀ) ⊗ Z) ≤ rk Z`. -/
theorem rk_kronOuterFin_le {S : Type*} [Semiring S] (ι : S →+* R)
    (hι : ∀ (s : S) (x : R), ι s * x = x * ι s) {N r c : ℕ} (f : Fin N → S)
    (Z : Matrix (Fin r) (Fin c) R) : ρ.rk (kronOuterFin ι f Z) ≤ ρ.rk Z := by
  have h := ρ.rkF_kronOuter_le ι hι f Z
  rw [← ρ.rkF_submatrix_equiv (kronOuter ι f Z) finProdFinEquiv.symm finProdFinEquiv.symm,
    rkF_fin, rkF_fin] at h
  exact h

/-- The rank count of Theorem `thm:collapse` in `Fin` form: if
`-⊕ᵢ Yᵢ = Σ_{z ∈ s} (f_z f_zᵀ) ⊗ Z_z` (central scalars), then `Σᵢ rk Yᵢ ≤ Σ_{z ∈ s} rk Z_z`. -/
theorem sum_rk_le_of_certificate {S : Type*} [Semiring S] (ι : S →+* R)
    (hι : ∀ (s : S) (x : R), ι s * x = x * ι s) {N r : ℕ} {Q : Type*} (s : Finset Q)
    (Y : Fin N → Matrix (Fin r) (Fin r) R) (f : Q → Fin N → S)
    (Z : Q → Matrix (Fin r) (Fin r) R)
    (hcert : -blockDiagFin Y = ∑ z ∈ s, kronOuterFin ι (f z) (Z z)) :
    ∑ i, ρ.rk (Y i) ≤ ∑ z ∈ s, ρ.rk (Z z) := by
  rw [← ρ.rk_blockDiagFin, ← ρ.rk_neg, hcert]
  exact (ρ.rk_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ρ.rk_kronOuterFin_le ι hι _ _)

end SylvesterRankFunction

end NonSofic
