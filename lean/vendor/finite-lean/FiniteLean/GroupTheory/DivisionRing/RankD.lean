import FiniteLean.GroupTheory.DivisionRing.Sylvester
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The rank over a division ring is a Sylvester matrix rank function

For a division ring `D` (not necessarily commutative), the *left row rank* of a matrix
`M : Matrix m n D` is the dimension of the left `D`-subspace of `n → D` spanned by its rows,
i.e. the `finrank` of the range of the left-`D`-linear map `x ↦ x ᵥ* M`.  We do not use
`Matrix.rank` (which needs a commutative ring).

Main results:
* `rankDRankFunction D`: `M ↦ (rankD M : ℝ)` is a `SylvesterRankFunction D`;
* `rankD_eq_card_of_isUnit`: an invertible `n × n` matrix has rank `n`;
* `SylvesterRankFunction.comap`: pullback of a Sylvester rank function along a ring
  homomorphism; `rankFun φ` is the rank function `M ↦ rank_D φ(M)` of the paper;
* `isUnit_of_vecMul_eq_zero`, `isUnit_of_mulVec_eq_zero`: a square matrix over a division ring
  whose rows are left independent (resp. columns right independent) is invertible.
-/

namespace NonSofic

open Matrix Module

section rankD

variable {D : Type*} [DivisionRing D]

/-- The left row rank of a matrix over a division ring: the dimension of the left
`D`-span of its rows, `finrank D (range (x ↦ x ᵥ* M))`. -/
noncomputable def rankD {m n : Type*} [Fintype m] (M : Matrix m n D) : ℕ :=
  Module.finrank D (LinearMap.range M.vecMulLinear)

theorem vecMulLinear_mul {l m n : Type*} [Fintype l] [Fintype m] (M₁ : Matrix l m D)
    (M₂ : Matrix m n D) : (M₁ * M₂).vecMulLinear = M₂.vecMulLinear ∘ₗ M₁.vecMulLinear :=
  LinearMap.ext fun x => by simp [Matrix.vecMul_vecMul]

theorem rankD_mul_le_left {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    (M₁ : Matrix l m D) (M₂ : Matrix m n D) : rankD (M₁ * M₂) ≤ rankD M₁ := by
  unfold rankD
  rw [vecMulLinear_mul, LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

theorem rankD_mul_le_right {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    (M₁ : Matrix l m D) (M₂ : Matrix m n D) : rankD (M₁ * M₂) ≤ rankD M₂ := by
  unfold rankD
  rw [vecMulLinear_mul]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

@[simp]
theorem rankD_zero {m n : Type*} [Fintype m] [Fintype n] : rankD (0 : Matrix m n D) = 0 := by
  have h : (0 : Matrix m n D).vecMulLinear = 0 := LinearMap.ext fun x => by simp
  rw [rankD, h, LinearMap.range_zero, finrank_bot]

/-- An invertible square matrix has full rank. -/
theorem rankD_eq_card_of_isUnit {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n D}
    (hM : IsUnit M) : rankD M = Fintype.card n := by
  obtain ⟨u, rfl⟩ := hM
  have h : LinearMap.range (u : Matrix n n D).vecMulLinear = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨y ᵥ* (↑u⁻¹ : Matrix n n D), ?_⟩
    simp [Matrix.vecMul_vecMul]
  rw [rankD, h, finrank_top, Module.finrank_fintype_fun_eq_card]

/-- An invertible `n × n` matrix (indexed by `Fin n`) has rank `n`. -/
theorem rankD_eq_of_isUnit {n : ℕ} {M : Matrix (Fin n) (Fin n) D} (hM : IsUnit M) :
    rankD M = n := by
  rw [rankD_eq_card_of_isUnit hM, Fintype.card_fin]

@[simp]
theorem rankD_one {n : Type*} [Fintype n] [DecidableEq n] :
    rankD (1 : Matrix n n D) = Fintype.card n :=
  rankD_eq_card_of_isUnit isUnit_one

theorem rankD_submatrix_le {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m']
    [Fintype n'] (M : Matrix m n D) (e : m' → m) (f : n' → n) :
    rankD (M.submatrix e f) ≤ rankD M := by
  classical
  rw [submatrix_eq_mul_mul]
  exact (rankD_mul_le_left _ _).trans (rankD_mul_le_right _ _)

theorem rankD_submatrix_equiv {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m']
    [Fintype n'] (M : Matrix m n D) (e : m' ≃ m) (f : n' ≃ n) :
    rankD (M.submatrix e f) = rankD M := by
  refine le_antisymm (rankD_submatrix_le M e f) ?_
  have h : M = (M.submatrix e f).submatrix e.symm f.symm := by
    simp [Matrix.submatrix_submatrix]
  conv_lhs => rw [h]
  exact rankD_submatrix_le _ _ _

/-- `y ↦ Sum.elim y 0`. -/
def sumInlL (n₁ n₂ : Type*) : (n₁ → D) →ₗ[D] (n₁ ⊕ n₂ → D) where
  toFun y := Sum.elim y 0
  map_add' a b := by ext (i | i) <;> simp
  map_smul' c a := by ext (i | i) <;> simp

/-- `y ↦ Sum.elim 0 y`. -/
def sumInrL (n₁ n₂ : Type*) : (n₂ → D) →ₗ[D] (n₁ ⊕ n₂ → D) where
  toFun y := Sum.elim 0 y
  map_add' a b := by ext (i | i) <;> simp
  map_smul' c a := by ext (i | i) <;> simp

/-- `y ↦ y ∘ Sum.inl`. -/
def sumProjL (n₁ n₂ : Type*) : (n₁ ⊕ n₂ → D) →ₗ[D] (n₁ → D) where
  toFun y := y ∘ Sum.inl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sumInrL_injective (n₁ n₂ : Type*) : Function.Injective (sumInrL (D := D) n₁ n₂) := by
  intro a b h
  funext i
  have := congrFun h (Sum.inr i)
  simpa [sumInrL] using this

theorem rankD_fromBlocks_diag_le {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Fintype n₁]
    [Fintype n₂] (M₁ : Matrix m₁ n₁ D) (M₂ : Matrix m₂ n₂ D) :
    rankD (fromBlocks M₁ 0 0 M₂) ≤ rankD M₁ + rankD M₂ := by
  unfold rankD
  set R₁ := LinearMap.range M₁.vecMulLinear
  set R₂ := LinearMap.range M₂.vecMulLinear
  have hle : LinearMap.range (fromBlocks M₁ 0 0 M₂).vecMulLinear ≤
      R₁.map (sumInlL n₁ n₂) ⊔ R₂.map (sumInrL n₁ n₂) := by
    rintro _ ⟨x, rfl⟩
    have hx : (fromBlocks M₁ 0 0 M₂).vecMulLinear x =
        sumInlL n₁ n₂ ((x ∘ Sum.inl) ᵥ* M₁) + sumInrL n₁ n₂ ((x ∘ Sum.inr) ᵥ* M₂) := by
      rw [Matrix.vecMulLinear_apply, Matrix.vecMul_fromBlocks]
      ext (i | i) <;> simp [sumInlL, sumInrL]
    rw [hx]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem (LinearMap.mem_range_self _ _))
      (Submodule.mem_map_of_mem (LinearMap.mem_range_self _ _))
  calc finrank D (LinearMap.range (fromBlocks M₁ 0 0 M₂).vecMulLinear)
      ≤ finrank D ↥(R₁.map (sumInlL n₁ n₂) ⊔ R₂.map (sumInrL n₁ n₂)) :=
        Submodule.finrank_mono hle
    _ ≤ finrank D ↥(R₁.map (sumInlL n₁ n₂)) + finrank D ↥(R₂.map (sumInrL n₁ n₂)) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ finrank D R₁ + finrank D R₂ :=
        add_le_add (Submodule.finrank_map_le _ _) (Submodule.finrank_map_le _ _)

theorem rankD_fromBlocks_tri {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Fintype n₁]
    [Fintype n₂] (M₁ : Matrix m₁ n₁ D) (M₂ : Matrix m₂ n₂ D) (M₃ : Matrix m₁ n₂ D) :
    rankD M₁ + rankD M₂ ≤ rankD (fromBlocks M₁ M₃ 0 M₂) := by
  unfold rankD
  set B := fromBlocks M₁ M₃ 0 M₂
  set W := LinearMap.range B.vecMulLinear
  set f : W →ₗ[D] (n₁ → D) := sumProjL n₁ n₂ ∘ₗ W.subtype
  set X := (LinearMap.range M₂.vecMulLinear).map (sumInrL n₁ n₂)
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  -- the range of `f` contains the row space of `M₁`
  have h₁ : LinearMap.range M₁.vecMulLinear ≤ LinearMap.range f := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨B.vecMulLinear (Sum.elim x 0), LinearMap.mem_range_self _ _⟩, ?_⟩
    ext i
    simp [f, B, sumProjL, Matrix.vecMul_fromBlocks]
  -- `X = 0 ⊕ rowspace M₂` lies in `W`
  have hXW : X ≤ W := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨Sum.elim 0 x, ?_⟩
    simp only [B, Matrix.vecMulLinear_apply, Matrix.vecMul_fromBlocks]
    ext (i | i) <;> simp [sumInrL]
  -- and in the kernel of `f`
  have h₂ : X.comap W.subtype ≤ LinearMap.ker f := by
    intro w hw
    rw [Submodule.mem_comap, Submodule.mem_map] at hw
    obtain ⟨y, -, hy⟩ := hw
    rw [LinearMap.mem_ker]
    funext i
    have := congrFun hy (Sum.inl i)
    simp only [sumInrL, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Pi.zero_apply,
      Submodule.subtype_apply] at this
    simpa [f, sumProjL] using this.symm
  have hX : finrank D X = finrank D (LinearMap.range M₂.vecMulLinear) :=
    (Submodule.equivMapOfInjective _ (sumInrL_injective n₁ n₂) _).finrank_eq.symm
  have hXc : finrank D (X.comap W.subtype) = finrank D X :=
    (Submodule.comapSubtypeEquivOfLe hXW).finrank_eq
  calc finrank D (LinearMap.range M₁.vecMulLinear) + finrank D (LinearMap.range M₂.vecMulLinear)
      ≤ finrank D (LinearMap.range f) + finrank D (LinearMap.ker f) := by
        refine add_le_add (Submodule.finrank_mono h₁) ?_
        rw [← hX, ← hXc]
        exact Submodule.finrank_mono h₂
    _ = finrank D W := hrn

theorem rankD_fromBlocks_diag {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Fintype n₁]
    [Fintype n₂] (M₁ : Matrix m₁ n₁ D) (M₂ : Matrix m₂ n₂ D) :
    rankD (fromBlocks M₁ 0 0 M₂) = rankD M₁ + rankD M₂ :=
  le_antisymm (rankD_fromBlocks_diag_le M₁ M₂) (rankD_fromBlocks_tri M₁ M₂ 0)

variable (D) in
/-- The rank over a division ring, `M ↦ rank_D M`, is a Sylvester matrix rank function. -/
noncomputable def rankDRankFunction : SylvesterRankFunction D where
  rk M := (rankD M : ℝ)
  rk_nonneg' _ := Nat.cast_nonneg _
  rk_zero' := by simp
  rk_one' := by simp
  rk_mul_le' M₁ M₂ := by
    rw [le_min_iff]
    exact ⟨by exact_mod_cast rankD_mul_le_left M₁ M₂, by exact_mod_cast rankD_mul_le_right M₁ M₂⟩
  rk_blockDiag' M₁ M₂ := by
    rw [blockFin, rankD_submatrix_equiv]
    exact_mod_cast rankD_fromBlocks_diag M₁ M₂
  rk_blockTri' M₁ M₂ M₃ := by
    rw [blockFin, rankD_submatrix_equiv]
    exact_mod_cast rankD_fromBlocks_tri M₁ M₂ M₃

@[simp]
theorem rankDRankFunction_rk {m n : ℕ} (M : Matrix (Fin m) (Fin n) D) :
    (rankDRankFunction D).rk M = rankD M := rfl

theorem rankDRankFunction_rkF {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n D) :
    (rankDRankFunction D).rkF M = rankD M := by
  classical
  rw [SylvesterRankFunction.rkF_eq _ M (Fintype.equivFin m).symm (Fintype.equivFin n).symm,
    rankDRankFunction_rk, rankD_submatrix_equiv]

/-! ### Invertibility criteria over a division ring -/

/-- Left independent rows ⇒ a left inverse exists (square matrices over a division ring). -/
theorem exists_mul_eq_one_of_vecMul {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n D)
    (h : ∀ x, x ᵥ* P = 0 → x = 0) : ∃ Q : Matrix n n D, Q * P = 1 := by
  have hinj : Function.Injective P.vecMulLinear := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact h
  have hsurj : Function.Surjective P.vecMulLinear := LinearMap.injective_iff_surjective.1 hinj
  choose x hx using fun i => hsurj (Pi.single i 1)
  refine ⟨Matrix.of fun i j => x i j, ?_⟩
  ext i j
  have e1 : (Matrix.of (fun i j => x i j) * P) i j = (x i ᵥ* P) j := by
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  rw [e1, ← Matrix.vecMulLinear_apply, hx i, Pi.single_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

/-- Left independent rows ⇒ invertible (square matrices over a division ring). -/
theorem isUnit_of_vecMul_eq_zero {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n D)
    (h : ∀ x, x ᵥ* P = 0 → x = 0) : IsUnit P := by
  obtain ⟨Q, hQ⟩ := exists_mul_eq_one_of_vecMul P h
  have hQinj : ∀ y, y ᵥ* Q = 0 → y = 0 := by
    intro y hy
    have : y ᵥ* Q ᵥ* P = 0 := by rw [hy, Matrix.zero_vecMul]
    rwa [Matrix.vecMul_vecMul, hQ, Matrix.vecMul_one] at this
  obtain ⟨Q', hQ'⟩ := exists_mul_eq_one_of_vecMul Q hQinj
  have hPQ' : P = Q' := by
    calc P = Q' * Q * P := by rw [hQ', Matrix.one_mul]
      _ = Q' := by rw [Matrix.mul_assoc, hQ, Matrix.mul_one]
  refine ⟨⟨P, Q, ?_, hQ⟩, rfl⟩
  rw [hPQ', hQ']

/-- Right independent columns ⇒ invertible (square matrices over a division ring), by passing
to the opposite division ring. -/
theorem isUnit_of_mulVec_eq_zero {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n D)
    (h : ∀ x, P *ᵥ x = 0 → x = 0) : IsUnit P := by
  have key : ∀ (B₁ B₂ : Matrix n n Dᵐᵒᵖ),
      (B₁ * B₂).transpose.map MulOpposite.unop =
        B₂.transpose.map MulOpposite.unop * B₁.transpose.map MulOpposite.unop := by
    intro B₁ B₂
    ext i j
    simp [Matrix.mul_apply, Finset.unop_sum]
  have hone : (1 : Matrix n n Dᵐᵒᵖ).transpose.map MulOpposite.unop = 1 := by
    rw [Matrix.transpose_one, Matrix.map_one _ MulOpposite.unop_zero MulOpposite.unop_one]
  have hB : IsUnit (P.transpose.map MulOpposite.op) := by
    refine isUnit_of_vecMul_eq_zero _ fun x hx => ?_
    have hx' : P *ᵥ (fun i => (x i).unop) = 0 := by
      funext j
      have := congrArg MulOpposite.unop (congrFun hx j)
      simpa [Matrix.vecMul, Matrix.mulVec, dotProduct, Finset.unop_sum] using this
    have h0 := h _ hx'
    funext i
    have := congrFun h0 i
    simpa using congrArg MulOpposite.op this
  obtain ⟨u, hu⟩ := hB
  have hP : (u : Matrix n n Dᵐᵒᵖ).transpose.map MulOpposite.unop = P := by
    rw [hu]; ext i j; simp
  refine ⟨⟨P, (↑u⁻¹ : Matrix n n Dᵐᵒᵖ).transpose.map MulOpposite.unop, ?_, ?_⟩, rfl⟩
  · rw [← hP, ← key, Units.inv_mul, hone]
  · rw [← hP, ← key, Units.mul_inv, hone]

end rankD

/-! ### Pullback along ring homomorphisms -/

theorem blockFin_map {R S : Type*} {m₁ m₂ n₁ n₂ : ℕ} (A : Matrix (Fin m₁) (Fin n₁) R)
    (B : Matrix (Fin m₁) (Fin n₂) R) (C : Matrix (Fin m₂) (Fin n₁) R)
    (D : Matrix (Fin m₂) (Fin n₂) R) (f : R → S) :
    (blockFin A B C D).map f = blockFin (A.map f) (B.map f) (C.map f) (D.map f) := by
  rw [blockFin, blockFin, ← Matrix.fromBlocks_map, Matrix.submatrix_map]

/-- The pullback `M ↦ rk (φ M)` of a Sylvester rank function along a ring homomorphism. -/
def SylvesterRankFunction.comap {R S : Type*} [Ring R] [Ring S] (ρ : SylvesterRankFunction S)
    (φ : R →+* S) : SylvesterRankFunction R where
  rk M := ρ.rk (M.map φ)
  rk_nonneg' M := ρ.rk_nonneg' _
  rk_zero' := by
    intro m n
    rw [Matrix.map_zero φ φ.map_zero]
    exact ρ.rk_zero'
  rk_one' := by rw [Matrix.map_one φ φ.map_zero φ.map_one]; exact ρ.rk_one'
  rk_mul_le' M₁ M₂ := by rw [Matrix.map_mul]; exact ρ.rk_mul_le' _ _
  rk_blockDiag' M₁ M₂ := by
    rw [blockFin_map, Matrix.map_zero φ φ.map_zero, Matrix.map_zero φ φ.map_zero]
    exact ρ.rk_blockDiag' _ _
  rk_blockTri' M₁ M₂ M₃ := by
    rw [blockFin_map, Matrix.map_zero φ φ.map_zero]
    exact ρ.rk_blockTri' _ _ _

@[simp]
theorem SylvesterRankFunction.comap_rk {R S : Type*} [Ring R] [Ring S]
    (ρ : SylvesterRankFunction S) (φ : R →+* S) {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) :
    (ρ.comap φ).rk M = ρ.rk (M.map φ) := rfl

/-- The Sylvester rank function `M ↦ rank_D φ(M)` attached to a ring homomorphism `φ` from `R`
to a division ring `D` (paper, Section 5, "A ring homomorphism φ … gives one"). -/
noncomputable def rankFun {R D : Type*} [Ring R] [DivisionRing D] (φ : R →+* D) :
    SylvesterRankFunction R :=
  (rankDRankFunction D).comap φ

@[simp]
theorem rankFun_rk {R D : Type*} [Ring R] [DivisionRing D] (φ : R →+* D) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) R) : (rankFun φ).rk M = rankD (M.map φ) := rfl

theorem rankFun_rkF {R D : Type*} [Ring R] [DivisionRing D] (φ : R →+* D) {m n : Type*}
    [Fintype m] [Fintype n] (M : Matrix m n R) : (rankFun φ).rkF M = rankD (M.map φ) := by
  classical
  rw [SylvesterRankFunction.rkF_eq _ M (Fintype.equivFin m).symm (Fintype.equivFin n).symm,
    rankFun_rk, ← Matrix.submatrix_map, rankD_submatrix_equiv]

end NonSofic
