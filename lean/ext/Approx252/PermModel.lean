import OAI.GroupTheory.Hyperbolic.MatrixRank

/-!
# Approximate permutation models of the block presentation

The finite-quotient rank obstruction of `OAI.Release075` (`finite_quotient_rank_obstruction`)
uses the finite group only through its regular permutation representation.  Here the regular
representation is replaced by an arbitrary assignment of permutations of a finite set `Ω` to
the generators `x i u v`, with two defect counts: a bound `e` on the number of fixed points of
every nondegenerate rectangular word, and a bound `k` on the number of points moved by every
triangle relator.  The certificate (`rank_budget_of_line_certificate`) and the integrality
lemma (`rank_reduction_half`) of the original development are reused unchanged.
-/

namespace Approx252

open OAI.Release075
open scoped BigOperators

section PermMat

variable {Ω R : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The permutation matrix `P(σ)` with `P(σ) e_c = e_{σ c}`, as a monoid homomorphism. -/
def permMat [Semiring R] : Equiv.Perm Ω →* Matrix Ω Ω R := Matrix.permMatrixHom

@[simp] theorem permMat_apply [Semiring R] (σ : Equiv.Perm Ω) (a b : Ω) :
    permMat (R := R) σ a b = if a = σ b then 1 else 0 := by
  simp only [permMat, Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  by_cases h : a = σ b
  · subst h; simp
  · have h' : ¬ (σ.symm a = b) := by
      intro hb; apply h; rw [← hb]; simp
    simp [h, h']

@[simp] theorem permMat_transpose [Semiring R] (σ : Equiv.Perm Ω) :
    (permMat (R := R) σ).transpose = permMat σ⁻¹ := by
  ext a b
  simp only [Matrix.transpose_apply, permMat_apply]
  by_cases h : b = σ a
  · subst h; simp
  · have h' : ¬ (a = σ.symm b) := by
      intro ha; apply h; rw [ha]; simp
    simp [h, h']

/-- The number of fixed points of a permutation. -/
def fixCount (σ : Equiv.Perm Ω) : ℕ := (Finset.univ.filter fun c => σ c = c).card

@[simp] theorem fixCount_one : fixCount (1 : Equiv.Perm Ω) = Fintype.card Ω := by
  simp [fixCount]

theorem fixCount_add_card_support (σ : Equiv.Perm Ω) :
    fixCount σ + σ.support.card = Fintype.card Ω := by
  unfold fixCount
  have hs : σ.support = Finset.univ.filter fun c => ¬ σ c = c := by
    ext c
    simp [Equiv.Perm.mem_support]
  rw [hs, ← Finset.card_univ]
  exact Finset.card_filter_add_card_filter_not (fun c => σ c = c)

theorem fixCount_le_card (σ : Equiv.Perm Ω) : fixCount σ ≤ Fintype.card Ω := by
  have := fixCount_add_card_support σ
  omega

@[simp] theorem permMat_trace [Semiring R] (σ : Equiv.Perm Ω) :
    (permMat (R := R) σ).trace = (fixCount σ : R) := by
  simp only [Matrix.trace, Matrix.diag, permMat_apply, fixCount]
  rw [Finset.sum_boole]
  congr 2
  ext c
  simp [eq_comm]

end PermMat

section Model

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The block permutation matrix attached to one line label under a model. -/
def modelMatrix {ι R : Type*} [Semiring R] (x : ι → ι → Equiv.Perm Ω) :
    Matrix (ι × Ω) (ι × Ω) R :=
  flattenMatrix (Matrix.of fun u v => permMat (x u v))

theorem modelMatrix_gram {ι R : Type*} [Fintype ι] [Semiring R] (x : ι → ι → Equiv.Perm Ω) :
    modelMatrix (R := R) x * (modelMatrix x).transpose =
      flattenMatrix (Matrix.of fun u u' => ∑ v, permMat (R := R) (x u v * (x u' v)⁻¹)) := by
  rw [modelMatrix, flattenMatrix_transpose, ← flattenMatrix_mul]
  congr 1
  ext u u' a b
  simp [Matrix.of_apply, Matrix.mul_apply, Matrix.sum_apply, ← map_mul]

theorem modelMatrix_gram_trace {ι R : Type*} [Fintype ι] [Semiring R]
    (x : ι → ι → Equiv.Perm Ω) :
    (modelMatrix (R := R) x * (modelMatrix x).transpose).trace =
      (Fintype.card ι : R) ^ 2 * Fintype.card Ω := by
  rw [modelMatrix_gram, flattenMatrix_trace]
  simp only [Matrix.of_apply, mul_inv_cancel, map_one, Matrix.trace_sum, Matrix.trace_one]
  simp [pow_two, mul_assoc]

theorem modelMatrix_gram_sq_trace {ι R : Type*} [Fintype ι] [Semiring R]
    (x : ι → ι → Equiv.Perm Ω) :
    ((modelMatrix (R := R) x * (modelMatrix x).transpose) *
      (modelMatrix x * (modelMatrix x).transpose)).trace =
        ∑ u, ∑ u', ∑ v, ∑ v', (permMat (R := R)
          (x u v * (x u' v)⁻¹ * x u' v' * (x u v')⁻¹)).trace := by
  rw [modelMatrix_gram, ← flattenMatrix_mul, flattenMatrix_trace]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.sum_mul, Matrix.mul_sum, ← map_mul,
    Matrix.trace_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro u' _
  exact Finset.sum_comm

/-- Every nondegenerate rectangular word of the model fixes at most `e` points. -/
def RectanglesAlmostFree {ι : Type*} (x : ι → ι → Equiv.Perm Ω) (e : ℕ) : Prop :=
  ∀ u u' v v', u ≠ u' → v ≠ v' →
    fixCount (x u v * (x u' v)⁻¹ * x u' v' * (x u v')⁻¹) ≤ e

/-- One term of the second trace expansion: exact for degenerate indices, bounded by `e`
otherwise. -/
theorem fixCount_rect_le {ι : Type*} [DecidableEq ι] (x : ι → ι → Equiv.Perm Ω) (e : ℕ)
    (hx : RectanglesAlmostFree x e) (u u' v v' : ι) :
    (fixCount (x u v * (x u' v)⁻¹ * x u' v' * (x u v')⁻¹) : ℝ) ≤
      (if u = u' then (Fintype.card Ω : ℝ) else 0) +
      (if v = v' then (Fintype.card Ω : ℝ) else 0) -
      (if u = u' ∧ v = v' then (Fintype.card Ω : ℝ) else 0) + e := by
  by_cases hu : u = u'
  · subst u'
    simp only [mul_inv_cancel, one_mul, fixCount_one, true_and]
    have : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    split_ifs <;> linarith
  · by_cases hv : v = v'
    · subst v'
      have h1 : x u v * (x u' v)⁻¹ * x u' v * (x u v)⁻¹ = 1 := by group
      rw [h1, fixCount_one]
      have : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      simp only [hu, ite_false, ite_true, false_and]
      linarith
    · have h := hx u u' v v' hu hv
      simp only [hu, hv, ite_false, false_and, zero_add, sub_zero]
      exact_mod_cast h

theorem modelMatrix_gram_sq_trace_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → Equiv.Perm Ω) (e : ℕ) (hx : RectanglesAlmostFree x e) :
    ((modelMatrix (R := ℝ) x * (modelMatrix x).transpose) *
      (modelMatrix x * (modelMatrix x).transpose)).trace ≤
      (2 * (Fintype.card ι : ℝ) ^ 3 - (Fintype.card ι : ℝ) ^ 2) * Fintype.card Ω +
        (Fintype.card ι : ℝ) ^ 4 * e := by
  rw [modelMatrix_gram_sq_trace]
  simp only [permMat_trace]
  calc
    _ ≤ ∑ u, ∑ u', ∑ v, ∑ v' : ι,
        ((if u = u' then (Fintype.card Ω : ℝ) else 0) +
        (if v = v' then (Fintype.card Ω : ℝ) else 0) -
        (if u = u' ∧ v = v' then (Fintype.card Ω : ℝ) else 0) + e) := by
      gcongr with u _ u' _ v _ v' _
      exact fixCount_rect_le x e hx u u' v v'
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_and]
      simp [pow_succ, mul_assoc, sub_mul]
      ring

theorem modelMatrix_rank_real_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → Equiv.Perm Ω) (e : ℕ) (hx : RectanglesAlmostFree x e)
    (he : Fintype.card ι ^ 2 * e ≤ Fintype.card Ω) :
    Fintype.card ι * Fintype.card Ω ≤ 2 * (modelMatrix (R := ℝ) x).rank := by
  by_cases hzero : Fintype.card ι = 0
  · simp [hzero]
  let Y := modelMatrix (R := ℝ) x
  have hA : (Y * Y.transpose).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self Y
  have hArank : (Y * Y.transpose).rank = Y.rank := Matrix.rank_self_mul_conjTranspose Y
  have h := trace_sq_le_rank_mul_trace_sq (Y * Y.transpose) hA
  rw [hArank] at h
  change (modelMatrix (R := ℝ) x * (modelMatrix x).transpose).trace ^ 2 ≤ _ at h
  rw [modelMatrix_gram_trace] at h
  change _ ≤ (Y.rank : ℝ) * ((modelMatrix (R := ℝ) x * (modelMatrix x).transpose) *
    (modelMatrix x * (modelMatrix x).transpose)).trace at h
  have hsq := modelMatrix_gram_sq_trace_le x e hx
  let r : ℝ := Fintype.card ι
  let D : ℝ := Fintype.card Ω
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast Nat.pos_of_ne_zero hzero
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with hΩ | hΩ
  · simp [hΩ]
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast hΩ
  have hk : 0 ≤ (Y.rank : ℝ) := Nat.cast_nonneg _
  have he' : r ^ 2 * e ≤ D := by
    dsimp [r, D]
    exact_mod_cast he
  have htr : ((modelMatrix (R := ℝ) x * (modelMatrix x).transpose) *
      (modelMatrix x * (modelMatrix x).transpose)).trace ≤ 2 * r ^ 3 * D := by
    refine hsq.trans ?_
    change (2 * r ^ 3 - r ^ 2) * D + r ^ 4 * e ≤ 2 * r ^ 3 * D
    nlinarith [sq_nonneg r]
  have hcancel : (r ^ 3 * D) * (r * D) ≤ (r ^ 3 * D) * (2 * (Y.rank : ℝ)) := by
    calc
      _ = (r ^ 2 * D) ^ 2 := by ring
      _ ≤ (Y.rank : ℝ) * ((modelMatrix (R := ℝ) x * (modelMatrix x).transpose) *
            (modelMatrix x * (modelMatrix x).transpose)).trace := h
      _ ≤ (Y.rank : ℝ) * (2 * r ^ 3 * D) := mul_le_mul_of_nonneg_left htr hk
      _ = _ := by ring
  have hf := (mul_le_mul_iff_right₀ (show 0 < r ^ 3 * D by positivity)).mp hcancel
  dsimp [r, D, Y] at hf
  exact_mod_cast hf

/-- Each integral row has exactly one unit entry per block column. -/
theorem modelMatrix_row_sq {ι : Type*} [Fintype ι] (x : ι → ι → Equiv.Perm Ω) (i : ι × Ω) :
    ∑ j, ((modelMatrix (R := ℤ) x i j : ℤ) : ℝ) ^ 2 = Fintype.card ι := by
  rw [Fintype.sum_prod_type]
  simp [modelMatrix, flattenMatrix, Matrix.of_apply, ← Equiv.Perm.inv_eq_iff_eq]

theorem modelMatrix_map {ι R : Type*} [Ring R] (x : ι → ι → Equiv.Perm Ω) :
    (modelMatrix (R := ℤ) x).map (Int.cast : ℤ → R) = modelMatrix (R := R) x := by
  ext i j
  simp [modelMatrix, flattenMatrix]

theorem modelMatrix_rank_mod_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → Equiv.Perm Ω) (e : ℕ) (hx : RectanglesAlmostFree x e)
    (he : Fintype.card ι ^ 2 * e ≤ Fintype.card Ω)
    (q : ℕ) [Fact q.Prime] (hq : Fintype.card ι < q) :
    Fintype.card ι * Fintype.card Ω ≤ 4 * (modelMatrix (R := ZMod q) x).rank := by
  by_cases hzero : Fintype.card ι = 0
  · simp [hzero]
  have hr : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
  have hqr : (Fintype.card ι : ℝ) < q := by exact_mod_cast hq
  have hred := rank_reduction_half (modelMatrix (R := ℤ) x) (Fintype.card ι) hr
    (fun i => (modelMatrix_row_sq x i).le) q hqr
  rw [modelMatrix_map, modelMatrix_map] at hred
  have hreal := modelMatrix_rank_real_lower x e hx he
  omega

end Model

section Defect

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A permutation matrix differs from the identity only in the columns of moved points. -/
theorem rank_permMat_sub_one_le {K : Type*} [Field K] [DecidableEq K] (θ : Equiv.Perm Ω) :
    (permMat (R := K) θ - 1).rank ≤ θ.support.card := by
  let w : Ω → K := fun c => if θ c = c then 0 else 1
  have hfactor : permMat (R := K) θ - 1 = (permMat (R := K) θ - 1) * Matrix.diagonal w := by
    ext a c
    simp only [Matrix.mul_diagonal, Matrix.sub_apply, permMat_apply, Matrix.one_apply, w]
    by_cases h : θ c = c
    · simp [h]
    · simp [h]
  rw [hfactor]
  refine (Matrix.rank_mul_le_right _ _).trans ?_
  rw [Matrix.rank_diagonal, Fintype.card_subtype]
  apply le_of_eq
  congr 1
  ext c
  by_cases h : θ c = c <;> simp [w, h, Equiv.Perm.mem_support]

/-- Embedding of one block into the flattened block matrix. -/
def singleBlock {ι K : Type*} [DecidableEq ι] [Zero K] (u v : ι) (M : Matrix Ω Ω K) :
    Matrix (ι × Ω) (ι × Ω) K :=
  Matrix.of fun x y => if x.1 = u ∧ y.1 = v then M x.2 y.2 else 0

theorem singleBlock_rank_le {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (u v : ι) (M : Matrix Ω Ω K) : (singleBlock u v M).rank ≤ M.rank := by
  let L : Matrix (ι × Ω) Ω K := Matrix.of fun x a => if x.1 = u ∧ x.2 = a then 1 else 0
  let Rm : Matrix Ω (ι × Ω) K := Matrix.of fun b y => if y.1 = v ∧ b = y.2 then 1 else 0
  have hfactor : singleBlock u v M = L * M * Rm := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp only [singleBlock, L, Rm, Matrix.of_apply, Matrix.mul_apply]
    by_cases hi : i = u <;> by_cases hj : j = v <;> simp [hi, hj]
  rw [hfactor]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

omit [Fintype Ω] [DecidableEq Ω] in
theorem flattenMatrix_eq_sum_singleBlock {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid K] (M : ι → ι → Matrix Ω Ω K) :
    flattenMatrix (Matrix.of M) = ∑ u, ∑ v, singleBlock u v (M u v) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [flattenMatrix_apply, Matrix.of_apply, Matrix.sum_apply]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp [singleBlock]
  · intro v _ hv
    simp [singleBlock, Ne.symm hv]
  · simp
  · intro u _ hu
    simp [singleBlock, Ne.symm hu]
  · simp

theorem permMat_sub_factor {K : Type*} [Ring K] (L x R : Equiv.Perm Ω) :
    permMat (R := K) x - permMat (L⁻¹ * R) =
      permMat L⁻¹ * (permMat (L * x * R⁻¹) - 1) * permMat R := by
  have h1 : L⁻¹ * (L * x * R⁻¹) * R = x := by group
  rw [mul_sub, sub_mul, mul_one, ← map_mul, ← map_mul, h1, ← map_mul]

/-- The rank cost of one approximately satisfied triangle relator. -/
theorem rank_permMat_sub_le {K : Type*} [Field K] [DecidableEq K] (L x R : Equiv.Perm Ω) :
    (permMat (R := K) x - permMat (L⁻¹ * R)).rank ≤ (L * x * R⁻¹).support.card := by
  rw [permMat_sub_factor]
  exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans
    (rank_permMat_sub_one_le _)

/-- A local Cartesian block of exact relations factors through one copy of `K^Ω`. -/
theorem modelMatrix_sum_rank_le {ι s t K : Type*} [Fintype ι] [Fintype s] [Fintype t] [Field K]
    (L : ι → s → Equiv.Perm Ω) (R : ι → t → Equiv.Perm Ω) :
    (∑ j : s, ∑ k : t, modelMatrix (R := K) (fun u v => (L u j)⁻¹ * R v k)).rank ≤
      Fintype.card Ω := by
  classical
  let A : Matrix (ι × Ω) Ω K := Matrix.of fun x a =>
    (∑ j, permMat (R := K) (L x.1 j)⁻¹) x.2 a
  let B : Matrix Ω (ι × Ω) K := Matrix.of fun b y =>
    (∑ k, permMat (R := K) (R y.1 k)) b y.2
  have hfactor :
      (∑ j : s, ∑ k : t, modelMatrix (R := K) (fun u v => (L u j)⁻¹ * R v k)) = A * B := by
    ext ⟨u,a⟩ ⟨v,b⟩
    simp only [Matrix.sum_apply, modelMatrix, flattenMatrix_apply, Matrix.of_apply,
      map_mul, Matrix.mul_apply, A, B]
    simp only [Finset.sum_mul, Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset t))
      (t := (Finset.univ : Finset Ω))]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_comm
  rw [hfactor]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

theorem modelMatrix_sum_reindex {ι B s t K : Type*} [Fintype B] [Fintype s] [Fintype t]
    [Semiring K] (g : B → ι → ι → Equiv.Perm Ω) (L : ι → s → Equiv.Perm Ω)
    (R : ι → t → Equiv.Perm Ω) (e : ι → ι → B ≃ s × t)
    (h : ∀ i u v, g i u v = (L u (e u v i).1)⁻¹ * R v (e u v i).2) :
    (∑ i, modelMatrix (R := K) (g i)) =
      ∑ j : s, ∑ k : t, modelMatrix (R := K) (fun u v => (L u j)⁻¹ * R v k) := by
  ext ⟨u,a⟩ ⟨v,b⟩
  simp only [Matrix.sum_apply, modelMatrix, flattenMatrix_apply, Matrix.of_apply, h]
  exact (Equiv.sum_comp (e u v) (fun p : s × t =>
    (permMat (R := K) ((L u p.1)⁻¹ * R v p.2)) a b)).trans
      (Fintype.sum_prod_type _)

/-- Approximate block relations: every triangle relator `l x ρ⁻¹` of the block moves at most
`k` points of `Ω`. -/
def ApproxRelations {I : Type*} {r : ℕ} (b : CartesianBlock I r)
    (x : I → Fin r → Fin r → Equiv.Perm Ω) (k : ℕ) : Prop :=
  ∃ (L : Fin r → ZMod b.s → Equiv.Perm Ω) (R : Fin r → ZMod b.t → Equiv.Perm Ω),
    ∀ (i : b.labels) u v,
      (L u ((b.coordinates i).1 + (v.val : ZMod b.s)) * x i u v *
        (R v ((b.coordinates i).2 + (u.val : ZMod b.t)))⁻¹).support.card ≤ k

/-- Approximate local factorization: one copy of `K^Ω` plus one rank unit per bad
(point, triangle) pair. -/
theorem block_model_rank_le {I K : Type*} {r : ℕ} [Field K] [DecidableEq K]
    (b : CartesianBlock I r) (x : I → Fin r → Fin r → Equiv.Perm Ω)
    (L : Fin r → ZMod b.s → Equiv.Perm Ω) (R : Fin r → ZMod b.t → Equiv.Perm Ω) (k : ℕ)
    (hrel : ∀ (i : b.labels) u v,
      (L u ((b.coordinates i).1 + (v.val : ZMod b.s)) * x i u v *
        (R v ((b.coordinates i).2 + (u.val : ZMod b.t)))⁻¹).support.card ≤ k) :
    (∑ i ∈ b.labels, modelMatrix (R := K) (x i)).rank ≤
      Fintype.card Ω + b.labels.card * (r * r * k) := by
  classical
  rw [Finset.sum_subtype b.labels (fun _ => Iff.rfl)]
  let g : b.labels → Fin r → Fin r → Equiv.Perm Ω := fun i u v =>
    (L u ((b.coordinates i).1 + (v.val : ZMod b.s)))⁻¹ *
      R v ((b.coordinates i).2 + (u.val : ZMod b.t))
  have hexact : (∑ i : b.labels, modelMatrix (R := K) (g i)).rank ≤ Fintype.card Ω := by
    rw [modelMatrix_sum_reindex g L R b.shifted (fun i u v => rfl)]
    exact modelMatrix_sum_rank_le L R
  have hdiff : ∀ i : b.labels,
      (modelMatrix (R := K) (x i) - modelMatrix (g i)).rank ≤ r * r * k := by
    intro i
    have hflat : modelMatrix (R := K) (x i) - modelMatrix (g i) =
        ∑ u, ∑ v, singleBlock u v (permMat (R := K) (x i u v) - permMat (g i u v)) := by
      rw [← flattenMatrix_eq_sum_singleBlock]
      ext ⟨u,a⟩ ⟨v,c⟩
      simp [modelMatrix, flattenMatrix]
    rw [hflat]
    calc
      _ ≤ ∑ u, ∑ v, (singleBlock u v (permMat (R := K) (x i u v) - permMat (g i u v))).rank :=
          (rank_sum_le _ _).trans (Finset.sum_le_sum fun u _ => rank_sum_le _ _)
      _ ≤ ∑ _u : Fin r, ∑ _v : Fin r, k := by
          gcongr with u _ v _
          exact (singleBlock_rank_le _ _ _).trans
            ((rank_permMat_sub_le (L u ((b.coordinates i).1 + (v.val : ZMod b.s))) (x i u v)
              (R v ((b.coordinates i).2 + (u.val : ZMod b.t)))).trans (hrel i u v))
      _ = r * r * k := by simp [mul_assoc]
  calc
    (∑ i : b.labels, modelMatrix (R := K) (x i)).rank
        = (∑ i : b.labels, (modelMatrix (R := K) (g i) +
            (modelMatrix (R := K) (x i) - modelMatrix (g i)))).rank := by simp
    _ = (∑ i : b.labels, modelMatrix (R := K) (g i) +
          ∑ i : b.labels, (modelMatrix (R := K) (x i) - modelMatrix (g i))).rank := by
        rw [Finset.sum_add_distrib]
    _ ≤ (∑ i : b.labels, modelMatrix (R := K) (g i)).rank +
          (∑ i : b.labels, (modelMatrix (R := K) (x i) - modelMatrix (g i))).rank :=
        rank_add_le _ _
    _ ≤ Fintype.card Ω + ∑ _i : b.labels, (r * r * k) := by
        gcongr
        exact (rank_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hdiff i)
    _ = _ := by simp

theorem two_block_model_rank_le {I K : Type*} [DecidableEq I] [Field K] [DecidableEq K]
    {r : ℕ} (A : Finset I) (x : I → Fin r → Fin r → Equiv.Perm Ω)
    (b₀ b₁ : CartesianBlock I r)
    (hdis : Disjoint b₀.labels b₁.labels) (hunion : b₀.labels ∪ b₁.labels = A) (k : ℕ)
    (h₀ : ApproxRelations b₀ x k) (h₁ : ApproxRelations b₁ x k) :
    (∑ i ∈ A, modelMatrix (R := K) (x i)).rank ≤
      2 * Fintype.card Ω + A.card * (r * r * k) := by
  obtain ⟨L₀,R₀,h₀⟩ := h₀
  obtain ⟨L₁,R₁,h₁⟩ := h₁
  rw [← hunion, Finset.sum_union hdis, Finset.card_union_of_disjoint hdis]
  have h := (rank_add_le _ _).trans (Nat.add_le_add
    (block_model_rank_le (K := K) b₀ x L₀ R₀ k h₀) (block_model_rank_le (K := K) b₁ x L₁ R₁ k h₁))
  have hm : (b₀.labels.card + b₁.labels.card) * (r * r * k) =
      b₀.labels.card * (r * r * k) + b₁.labels.card * (r * r * k) := add_mul _ _ _
  omega

/-- The numerical rank contradiction for approximate models.  `δ z` is the total number of
bad (point, triangle) pairs at the regular point `z`; the budget absorbs `4 ∑ δ`. -/
theorem approx_rank_obstruction {P I : Type*} [Fintype P] [Fintype I] [DecidableEq I]
    (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (inc : P → Finset I) (f : P → I → ZMod q) (E : Finset P)
    (x : I → Fin r → Fin r → Equiv.Perm Ω) (e : ℕ)
    (hx : ∀ i, RectanglesAlmostFree (x i) e) (he : r ^ 2 * e ≤ Fintype.card Ω)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0))
    (δ : P → ℕ)
    (hlocal : ∀ z, z ∉ E → (∑ i ∈ inc z, modelMatrix (R := ZMod q) (x i)).rank ≤
      2 * Fintype.card Ω + δ z)
    (hbudget : 4 * (2 * Fintype.card P + r * E.card) * Fintype.card Ω + 4 * ∑ z, δ z <
      Fintype.card I * r * Fintype.card Ω) : False := by
  classical
  let D := Fintype.card Ω
  let Y := fun i => modelMatrix (R := ZMod q) (x i)
  let Z := fun z => ∑ i ∈ inc z, Y i
  have lower : Fintype.card I * r * D ≤ 4 * ∑ i, (Y i).rank := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      modelMatrix_rank_mod_lower (x i) e (hx i) (by simpa using he) q (by simpa using hq))
    simpa [Y, D, ← Finset.mul_sum, mul_assoc] using h
  have middle : (∑ i, (Y i).rank) ≤ ∑ z, (Z z).rank :=
    rank_budget_of_line_certificate inc f Y hline
  have upper : (∑ z, (Z z).rank) ≤ (2 * Fintype.card P + r * E.card) * D + ∑ z, δ z := by
    have hbound (z : P) : (Z z).rank ≤ 2 * D + δ z + if z ∈ E then r * D else 0 := by
      by_cases hz : z ∈ E
      · rw [ite_eq_left hz]
        have hrank : (Z z).rank ≤ r * D := by
          simpa [D] using Matrix.rank_le_card_height (Z z)
        omega
      · rw [ite_eq_right hz, add_zero]
        exact hlocal z hz
    calc
      _ ≤ ∑ z, (2 * D + δ z + if z ∈ E then r * D else 0) :=
          Finset.sum_le_sum (fun z _ => hbound z)
      _ = _ := by simp [Finset.sum_add_distrib, add_mul]; ring
  have hc : Fintype.card I * r * D ≤
      4 * (2 * Fintype.card P + r * E.card) * D + 4 * ∑ z, δ z := by
    calc
      _ ≤ 4 * ∑ i, (Y i).rank := lower
      _ ≤ 4 * ∑ z, (Z z).rank := Nat.mul_le_mul_left _ middle
      _ ≤ 4 * ((2 * Fintype.card P + r * E.card) * D + ∑ z, δ z) := Nat.mul_le_mul_left _ upper
      _ = _ := by ring
  exact absurd hc (not_le.mpr hbudget)

theorem puncturedLine_card_le {T : Type*} [Fintype T] (q : ℕ) [Fact q.Prime]
    (a v : T → ZMod q) : (puncturedLine a v).card ≤ q - 1 := by
  classical
  have h : (puncturedLine a v).card ≤ ((Finset.univ : Finset (ZMod q)).erase 0).card := by
    unfold puncturedLine
    convert Finset.card_image_le (s := (Finset.univ : Finset (ZMod q)).erase 0)
      (f := affineLineMap a v)
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at h
  exact h

/-- The total number of (regular point, label) incidences is at most `|I| (q - 1)`. -/
theorem sum_card_lineIncidence_le {T I : Type*} [Fintype T] [DecidableEq T] [Fintype I]
    (q : ℕ) [Fact q.Prime] (a v : I → T → ZMod q) :
    (∑ z, (lineIncidence a v z).card) ≤ Fintype.card I * (q - 1) := by
  classical
  have h1 : ∀ z, (lineIncidence a v z).card =
      ∑ i, if z ∈ puncturedLine (a i) (v i) then 1 else 0 := by
    intro z
    unfold lineIncidence
    convert Finset.card_filter (fun i => z ∈ puncturedLine (a i) (v i)) Finset.univ
  simp_rw [h1]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _i : I, (q - 1) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Finset.sum_boole]
      simpa using puncturedLine_card_le q (a i) (v i)
    _ = _ := by simp

/-- **Theorem A (finite-scale obstruction).**  No permutation model of the block
presentation on a finite set `Ω` has every nondegenerate rectangular word fixing at most
`e ≤ |Ω| / r²` points while every triangle relator moves at most `k` points, as soon as
`4 (2 |P| + r |E|) |Ω| + 4 T k < N r |Ω|`, where `T = r² ∑_z |I(z)|` is the number of
triangles. -/
theorem no_model_of_line_blocks {T I : Type*}
    [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I]
    (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (S : Finset (ZMod q)) (a v : I → T → ZMod q)
    (ha : ∀ i t, a i t ∈ S) (hinj : Function.Injective a) (hv : ∀ i, v i ≠ 0)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < q - 1)
    (E : Finset (T → ZMod q)) (x : I → Fin r → Fin r → Equiv.Perm Ω) (e k : ℕ)
    (hx : ∀ i, RectanglesAlmostFree (x i) e) (he : r ^ 2 * e ≤ Fintype.card Ω)
    (hblocks : ∀ z, z ∉ E → ∃ b₀ b₁ : CartesianBlock I r,
      Disjoint b₀.labels b₁.labels ∧ b₀.labels ∪ b₁.labels = lineIncidence a v z ∧
      ApproxRelations b₀ x k ∧ ApproxRelations b₁ x k)
    (hbudget : 4 * (2 * Fintype.card (T → ZMod q) + r * E.card) * Fintype.card Ω +
      4 * ((∑ z, (lineIncidence a v z).card) * (r * r * k)) <
        Fintype.card I * r * Fintype.card Ω) : False := by
  classical
  apply approx_rank_obstruction r q hq (lineIncidence a v)
    (fun z i => gridLagrange S (a i) z) E x e hx he
    (grid_line_certificate S a v ha hinj hv (by simpa using hdeg))
    (fun z => (lineIncidence a v z).card * (r * r * k)) _
    (by rw [← Finset.sum_mul]; exact hbudget)
  intro z hz
  obtain ⟨b₀,b₁,hd,hu,h₀,h₁⟩ := hblocks z hz
  exact two_block_model_rank_le _ x b₀ b₁ hd hu k h₀ h₁

/-- **Theorem A, threshold form.**  Under the data budget `4 (2 |P| + r |E|) < N r` (that is,
`Γ ≥ 1`), no permutation model on a nonempty finite set `Ω` has both defect fractions at most
`ε₀ = 1 / (8 r² N q)`: here `e ≤ ε |Ω|` bounds the fixed points of every nondegenerate
rectangular word and `k ≤ ε |Ω|` bounds the points moved by every triangle relator. -/
theorem no_model_of_line_blocks_threshold {T I : Type*}
    [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I]
    (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (S : Finset (ZMod q)) (a v : I → T → ZMod q)
    (ha : ∀ i t, a i t ∈ S) (hinj : Function.Injective a) (hv : ∀ i, v i ≠ 0)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < q - 1)
    (E : Finset (T → ZMod q))
    (hbudget : 4 * (2 * Fintype.card (T → ZMod q) + r * E.card) < Fintype.card I * r)
    (x : I → Fin r → Fin r → Equiv.Perm Ω) (hΩ : 0 < Fintype.card Ω)
    (ε : ℝ) (hε : ε ≤ 1 / (8 * (r : ℝ) ^ 2 * Fintype.card I * q))
    (e k : ℕ) (hx : ∀ i, RectanglesAlmostFree (x i) e)
    (he : (e : ℝ) ≤ ε * Fintype.card Ω) (hk : (k : ℝ) ≤ ε * Fintype.card Ω)
    (hblocks : ∀ z, z ∉ E → ∃ b₀ b₁ : CartesianBlock I r,
      Disjoint b₀.labels b₁.labels ∧ b₀.labels ∪ b₁.labels = lineIncidence a v z ∧
      ApproxRelations b₀ x k ∧ ApproxRelations b₁ x k) : False := by
  classical
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  have hN : 0 < Fintype.card I := by
    rcases Nat.eq_zero_or_pos (Fintype.card I) with h | h
    · rw [h] at hbudget
      simp at hbudget
    · exact h
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      simp at hbudget
    · exact h
  have hDR : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hΩ
  have hNR : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast hN
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hεnn : 0 ≤ ε := by
    by_contra hneg
    have hlt : ε * Fintype.card Ω < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hDR
    have h0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    linarith
  have hc : (0 : ℝ) < 8 * (r : ℝ) ^ 2 * Fintype.card I * q := by positivity
  have hεc : ε * (8 * (r : ℝ) ^ 2 * Fintype.card I * q) ≤ 1 := (le_div_iff₀ hc).mp hε
  have h8 : (8 : ℝ) ≤ 8 * (Fintype.card I : ℝ) * q := by nlinarith
  have hr2ε : (r : ℝ) ^ 2 * ε ≤ 1 := by
    have h : (r : ℝ) ^ 2 * ε * (8 * (Fintype.card I : ℝ) * q) ≤ 1 * (8 * (Fintype.card I : ℝ) * q) := by
      calc (r : ℝ) ^ 2 * ε * (8 * (Fintype.card I : ℝ) * q)
          = ε * (8 * (r : ℝ) ^ 2 * Fintype.card I * q) := by ring
        _ ≤ 1 := hεc
        _ ≤ 1 * (8 * (Fintype.card I : ℝ) * q) := by linarith
    exact le_of_mul_le_mul_right h (by positivity)
  have h4 : 4 * (Fintype.card I : ℝ) * q * (r : ℝ) ^ 2 * ε ≤ 1 / 2 := by
    calc 4 * (Fintype.card I : ℝ) * q * (r : ℝ) ^ 2 * ε
        = ε * (8 * (r : ℝ) ^ 2 * Fintype.card I * q) / 2 := by ring
      _ ≤ 1 / 2 := by linarith
  apply no_model_of_line_blocks r q hq S a v ha hinj hv hdeg E x e k hx ?_ hblocks ?_
  · have hreal : (r : ℝ) ^ 2 * e ≤ Fintype.card Ω := by
      calc (r : ℝ) ^ 2 * e ≤ (r : ℝ) ^ 2 * (ε * Fintype.card Ω) := by gcongr
        _ = ((r : ℝ) ^ 2 * ε) * Fintype.card Ω := by ring
        _ ≤ 1 * Fintype.card Ω := by gcongr
        _ = _ := one_mul _
    exact_mod_cast hreal
  · have hS := sum_card_lineIncidence_le q a v
    have hS' : ((∑ z, (lineIncidence a v z).card : ℕ) : ℝ) ≤ (Fintype.card I : ℝ) * q := by
      have : (∑ z, (lineIncidence a v z).card) ≤ Fintype.card I * q :=
        hS.trans (Nat.mul_le_mul_left _ (Nat.sub_le q 1))
      exact_mod_cast this
    have hA : (4 * (2 * (Fintype.card (T → ZMod q) : ℝ) + (r : ℝ) * (E.card : ℝ))) + 1 ≤
        (Fintype.card I : ℝ) * r := by
      have : 4 * (2 * Fintype.card (T → ZMod q) + r * E.card) + 1 ≤ Fintype.card I * r := hbudget
      exact_mod_cast this
    have hA' : (4 * (2 * (Fintype.card (T → ZMod q) : ℝ) + (r : ℝ) * (E.card : ℝ))) *
        Fintype.card Ω + Fintype.card Ω ≤ (Fintype.card I : ℝ) * r * Fintype.card Ω := by
      calc (4 * (2 * (Fintype.card (T → ZMod q) : ℝ) + (r : ℝ) * (E.card : ℝ))) *
            Fintype.card Ω + Fintype.card Ω
          = ((4 * (2 * (Fintype.card (T → ZMod q) : ℝ) + (r : ℝ) * (E.card : ℝ))) + 1) *
            Fintype.card Ω := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hA hDR.le
    have hprod : (4 : ℝ) * (((∑ z, (lineIncidence a v z).card : ℕ) : ℝ) *
        ((r : ℝ) * (r : ℝ) * (k : ℝ))) ≤ 1 / 2 * Fintype.card Ω := by
      calc (4 : ℝ) * (((∑ z, (lineIncidence a v z).card : ℕ) : ℝ) * ((r : ℝ) * (r : ℝ) * (k : ℝ)))
          ≤ 4 * (((Fintype.card I : ℝ) * q) * ((r : ℝ) * (r : ℝ) * (ε * Fintype.card Ω))) := by
            gcongr
        _ = (4 * (Fintype.card I : ℝ) * q * (r : ℝ) ^ 2 * ε) * Fintype.card Ω := by ring
        _ ≤ 1 / 2 * Fintype.card Ω := mul_le_mul_of_nonneg_right h4 hDR.le
    have goalR : (4 * (2 * (Fintype.card (T → ZMod q) : ℝ) + (r : ℝ) * (E.card : ℝ))) *
        (Fintype.card Ω : ℝ) + (4 : ℝ) * (((∑ z, (lineIncidence a v z).card : ℕ) : ℝ) *
          ((r : ℝ) * (r : ℝ) * (k : ℝ))) < (Fintype.card I : ℝ) * (r : ℝ) * (Fintype.card Ω : ℝ) := by
      linarith
    exact_mod_cast goalR

end Defect

end Approx252
