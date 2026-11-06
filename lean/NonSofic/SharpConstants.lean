import FiniteLean.GroupTheory.Sofic.PermModel
import NonSofic.SharpCount

/-! Sharp constants (`thm:ineq`): the `2r³-r²` degenerate terms of `tr A²` are exactly `|Ω|`,
only `r²(r-1)²` are rectangular words, so `(r-1)² e ≤ |Ω|` suffices
(`modelMatrix_rank_mod_lower_sharp`); `approx_rank_ineq_sharp(_reg)` is `thm:ineq` in counts;
`block_model_rank_le_sum` keeps the exact per-triangle defects. -/

namespace NonSofic

open OAI.Release075 Approx252
open scoped BigOperators


section Sharp

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- One term of the second trace expansion, with the exact degenerate value. -/
theorem fixCount_rect_le_sharp {ι : Type*} [DecidableEq ι] (x : ι → ι → Equiv.Perm Ω)
    (e : ℕ) (hx : RectanglesAlmostFree x e) (u u' v v' : ι) :
    (fixCount (x u v * (x u' v)⁻¹ * x u' v' * (x u v')⁻¹) : ℝ) ≤
      (if u = u' then (Fintype.card Ω : ℝ) else 0) +
      (if v = v' then (Fintype.card Ω : ℝ) else 0) -
      (if u = u' ∧ v = v' then (Fintype.card Ω : ℝ) else 0) +
      (if u ≠ u' ∧ v ≠ v' then (e : ℝ) else 0) := by
  by_cases hu : u = u'
  · subst u'
    have hw : x u v * (x u v)⁻¹ * x u v' * (x u v')⁻¹ = 1 := by group
    rw [hw, fixCount_one]
    by_cases hv : v = v' <;> simp [hv]
  · by_cases hv : v = v'
    · subst v'
      have hw : x u v * (x u' v)⁻¹ * x u' v * (x u v)⁻¹ = 1 := by group
      rw [hw, fixCount_one]
      simp [hu]
    · have h := hx u u' v v' hu hv
      simpa [hu, hv] using h

theorem modelMatrix_gram_sq_trace_le_sharp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → Equiv.Perm Ω) (e : ℕ) (hx : RectanglesAlmostFree x e) :
    ((modelMatrix (R := ℝ) x * (modelMatrix x).transpose) *
      (modelMatrix x * (modelMatrix x).transpose)).trace ≤
      (2 * (Fintype.card ι : ℝ) ^ 3 - (Fintype.card ι : ℝ) ^ 2) * Fintype.card Ω +
        (Fintype.card ι : ℝ) ^ 2 * ((Fintype.card ι : ℝ) - 1) ^ 2 * e := by
  rw [modelMatrix_gram_sq_trace]
  simp only [permMat_trace]
  calc
    _ ≤ ∑ u, ∑ u', ∑ v, ∑ v' : ι,
        ((if u = u' then (Fintype.card Ω : ℝ) else 0) +
        (if v = v' then (Fintype.card Ω : ℝ) else 0) -
        (if u = u' ∧ v = v' then (Fintype.card Ω : ℝ) else 0) +
        (if u ≠ u' ∧ v ≠ v' then (e : ℝ) else 0)) := by
      gcongr with u _ u' _ v _ v' _
      exact fixCount_rect_le_sharp x e hx u u' v v'
    _ = _ := sum_rect_count _ _

/-- Step 2 with the sharp threshold `(r-1)² e ≤ D`. -/
theorem modelMatrix_rank_real_lower_sharp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → Equiv.Perm Ω) (e : ℕ) (hx : RectanglesAlmostFree x e)
    (he : (Fintype.card ι - 1) ^ 2 * e ≤ Fintype.card Ω) :
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
  have hsq := modelMatrix_gram_sq_trace_le_sharp x e hx
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
  have hcast : ((Fintype.card ι - 1 : ℕ) : ℝ) = r - 1 := by
    dsimp [r]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hzero), Nat.cast_one]
  have he' : (r - 1) ^ 2 * e ≤ D := by
    rw [← hcast]
    dsimp [D]
    exact_mod_cast he
  have he2 : r ^ 2 * ((r - 1) ^ 2 * e) ≤ r ^ 2 * D :=
    mul_le_mul_of_nonneg_left he' (sq_nonneg r)
  have htr : ((modelMatrix (R := ℝ) x * (modelMatrix x).transpose) *
      (modelMatrix x * (modelMatrix x).transpose)).trace ≤ 2 * r ^ 3 * D := by
    refine hsq.trans ?_
    change (2 * r ^ 3 - r ^ 2) * D + r ^ 2 * (r - 1) ^ 2 * e ≤ 2 * r ^ 3 * D
    nlinarith [he2]
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

/-- Step 3 with the sharp threshold. -/
theorem modelMatrix_rank_mod_lower_sharp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → Equiv.Perm Ω) (e : ℕ) (hx : RectanglesAlmostFree x e)
    (he : (Fintype.card ι - 1) ^ 2 * e ≤ Fintype.card Ω)
    (q : ℕ) [Fact q.Prime] (hq : Fintype.card ι < q) :
    Fintype.card ι * Fintype.card Ω ≤ 4 * (modelMatrix (R := ZMod q) x).rank := by
  by_cases hzero : Fintype.card ι = 0
  · simp [hzero]
  have hr : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
  have hqr : (Fintype.card ι : ℝ) < q := by exact_mod_cast hq
  have hred := rank_reduction_half (modelMatrix (R := ℤ) x) (Fintype.card ι) hr
    (fun i => (modelMatrix_row_sq x i).le) q hqr
  rw [modelMatrix_map, modelMatrix_map] at hred
  have hreal := modelMatrix_rank_real_lower_sharp x e hx he
  omega

/-- **Theorem `thm:ineq`** (abstract form).  With `δ z` bounding the excess rank at the regular
point `z` (in the application: the number of bad (point, triangle) pairs at `z`),
`N r D ≤ 4 (2 |P| + r |E|) D + 4 ∑_z δ z`, i.e. `∑ δ / D ≥ N r/4 - 2m - r|E| = Γ/4`. -/
theorem approx_rank_ineq_sharp {P I : Type*} [Fintype P] [Fintype I] [DecidableEq I]
    (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (inc : P → Finset I) (f : P → I → ZMod q) (E : Finset P)
    (x : I → Fin r → Fin r → Equiv.Perm Ω) (e : ℕ)
    (hx : ∀ i, RectanglesAlmostFree (x i) e) (he : (r - 1) ^ 2 * e ≤ Fintype.card Ω)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0))
    (δ : P → ℕ)
    (hlocal : ∀ z, z ∉ E → (∑ i ∈ inc z, modelMatrix (R := ZMod q) (x i)).rank ≤
      2 * Fintype.card Ω + δ z) :
    Fintype.card I * r * Fintype.card Ω ≤
      4 * (2 * Fintype.card P + r * E.card) * Fintype.card Ω + 4 * ∑ z, δ z := by
  classical
  let D := Fintype.card Ω
  let Y := fun i => modelMatrix (R := ZMod q) (x i)
  let Z := fun z => ∑ i ∈ inc z, Y i
  have lower : Fintype.card I * r * D ≤ 4 * ∑ i, (Y i).rank := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      modelMatrix_rank_mod_lower_sharp (x i) e (hx i) (by simpa using he) q
        (by simpa using hq))
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
  calc Fintype.card I * r * D
      ≤ 4 * ∑ i, (Y i).rank := lower
    _ ≤ 4 * ∑ z, (Z z).rank := Nat.mul_le_mul_left _ middle
    _ ≤ 4 * ((2 * Fintype.card P + r * E.card) * D + ∑ z, δ z) := Nat.mul_le_mul_left _ upper
    _ = 4 * (2 * Fintype.card P + r * E.card) * D + 4 * ∑ z, δ z := by ring

/-- **Theorem `thm:ineq`**, with the defect `δ` defined on the regular points only. -/
theorem approx_rank_ineq_sharp_reg {P I : Type*} [Fintype P] [DecidableEq P] [Fintype I]
    [DecidableEq I] (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (inc : P → Finset I) (f : P → I → ZMod q) (E : Finset P) [Fintype {z // z ∉ E}]
    (x : I → Fin r → Fin r → Equiv.Perm Ω) (e : ℕ)
    (hx : ∀ i, RectanglesAlmostFree (x i) e) (he : (r - 1) ^ 2 * e ≤ Fintype.card Ω)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0))
    (δ : {z // z ∉ E} → ℕ)
    (hlocal : ∀ z : {z // z ∉ E}, (∑ i ∈ inc z, modelMatrix (R := ZMod q) (x i)).rank ≤
      2 * Fintype.card Ω + δ z) :
    Fintype.card I * r * Fintype.card Ω ≤
      4 * (2 * Fintype.card P + r * E.card) * Fintype.card Ω + 4 * ∑ z, δ z := by
  have h := approx_rank_ineq_sharp r q hq inc f E x e hx he hline
    (fun z => if h : z ∈ E then 0 else δ ⟨z, h⟩) (by
      intro z hz
      simp only [dif_neg hz]
      exact hlocal ⟨z, hz⟩)
  rwa [sum_dite_not_mem] at h

/-- `no_model_of_line_blocks` with the sharp rectangle threshold `(r-1)² e ≤ |Ω|`. -/
theorem no_model_of_line_blocks_sharp {T I : Type*}
    [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I]
    (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (S : Finset (ZMod q)) (a v : I → T → ZMod q)
    (ha : ∀ i t, a i t ∈ S) (hinj : Function.Injective a) (hv : ∀ i, v i ≠ 0)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < q - 1)
    (E : Finset (T → ZMod q)) (x : I → Fin r → Fin r → Equiv.Perm Ω) (e k : ℕ)
    (hx : ∀ i, RectanglesAlmostFree (x i) e) (he : (r - 1) ^ 2 * e ≤ Fintype.card Ω)
    (hblocks : ∀ z, z ∉ E → ∃ b₀ b₁ : CartesianBlock I r,
      Disjoint b₀.labels b₁.labels ∧ b₀.labels ∪ b₁.labels = lineIncidence a v z ∧
      ApproxRelations b₀ x k ∧ ApproxRelations b₁ x k)
    (hbudget : 4 * (2 * Fintype.card (T → ZMod q) + r * E.card) * Fintype.card Ω +
      4 * ((∑ z, (lineIncidence a v z).card) * (r * r * k)) <
        Fintype.card I * r * Fintype.card Ω) : False := by
  classical
  have h := approx_rank_ineq_sharp r q hq (lineIncidence a v)
    (fun z i => gridLagrange S (a i) z) E x e hx he
    (grid_line_certificate S a v ha hinj hv (by simpa using hdeg))
    (fun z => (lineIncidence a v z).card * (r * r * k)) (by
      intro z hz
      obtain ⟨b₀,b₁,hd,hu,h₀,h₁⟩ := hblocks z hz
      exact two_block_model_rank_le _ x b₀ b₁ hd hu k h₀ h₁)
  rw [← Finset.sum_mul] at h
  exact absurd h (not_le.mpr hbudget)

/-- `Approx252.block_model_rank_le` with the exact per-triangle defects: one copy of `K^Ω` plus,
for every triangle `(i, u, v)` of the block, the number of points moved by its relator. -/
theorem block_model_rank_le_sum {I K : Type*} {r : ℕ} [Field K] [DecidableEq K]
    (b : CartesianBlock I r) (x : I → Fin r → Fin r → Equiv.Perm Ω)
    (L : Fin r → ZMod b.s → Equiv.Perm Ω) (R : Fin r → ZMod b.t → Equiv.Perm Ω) :
    (∑ i ∈ b.labels, modelMatrix (R := K) (x i)).rank ≤
      Fintype.card Ω + ∑ i : b.labels, ∑ u, ∑ v,
        (L u ((b.coordinates i).1 + (v.val : ZMod b.s)) * x i u v *
          (R v ((b.coordinates i).2 + (u.val : ZMod b.t)))⁻¹).support.card := by
  classical
  rw [Finset.sum_subtype b.labels (fun _ => Iff.rfl)]
  let g : b.labels → Fin r → Fin r → Equiv.Perm Ω := fun i u v =>
    (L u ((b.coordinates i).1 + (v.val : ZMod b.s)))⁻¹ *
      R v ((b.coordinates i).2 + (u.val : ZMod b.t))
  have hexact : (∑ i : b.labels, modelMatrix (R := K) (g i)).rank ≤ Fintype.card Ω := by
    rw [modelMatrix_sum_reindex g L R b.shifted (fun i u v => rfl)]
    exact modelMatrix_sum_rank_le L R
  have hdiff : ∀ i : b.labels,
      (modelMatrix (R := K) (x i) - modelMatrix (g i)).rank ≤ ∑ u, ∑ v,
        (L u ((b.coordinates i).1 + (v.val : ZMod b.s)) * x i u v *
          (R v ((b.coordinates i).2 + (u.val : ZMod b.t)))⁻¹).support.card := by
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
      _ ≤ _ := by
          gcongr with u _ v _
          exact (singleBlock_rank_le _ _ _).trans
            (rank_permMat_sub_le (L u ((b.coordinates i).1 + (v.val : ZMod b.s))) (x i u v)
              (R v ((b.coordinates i).2 + (u.val : ZMod b.t))))
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
    _ ≤ _ := by
        gcongr
        exact (rank_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hdiff i)

/-- Two blocks at a regular point, with the exact per-triangle defects (`b₁`'s first). -/
theorem two_block_model_rank_le_sum {I K : Type*} [DecidableEq I] [Field K] [DecidableEq K]
    {r : ℕ} (A : Finset I) (x : I → Fin r → Fin r → Equiv.Perm Ω)
    (b₀ b₁ : CartesianBlock I r)
    (hdis : Disjoint b₀.labels b₁.labels) (hunion : b₀.labels ∪ b₁.labels = A)
    (L₀ : Fin r → ZMod b₀.s → Equiv.Perm Ω) (R₀ : Fin r → ZMod b₀.t → Equiv.Perm Ω)
    (L₁ : Fin r → ZMod b₁.s → Equiv.Perm Ω) (R₁ : Fin r → ZMod b₁.t → Equiv.Perm Ω) :
    (∑ i ∈ A, modelMatrix (R := K) (x i)).rank ≤ 2 * Fintype.card Ω +
      ((∑ i : b₁.labels, ∑ u, ∑ v,
        (L₁ u ((b₁.coordinates i).1 + (v.val : ZMod b₁.s)) * x i u v *
          (R₁ v ((b₁.coordinates i).2 + (u.val : ZMod b₁.t)))⁻¹).support.card) +
       (∑ i : b₀.labels, ∑ u, ∑ v,
        (L₀ u ((b₀.coordinates i).1 + (v.val : ZMod b₀.s)) * x i u v *
          (R₀ v ((b₀.coordinates i).2 + (u.val : ZMod b₀.t)))⁻¹).support.card)) := by
  rw [← hunion, Finset.sum_union hdis]
  have h := (rank_add_le _ _).trans (Nat.add_le_add
    (block_model_rank_le_sum (K := K) b₀ x L₀ R₀) (block_model_rank_le_sum (K := K) b₁ x L₁ R₁))
  omega

end Sharp


end NonSofic
