import FiniteLean.GroupTheory.DivisionRing.RankD
import FiniteLean.GroupTheory.DivisionRing.Freeness

/-!
# Lemma `lem:fullrank`

Douglas–Mghirbi v1.1.0, Section 5, Lemma `lem:fullrank`.

*Abstract form* (`isUnit_of_skewLaurent`): let `D` be a division ring, `D₀ ≤ D` a division
subring, `t ≠ 0` with `t D₀ t⁻¹ ⊆ D₀`, whose powers `tᵏ` (`k ∈ ℤ`) are left linearly
independent over `D₀`.  Then every `r × r` matrix with entries `n u v * t ^ δ u v`, where
`n u v ∈ D₀`, `n u u ≠ 0`, `δ u u = 0` and `δ u v = -1` for `u ≠ v`, is invertible.

*Proof used here.*  Instead of the paper's skew-Laurent ring / Ore localization we argue with a
finite-dimensional invariant subspace (the statement is the same).  If `P x = 0` for a column
`x ≠ 0`, the equations give `x u = ∑_{v ≠ u} (-(n u u)⁻¹ n u v) t⁻¹ x v`, so the left
`D₀`-span `W` of `x 1, …, x r` satisfies `t W ⊆ W`.  For `x u₀ ≠ 0`, the `r + 1` vectors
`tᵏ x u₀ ∈ W` (`0 ≤ k ≤ r`) are left dependent over `D₀`, and cancelling `x u₀` on the right
gives a nontrivial relation `∑ dₖ tᵏ = 0` with `dₖ ∈ D₀`, a contradiction.  So the columns of
`P` are right independent and `P` is invertible.

*Group form* (`isUnit_map_of_powersLeftIndep`, `isUnit_map_of_zQuotientData`): for
`φ : K[Λ] → D`, `A0 ≤ Λ` normalized by `t`, and group elements `y u v` with `y u u ∈ A0`,
`y u v t ∈ A0` (`u ≠ v`) — i.e. `δ (y u u) = 0`, `δ (y u v) = -1` for `δ : A → ℤ` with kernel
`A0` and `δ t = 1` — if the powers of `φ(t)` are left independent over `D_{A0}` then `φ(y u v)`
is an invertible matrix, of rank `r`.
-/

namespace NonSofic

open Matrix MonoidAlgebra

section Core

variable {D : Type*} [DivisionRing D]

/-- More rows than columns over a division ring: the rows are left dependent. -/
theorem exists_ne_zero_vecMul_eq_zero {E : Type*} [DivisionRing E] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) E) (h : n < m) : ∃ d : Fin m → E, d ≠ 0 ∧ d ᵥ* A = 0 := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective A.vecMulLinear := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    by_contra hne
    exact hcon d hne hd
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fin_fun] at this
  omega

/-- Left independence of the integer powers gives left independence of `t⁰, …, t^(m-1)`. -/
theorem PowersLeftIndep.natPow {D₀ : Subfield D} {x : D} (h : PowersLeftIndep D₀ x) {m : ℕ}
    (c : Fin m → D) (hc : ∀ k, c k ∈ D₀) (hsum : ∑ k, c k * x ^ (k : ℕ) = 0) : c = 0 := by
  classical
  let f : Fin m → ℤ := fun k => ((k : ℕ) : ℤ)
  have hf : Function.Injective f := fun a b hab => Fin.ext (by simpa [f] using hab)
  let c' : ℤ → D := Function.extend f c 0
  have hc' : ∀ k, c' (f k) = c k := fun k => hf.extend_apply c 0 k
  have h' := h (Finset.univ.map ⟨f, hf⟩) c' (by
      intro j hj
      obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 hj
      rw [Function.Embedding.coeFn_mk, hc']
      exact hc k)
    (by
      rw [Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, hc']
      simp only [f, zpow_natCast]
      exact hsum)
  funext k
  rw [Pi.zero_apply, ← hc']
  exact h' _ (Finset.mem_map_of_mem _ (Finset.mem_univ k))

/-- **Lemma `lem:fullrank`, abstract form.** -/
theorem isUnit_of_skewLaurent {r : ℕ} (D₀ : Subfield D) (t : D) (ht : t ≠ 0)
    (hconj : ∀ d ∈ D₀, t * d * t⁻¹ ∈ D₀) (hind : PowersLeftIndep D₀ t)
    (n : Fin r → Fin r → D) (hn : ∀ u v, n u v ∈ D₀) (hn0 : ∀ u, n u u ≠ 0)
    (δ : Fin r → Fin r → ℤ) (hδd : ∀ u, δ u u = 0) (hδo : ∀ u v, u ≠ v → δ u v = -1) :
    IsUnit (Matrix.of fun u v => n u v * t ^ δ u v) := by
  classical
  apply isUnit_of_mulVec_eq_zero
  intro x hx
  by_contra hx0
  obtain ⟨u₀, hu₀⟩ : ∃ u, x u ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (funext h)
  -- the equations of `P x = 0`
  have hrow : ∀ u, ∑ v, n u v * t ^ δ u v * x v = 0 := fun u => by
    have := congrFun hx u
    simpa [Matrix.mulVec, dotProduct] using this
  -- step 1: `t W ⊆ W`
  have step1 : ∀ u, ∃ b : Fin r → D, (∀ v, b v ∈ D₀) ∧ t * x u = ∑ v, b v * x v := by
    intro u
    have hsplit : ∀ v, n u v * t ^ δ u v * x v =
        (if v = u then n u u * x u else 0) + (if v = u then 0 else n u v * t⁻¹ * x v) := by
      intro v
      by_cases hv : v = u
      · subst hv; simp [hδd]
      · simp [hv, hδo u v (Ne.symm hv)]
    have h0 : n u u * x u + ∑ v, (if v = u then 0 else n u v * t⁻¹ * x v) = 0 := by
      have := hrow u
      rw [Finset.sum_congr rfl fun v _ => hsplit v, Finset.sum_add_distrib] at this
      simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] using this
    have hxu : x u = -(n u u)⁻¹ * ∑ v, (if v = u then 0 else n u v * t⁻¹ * x v) := by
      have h1 := eq_neg_of_add_eq_zero_left h0
      calc x u = (n u u)⁻¹ * (n u u * x u) := by
            rw [← mul_assoc, inv_mul_cancel₀ (hn0 u), one_mul]
        _ = _ := by rw [h1, mul_neg, neg_mul]
    refine ⟨fun v => if v = u then 0 else t * (-(n u u)⁻¹ * n u v) * t⁻¹, fun v => ?_, ?_⟩
    · show (if v = u then (0 : D) else t * (-(n u u)⁻¹ * n u v) * t⁻¹) ∈ D₀
      split_ifs
      · exact D₀.zero_mem
      · exact hconj _ (D₀.mul_mem (D₀.neg_mem (D₀.inv_mem (hn u u))) (hn u v))
    · rw [hxu, ← mul_assoc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : v = u <;> simp [hv, mul_assoc]
  choose b hbmem hb using step1
  -- step 2: `tᵏ x u₀ ∈ W` for all `k`
  have step2 : ∀ k : ℕ, ∃ a : Fin r → D, (∀ v, a v ∈ D₀) ∧ t ^ k * x u₀ = ∑ v, a v * x v := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun v => if v = u₀ then 1 else 0, fun v => ?_, by simp [ite_mul]⟩
      show (if v = u₀ then (1 : D) else 0) ∈ D₀
      split_ifs
      · exact D₀.one_mem
      · exact D₀.zero_mem
    | succ k ih =>
      obtain ⟨a, ha, hk⟩ := ih
      refine ⟨fun w => ∑ v, t * a v * t⁻¹ * b v w,
        fun w => D₀.sum_mem fun v _ => D₀.mul_mem (hconj _ (ha v)) (hbmem v w), ?_⟩
      have key : ∀ v, t * (a v * x v) = t * a v * t⁻¹ * (t * x v) := fun v => by
        rw [mul_assoc (t * a v) t⁻¹, ← mul_assoc t⁻¹ t, inv_mul_cancel₀ ht, one_mul, mul_assoc]
      calc t ^ (k + 1) * x u₀ = t * (t ^ k * x u₀) := by rw [pow_succ', mul_assoc]
        _ = ∑ v, t * a v * t⁻¹ * (t * x v) := by
          rw [hk, Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => key v
        _ = ∑ v, t * a v * t⁻¹ * ∑ w, b v w * x w := by simp_rw [hb]
        _ = ∑ w, (∑ v, t * a v * t⁻¹ * b v w) * x w := by
          simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
          exact Finset.sum_comm
  choose a ha hak using step2
  -- step 3: a dependence among `t⁰ x u₀, …, tʳ x u₀`
  let A : Matrix (Fin (r + 1)) (Fin r) D₀ := fun k v => ⟨a (k : ℕ) v, ha (k : ℕ) v⟩
  obtain ⟨d, hd0, hdA⟩ := exists_ne_zero_vecMul_eq_zero A (Nat.lt_succ_self r)
  have hcomb : (∑ k : Fin (r + 1), (d k : D) * t ^ (k : ℕ)) * x u₀ = 0 := by
    rw [Finset.sum_mul]
    simp_rw [mul_assoc, hak, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun v _ => ?_
    have hv : ((d ᵥ* A) v : D) = 0 := by simp [hdA]
    have : ((d ᵥ* A) v : D) = ∑ k, (d k : D) * a k v := by
      simp [Matrix.vecMul, dotProduct, A]
    rw [this] at hv
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hv, zero_mul]
  have hzero : ∑ k : Fin (r + 1), (d k : D) * t ^ (k : ℕ) = 0 :=
    (mul_eq_zero.1 hcomb).resolve_right hu₀
  have := hind.natPow (fun k => (d k : D)) (fun k => (d k).2) hzero
  apply hd0
  funext k
  exact Subtype.ext (congrFun this k)

/-- **Lemma `lem:fullrank`, abstract form, rank version.** -/
theorem rankD_of_skewLaurent {r : ℕ} (D₀ : Subfield D) (t : D) (ht : t ≠ 0)
    (hconj : ∀ d ∈ D₀, t * d * t⁻¹ ∈ D₀) (hind : PowersLeftIndep D₀ t)
    (n : Fin r → Fin r → D) (hn : ∀ u v, n u v ∈ D₀) (hn0 : ∀ u, n u u ≠ 0)
    (δ : Fin r → Fin r → ℤ) (hδd : ∀ u, δ u u = 0) (hδo : ∀ u v, u ≠ v → δ u v = -1) :
    rankD (Matrix.of fun u v => n u v * t ^ δ u v) = r := by
  rw [rankD_eq_card_of_isUnit (isUnit_of_skewLaurent D₀ t ht hconj hind n hn hn0 δ hδd hδo),
    Fintype.card_fin]

end Core

section Group

variable {K : Type*} [Ring K] {Λ : Type*} [Group Λ] {D : Type*} [DivisionRing D]

/-- Conjugation `x ↦ u x u⁻¹` by a nonzero element, as a ring homomorphism. -/
def conjRingHom (u : D) (hu : u ≠ 0) : D →+* D where
  toFun x := u * x * u⁻¹
  map_one' := by simp [hu]
  map_mul' x y := by
    simp only [mul_assoc, inv_mul_cancel_left₀ hu]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]

/-- If `t` normalizes `C` then conjugation by `φ(t)` maps `D_C` into itself. -/
theorem conj_mem_divClosure (φ : MonoidAlgebra K Λ →+* D) {C : Subgroup Λ} {t : Λ}
    (hC : ∀ g ∈ C, t * g * t⁻¹ ∈ C) {d : D} (hd : d ∈ divClosure φ C) :
    φ (of K Λ t) * d * (φ (of K Λ t))⁻¹ ∈ divClosure φ C := by
  have hle : divClosure φ C ≤
      (divClosure φ C).comap (conjRingHom (φ (of K Λ t)) (map_of_ne_zero φ t)) := by
    conv_lhs => rw [divClosure_eq_closure_single]
    rw [Subfield.closure_le]
    rintro _ ⟨g, hg, k, rfl⟩
    show φ (of K Λ t) * φ (single g k) * (φ (of K Λ t))⁻¹ ∈ divClosure φ C
    rw [← map_of_inv, ← map_mul, ← map_mul, MonoidAlgebra.of_apply, MonoidAlgebra.of_apply,
      single_mul_single, single_mul_single, one_mul, mul_one]
    exact single_mem_divClosure φ (hC g hg) k
  exact hle hd

/-- **Lemma `lem:fullrank`, group form.** Let `A0 ≤ Λ` be normalized by `t`, and let
`y u v ∈ Λ` with `y u u ∈ A0` and `y u v * t ∈ A0` for `u ≠ v` (i.e. `y u v ∈ A0 t⁻¹`).  If the
powers of `φ(t)` are left linearly independent over `D_{A0}`, then `φ (y u v)` is invertible. -/
theorem isUnit_map_of_powersLeftIndep (φ : MonoidAlgebra K Λ →+* D) (A0 : Subgroup Λ) (t : Λ)
    (hnorm : ∀ g ∈ A0, t * g * t⁻¹ ∈ A0) {r : ℕ} (y : Fin r → Fin r → Λ)
    (hdiag : ∀ u, y u u ∈ A0) (hoff : ∀ u v, u ≠ v → y u v * t ∈ A0)
    (hind : PowersLeftIndep (divClosure φ A0) (φ (of K Λ t))) :
    IsUnit ((Matrix.of fun u v => of K Λ (y u v)).map φ) := by
  classical
  let δ : Fin r → Fin r → ℤ := fun u v => if u = v then 0 else -1
  let n : Fin r → Fin r → D := fun u v => φ (of K Λ (y u v * t ^ (-δ u v)))
  have hmat : (Matrix.of fun u v => of K Λ (y u v)).map φ =
      Matrix.of fun u v => n u v * φ (of K Λ t) ^ δ u v := by
    ext u v
    simp only [Matrix.map_apply, Matrix.of_apply, n]
    rw [← map_of_zpow, ← map_mul, ← map_mul, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero,
      mul_one]
  have hmem : ∀ u v, y u v * t ^ (-δ u v) ∈ A0 := by
    intro u v
    by_cases h : u = v
    · subst h; simpa [δ] using hdiag u
    · simpa [δ, h] using hoff u v h
  rw [hmat]
  refine isUnit_of_skewLaurent (divClosure φ A0) (φ (of K Λ t)) (map_of_ne_zero φ t)
    (fun d hd => conj_mem_divClosure φ hnorm hd) hind n
    (fun u v => of_mem_divClosure φ (hmem u v)) (fun u => map_of_ne_zero φ _) δ
    (fun u => by simp [δ]) (fun u v h => by simp [δ, h])

/-- **Lemma `lem:fullrank`, as stated in the paper**: `δ : A → ℤ` with kernel `A0`, `δ t = 1`,
`y u v ∈ A` with `δ (y u u) = 0` and `δ (y u v) = -1` for `u ≠ v`.  If the powers `φ(t)ᵏ` are
left linearly independent over `D_{A0}`, the matrix `φ (y u v)` is invertible. -/
theorem isUnit_map_of_zQuotientData (φ : MonoidAlgebra K Λ →+* D) (Q : ZQuotientData Λ)
    {r : ℕ} (y : Fin r → Fin r → Λ) (hy : ∀ u v, y u v ∈ Q.A)
    (hδd : ∀ u, Q.δ ⟨y u u, hy u u⟩ = 1)
    (hδo : ∀ u v, u ≠ v → Q.δ ⟨y u v, hy u v⟩ = Multiplicative.ofAdd (-1))
    (hind : PowersLeftIndep (divClosure φ Q.A0) (φ (of K Λ Q.t))) :
    IsUnit ((Matrix.of fun u v => of K Λ (y u v)).map φ) := by
  refine isUnit_map_of_powersLeftIndep φ Q.A0 Q.t (fun g hg => Q.conj_mem_A0 hg) y
    (fun u => (Q.mem_A0).2 ⟨hy u u, hδd u⟩) (fun u v h => (Q.mem_A0).2 ⟨?_, ?_⟩) hind
  · exact Q.A.mul_mem (hy u v) Q.t_mem
  · have : (⟨y u v * Q.t, Q.A.mul_mem (hy u v) Q.t_mem⟩ : Q.A) =
        ⟨y u v, hy u v⟩ * ⟨Q.t, Q.t_mem⟩ := rfl
    rw [this, map_mul, hδo u v h, Q.δ_t, ← ofAdd_add]
    simp

/-- Rank version of `isUnit_map_of_zQuotientData`: `rank_D φ(Y') = r`. -/
theorem rankD_map_of_zQuotientData (φ : MonoidAlgebra K Λ →+* D) (Q : ZQuotientData Λ)
    {r : ℕ} (y : Fin r → Fin r → Λ) (hy : ∀ u v, y u v ∈ Q.A)
    (hδd : ∀ u, Q.δ ⟨y u u, hy u u⟩ = 1)
    (hδo : ∀ u v, u ≠ v → Q.δ ⟨y u v, hy u v⟩ = Multiplicative.ofAdd (-1))
    (hind : PowersLeftIndep (divClosure φ Q.A0) (φ (of K Λ Q.t))) :
    rankD ((Matrix.of fun u v => of K Λ (y u v)).map φ) = r := by
  classical
  rw [rankD_eq_card_of_isUnit (isUnit_map_of_zQuotientData φ Q y hy hδd hδo hind),
    Fintype.card_fin]

end Group

end NonSofic
