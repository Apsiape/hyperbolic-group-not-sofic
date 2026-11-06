import FiniteLean.GroupTheory.DivisionRing.FullRank

/-!
# Assembly: the abstract proof of Theorem `thm:linnell`

Douglas–Mghirbi v1.1.0, Section 5, "Proof of Theorem `thm:linnell`", with the group-specific
inputs (the line subgroups and the rank collapse of Theorem `thm:collapse`) as hypotheses.

A `LineDatum Λ r` packages, for one label `i`:
* the subgroup `A = A_i`, `δ = δ_i : A → ℤ`, `t = t_i ∈ A` with `δ t = 1` (so `A0 = ker δ`),
* the elements `y u v = x_{iuv} x_{i00}⁻¹ ∈ A` with `δ (y u u) = 0` and `δ (y u v) = -1`
  (`u ≠ v`),
* the group element `x = x_{i00}`,
and `LineDatum.matrix K` is `Y_i = (y u v * x)_{u,v} = (x_{iuv})_{u,v}` over `K[Λ]`.

Main results, for every ring homomorphism `φ : K[Λ] → D` to a division ring:
* `exists_not_powersLeftIndep`: if `∑ᵢ rank_D φ(Yᵢ) < |I| r / 4`, the powers of some `φ(tᵢ)` are
  left dependent over `D_{Aᵢ⁰}`;
* `not_isLinnell`, `not_isStronglyHughesFree`, `not_satisfiesHF` (the latter for finitely
  generated `Aᵢ`);
* `linnell_obstruction_of_collapse`: the same conclusions from the rank collapse
  `∑ᵢ rk(Yᵢ) < |I| r / 4` for every Sylvester rank function on a ring `R` mapping to `K[Λ]`
  (e.g. `R = K[G]` for a subgroup `G ≤ Λ`), as in the paper.
-/

namespace NonSofic

open Matrix MonoidAlgebra

/-- The data attached to one line label (see the module docstring). -/
structure LineDatum (Λ : Type*) [Group Λ] (r : ℕ) extends ZQuotientData Λ where
  /-- `y u v = x_{iuv} x_{i00}⁻¹`. -/
  y : Fin r → Fin r → Λ
  y_mem : ∀ u v, y u v ∈ A
  δ_diag : ∀ u, δ ⟨y u u, y_mem u u⟩ = 1
  δ_off : ∀ u v, u ≠ v → δ ⟨y u v, y_mem u v⟩ = Multiplicative.ofAdd (-1)
  /-- `x = x_{i00}`. -/
  x : Λ

namespace LineDatum

variable {Λ : Type*} [Group Λ] {r : ℕ} (L : LineDatum Λ r)

/-- `Y_i = (y u v * x)_{u,v}` over `K[Λ]`. -/
noncomputable def matrix (K : Type*) [Ring K] : Matrix (Fin r) (Fin r) (MonoidAlgebra K Λ) :=
  Matrix.of fun u v => of K Λ (L.y u v * L.x)

variable {K : Type*} [Ring K] {D : Type*} [DivisionRing D]

/-- If `y u v * x = X u v`, then `Y_i` is the matrix of the group elements `X u v`
(e.g. `X u v = x_{iuv}`, `y u v = x_{iuv} x_{i00}⁻¹`, `x = x_{i00}`). -/
theorem matrix_eq_of (X : Fin r → Fin r → Λ) (hX : ∀ u v, L.y u v * L.x = X u v) :
    L.matrix K = Matrix.of fun u v => of K Λ (X u v) := by
  ext u v
  simp [matrix, hX]

/-- `φ(Y_i)` is invertible when the powers of `φ(t_i)` are left independent over `D_{A_i⁰}`
(Lemma `lem:fullrank` together with `φ(Y_i) = φ(Y') φ(x_{i00})`). -/
theorem isUnit_map (φ : MonoidAlgebra K Λ →+* D)
    (hind : PowersLeftIndep (divClosure φ L.A0) (φ (of K Λ L.t))) :
    IsUnit ((L.matrix K).map φ) := by
  classical
  have hY : (L.matrix K).map φ = (Matrix.of fun u v => of K Λ (L.y u v)).map φ *
      Matrix.diagonal (fun _ => φ (of K Λ L.x)) := by
    ext u v
    rw [Matrix.mul_diagonal]
    simp only [matrix, Matrix.map_apply, Matrix.of_apply]
    rw [← map_mul, ← map_mul]
  rw [hY]
  refine (isUnit_map_of_zQuotientData φ L.toZQuotientData L.y L.y_mem L.δ_diag L.δ_off
    hind).mul ?_
  set c := φ (of K Λ L.x)
  have hc : c ≠ 0 := map_of_ne_zero φ L.x
  refine ⟨⟨Matrix.diagonal (fun _ => c), Matrix.diagonal (fun _ => c⁻¹), ?_, ?_⟩, rfl⟩
  · rw [Matrix.diagonal_mul_diagonal]; simp [hc, Matrix.diagonal_one]
  · rw [Matrix.diagonal_mul_diagonal]; simp [hc, Matrix.diagonal_one]

theorem rankD_map (φ : MonoidAlgebra K Λ →+* D)
    (hind : PowersLeftIndep (divClosure φ L.A0) (φ (of K Λ L.t))) :
    rankD ((L.matrix K).map φ) = r := by
  classical
  rw [rankD_eq_card_of_isUnit (L.isUnit_map φ hind), Fintype.card_fin]

end LineDatum

section Assembly

variable {K : Type*} [Ring K] {Λ : Type*} [Group Λ] {D : Type*} [DivisionRing D]

/-- First paragraph of the proof of `thm:linnell`: the rank bound forces, for some label `i`,
a left dependence of the powers of `φ(t_i)` over `D_{A_i⁰}`. -/
theorem exists_not_powersLeftIndep {I : Type*} [Fintype I] {r : ℕ} (φ : MonoidAlgebra K Λ →+* D)
    (L : I → LineDatum Λ r)
    (hsum : ∑ i, (rankD (((L i).matrix K).map φ) : ℝ) < Fintype.card I * r / 4) :
    ∃ i, ¬ PowersLeftIndep (divClosure φ (L i).A0) (φ (of K Λ (L i).t)) := by
  by_contra h
  push Not at h
  have hr : ∀ i, rankD (((L i).matrix K).map φ) = r := fun i => (L i).rankD_map φ (h i)
  simp only [hr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have h0 : (0 : ℝ) ≤ (Fintype.card I : ℝ) * r := by positivity
  linarith

/-- No Linnell division ring. -/
theorem not_isLinnell {I : Type*} [Fintype I] {r : ℕ} (φ : MonoidAlgebra K Λ →+* D) (L : I → LineDatum Λ r)
    (hsum : ∑ i, (rankD (((L i).matrix K).map φ) : ℝ) < Fintype.card I * r / 4) : ¬ IsLinnell φ := by
  intro hL
  obtain ⟨i, hi⟩ := exists_not_powersLeftIndep φ L hsum
  exact hi (hL.powersLeftIndep fun _ hk => (L i).zpow_mem_A0 hk)

/-- No strongly Hughes-free division ring. -/
theorem not_isStronglyHughesFree {I : Type*} [Fintype I] {r : ℕ} (φ : MonoidAlgebra K Λ →+* D)
    (L : I → LineDatum Λ r)
    (hsum : ∑ i, (rankD (((L i).matrix K).map φ) : ℝ) < Fintype.card I * r / 4) :
    ¬ IsStronglyHughesFree φ := by
  intro hS
  obtain ⟨i, hi⟩ := exists_not_powersLeftIndep φ L hsum
  exact hi (hS.powersLeftIndep (L i).isNormalIn (L i).t_mem fun _ hk => (L i).zpow_mem_A0 hk)

/-- Condition (HF) fails (the line subgroups being finitely generated). -/
theorem not_satisfiesHF {I : Type*} [Fintype I] {r : ℕ} (φ : MonoidAlgebra K Λ →+* D) (L : I → LineDatum Λ r)
    (hfg : ∀ i, IsFinitelyGenerated (L i).A)
    (hsum : ∑ i, (rankD (((L i).matrix K).map φ) : ℝ) < Fintype.card I * r / 4) :
    ¬ SatisfiesHF φ := by
  intro hHF
  obtain ⟨i, hi⟩ := exists_not_powersLeftIndep φ L hsum
  exact hi (hHF (L i).A0 (L i).A (L i).t (hfg i) (L i).isNormalIn (L i).isInfCyclicQuotient)

/-- The rank collapse for all Sylvester rank functions on a ring `R` mapping to `K[Λ]` gives
the rank bound for `φ` (restrict `φ` along `ψ`). -/
theorem sum_rankD_lt_of_collapse {I : Type*} [Fintype I] {r : ℕ} {R : Type*} [Ring R]
    (ψ : R →+* MonoidAlgebra K Λ) (L : I → LineDatum Λ r)
    (Y₀ : I → Matrix (Fin r) (Fin r) R) (hY : ∀ i, (Y₀ i).map ψ = (L i).matrix K)
    (hcollapse : ∀ ρ : SylvesterRankFunction R, ∑ i, ρ.rk (Y₀ i) < Fintype.card I * r / 4)
    (φ : MonoidAlgebra K Λ →+* D) :
    ∑ i, (rankD (((L i).matrix K).map φ) : ℝ) < Fintype.card I * r / 4 := by
  have h := hcollapse (rankFun (φ.comp ψ))
  have he : ∀ i, (Y₀ i).map (φ.comp ψ) = ((L i).matrix K).map φ := fun i => by
    rw [← hY i, Matrix.map_map, RingHom.coe_comp]
  simpa only [rankFun_rk, he] using h

/-- **Theorem `thm:linnell`, abstract form.** Given line data `L i` whose matrices `Y_i` come
from matrices `Y₀ i` over a ring `R → K[Λ]` satisfying the rank collapse
`∑ᵢ rk(Y₀ i) < |I| r / 4` for every Sylvester rank function on `R`, no ring homomorphism from
`K[Λ]` to a division ring is Linnell or strongly Hughes-free, and none satisfies (HF) if the
line subgroups are finitely generated. -/
theorem linnell_obstruction_of_collapse {I : Type*} [Fintype I] {r : ℕ} {R : Type*} [Ring R]
    (ψ : R →+* MonoidAlgebra K Λ) (L : I → LineDatum Λ r)
    (Y₀ : I → Matrix (Fin r) (Fin r) R) (hY : ∀ i, (Y₀ i).map ψ = (L i).matrix K)
    (hcollapse : ∀ ρ : SylvesterRankFunction R, ∑ i, ρ.rk (Y₀ i) < Fintype.card I * r / 4)
    (hfg : ∀ i, IsFinitelyGenerated (L i).A) (φ : MonoidAlgebra K Λ →+* D) :
    ¬ IsLinnell φ ∧ ¬ IsStronglyHughesFree φ ∧ ¬ SatisfiesHF φ := by
  have hsum := sum_rankD_lt_of_collapse ψ L Y₀ hY hcollapse φ
  exact ⟨not_isLinnell φ L hsum, not_isStronglyHughesFree φ L hsum,
    not_satisfiesHF φ L hfg hsum⟩

end Assembly

end NonSofic
