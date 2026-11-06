import FiniteLean.GroupTheory.DivisionRing.Assembly

/-!
# Line data from free bases: the abstract form of Theorem `thm:linnell`

Douglas–Mghirbi v1.1.0, Section 5.  For one label `i`, let `X u v = x_{iuv}` (`u, v ∈ [r]`) be
elements of a group `Λ`, and suppose that the homomorphism `lineHom` from the free group on
`{(u, v) ≠ (0, 0)}` sending `y_{uv} ↦ X u v * (X 0 0)⁻¹` is injective (Lemma `lem:free`, pushed
along an injective `G → Λ`).  Then (`exists_lineDatum`, for `r ≥ 2`) its image `A_i` with
`δ_i(y_{uv}) = -1` (`u ≠ v`), `δ_i(y_{uu}) = 0`, `t_i = y_{01}⁻¹`, `x = X 0 0` is a `LineDatum`
with matrix `(X u v)`, and `A_i` is finitely generated.

`linnell_obstruction_of_lines`: if moreover `∑ᵢ rank_D φ(X_i) < |I| r / 4`, then `φ` is not
Linnell, not strongly Hughes-free, and does not satisfy (HF).  (For `r = 1` the rank bound is
contradictory by itself, since every `φ(X_i)` is a nonzero `1 × 1` matrix.)
-/

namespace NonSofic

open Matrix MonoidAlgebra

variable {Λ : Type*} [Group Λ]

/-- The index set `{(u, v) ≠ (0, 0)}` of the free basis of a line subgroup. -/
abbrev LineIdx (r : ℕ) (hr : 0 < r) : Type := {p : Fin r × Fin r // p ≠ (⟨0, hr⟩, ⟨0, hr⟩)}

/-- `δ` on the free group: `y_{uv} ↦ -1` for `u ≠ v` and `y_{uu} ↦ 0` (written multiplicatively). -/
def lineDegree (r : ℕ) (hr : 0 < r) : FreeGroup (LineIdx r hr) →* Multiplicative ℤ :=
  FreeGroup.lift fun p => if p.1.1 = p.1.2 then 1 else Multiplicative.ofAdd (-1)

/-- The homomorphism `y_{uv} ↦ X u v * (X 0 0)⁻¹`. -/
def lineHom {r : ℕ} (hr : 0 < r) (X : Fin r → Fin r → Λ) : FreeGroup (LineIdx r hr) →* Λ :=
  FreeGroup.lift fun p => X p.1.1 p.1.2 * (X ⟨0, hr⟩ ⟨0, hr⟩)⁻¹

/-- A free basis `y_{uv} = X u v * (X 0 0)⁻¹` gives a `LineDatum` whose matrix is `(X u v)`, with
finitely generated `A`. -/
theorem exists_lineDatum {r : ℕ} (hr : 0 < r) (hr1 : 1 < r) (X : Fin r → Fin r → Λ)
    (hfree : Function.Injective (lineHom hr X)) :
    ∃ L : LineDatum Λ r, IsFinitelyGenerated L.A ∧ ∀ u v, L.y u v * L.x = X u v := by
  classical
  set o : Fin r := ⟨0, hr⟩ with ho
  set o1 : Fin r := ⟨1, hr1⟩ with ho1
  set ψ := lineHom hr X with hψdef
  let e : FreeGroup (LineIdx r hr) ≃* ψ.range := MonoidHom.ofInjective hfree
  let δ : ψ.range →* Multiplicative ℤ := (lineDegree r hr).comp e.symm.toMonoidHom
  let y : Fin r → Fin r → Λ := fun u v => X u v * (X o o)⁻¹
  have hψ : ∀ p : LineIdx r hr, ψ (FreeGroup.of p) = y p.1.1 p.1.2 := fun p => by
    simp [hψdef, lineHom, y, ho]
  have hoo : y o o = 1 := by simp [y]
  have hmem : ∀ u v, y u v ∈ ψ.range := by
    intro u v
    by_cases h : (u, v) = (o, o)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [hoo]
      exact ψ.range.one_mem
    · exact ⟨FreeGroup.of ⟨(u, v), h⟩, hψ _⟩
  have hδ : ∀ u v, δ ⟨y u v, hmem u v⟩ = if u = v then 1 else Multiplicative.ofAdd (-1) := by
    intro u v
    by_cases h : (u, v) = (o, o)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      have h1 : (⟨y o o, hmem o o⟩ : ψ.range) = 1 := Subtype.ext hoo
      rw [h1, map_one, ite_eq_left_iff.2 (fun h => absurd rfl h)]
    · have h1 : (⟨y u v, hmem u v⟩ : ψ.range) = e (FreeGroup.of ⟨(u, v), h⟩) := by
        apply Subtype.ext
        rw [MonoidHom.ofInjective_apply, hψ]
      rw [h1]
      simp [δ, lineDegree]
  have hne : o ≠ o1 := by
    rw [ho, ho1, ne_eq, Fin.ext_iff]
    simp
  refine ⟨⟨⟨ψ.range, δ, (y o o1)⁻¹, ψ.range.inv_mem (hmem o o1), ?_⟩, y, hmem, fun u => ?_,
      fun u v huv => ?_, X o o⟩, ?_, fun u v => by simp [y]⟩
  · have h1 : (⟨(y o o1)⁻¹, ψ.range.inv_mem (hmem o o1)⟩ : ψ.range) =
        (⟨y o o1, hmem o o1⟩ : ψ.range)⁻¹ := rfl
    rw [h1, map_inv, hδ]
    simp [hne]
  · rw [hδ, ite_eq_left_iff.2 (fun h => absurd rfl h)]
  · rw [hδ]
    simp [huv]
  · refine ⟨Finset.univ.image (fun p => ψ (FreeGroup.of p)), ?_⟩
    show _ = ψ.range
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, MonoidHom.range_eq_map,
      ← FreeGroup.closure_range_of, MonoidHom.map_closure, ← Set.range_comp]
    rfl

/-- **Theorem `thm:linnell`, abstract form.** Let `X i u v` (`i ∈ I`, `u, v ∈ [r]`) be elements of
`Λ` such that for every `i` the elements `X i u v * (X i 0 0)⁻¹`, `(u, v) ≠ (0, 0)`, freely
generate a subgroup, and let `φ : K[Λ] → D` be a ring homomorphism to a division ring with
`∑ᵢ rank_D φ((X i u v)_{u,v}) < |I| r / 4`. Then `φ` is not Linnell, not strongly Hughes-free,
and does not satisfy (HF). -/
theorem linnell_obstruction_of_lines {K : Type*} [Ring K] {D : Type*} [DivisionRing D]
    {I : Type*} [Fintype I] {r : ℕ} (hr : 0 < r) (X : I → Fin r → Fin r → Λ)
    (hfree : ∀ i, Function.Injective (lineHom hr (X i))) (φ : MonoidAlgebra K Λ →+* D)
    (hsum : ∑ i, (rankD ((Matrix.of fun u v => of K Λ (X i u v)).map φ) : ℝ) <
      Fintype.card I * r / 4) :
    ¬ IsLinnell φ ∧ ¬ IsStronglyHughesFree φ ∧ ¬ SatisfiesHF φ := by
  classical
  rcases Nat.lt_or_ge 1 r with hr1 | hr1
  · choose L hfg hX using fun i => exists_lineDatum hr hr1 (X i) (hfree i)
    have hY : ∀ i, (L i).matrix K = Matrix.of fun u v => of K Λ (X i u v) :=
      fun i => (L i).matrix_eq_of _ (hX i)
    have hsum' : ∑ i, (rankD (((L i).matrix K).map φ) : ℝ) < Fintype.card I * r / 4 := by
      simpa only [hY] using hsum
    exact ⟨not_isLinnell φ L hsum', not_isStronglyHughesFree φ L hsum',
      not_satisfiesHF φ L hfg hsum'⟩
  · exfalso
    have hr1' : r = 1 := by omega
    subst hr1'
    have hunit : ∀ i, rankD ((Matrix.of fun u v => of K Λ (X i u v)).map φ) = 1 := by
      intro i
      apply rankD_eq_of_isUnit
      apply isUnit_of_vecMul_eq_zero
      intro x hx
      funext j
      have h0 := congrFun hx 0
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_one, Matrix.map_apply,
        Matrix.of_apply, Pi.zero_apply] at h0
      rw [Subsingleton.elim j 0, Pi.zero_apply]
      exact (mul_eq_zero.1 h0).resolve_right (map_of_ne_zero φ _)
    simp only [hunit, Nat.cast_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at hsum
    have : (0 : ℝ) ≤ Fintype.card I := by positivity
    linarith

end NonSofic
