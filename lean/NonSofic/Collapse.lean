import FiniteLean.GroupTheory.RankCertificate
import NonSofic.DataBounds
import FiniteLean.GroupTheory.OAI.GroupTheory.Hyperbolic.Main

/-! `thm:collapse` for OpenAI's group: for `c : ZMod q →+* R`, `χ : G →* R` (e.g.
`MonoidAlgebra.of K G`, or `of K Λ ∘ ι`), `ρ : RankFn R`: `∑_i ρ(Y_i) ≤ 2(m-|E|)+r|E|` and
`4(2(m-|E|)+r|E|) < N r`. -/

namespace NonSofic

open OAI.Release075
open scoped BigOperators

variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

/-- `Y_i = (x_{iuv})_{u,v ∈ [r]}`, pushed into `R` by `χ`. -/
noncomputable def lineMatrix {R : Type*} [Ring R] (χ : (d.presentation hr).GroupType →* R) (i : d.Label) :
    Matrix (Fin r) (Fin r) R :=
  Matrix.of fun u v => χ ((d.presentation hr).x i u v)

/-- The triangle relators give `Y_i(u,v) = χ(L⁻¹) χ(R)` on each block. -/
theorem lineMatrix_block {R : Type*} [Ring R] (χ : (d.presentation hr).GroupType →* R)
    (b : d.BlockIndex) : ∀ (i : (d.block hr b).labels) (u v : Fin r),
      lineMatrix d hr χ i u v =
        χ (((d.presentation hr).l b u
          (((d.block hr b).coordinates i).1 + (v.val : ZMod (d.block hr b).s)))⁻¹) *
        χ ((d.presentation hr).rr b v
          (((d.block hr b).coordinates i).2 + (u.val : ZMod (d.block hr b).t))) := by
  intro i u v
  have h := congrArg χ ((d.presentation hr).triangle_relation b i u v)
  rw [map_mul] at h
  exact h

/-- **Theorem `thm:collapse`.** -/
theorem collapse {R : Type*} [Ring R] (ρ : RankFn R) (c : ZMod q →+* R)
    (χ : (d.presentation hr).GroupType →* R) :
    ∑ i, ρ.rk (lineMatrix d hr χ i) ≤
        ((2 * (q ^ 20 - d.exceptional.card) + r * d.exceptional.card : ℕ) : ℝ) ∧
      4 * (2 * (q ^ 20 - d.exceptional.card) + r * d.exceptional.card) <
        Fintype.card d.Label * r := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  refine ⟨?_, by have hb := d.budget; omega⟩
  have hcert := rk_sum_le_certificate c ρ d.incidences
    (fun z i => gridLagrange d.scalarGrid (d.mark i) z)
    (grid_line_certificate d.scalarGrid d.mark (fun i => (d.direction i).rep) d.marks_mem
      d.marks_injective (fun i => (d.direction i).rep_nonzero)
      (by simpa using d.degree_cutoff (two_hundred_le d)))
    (lineMatrix d hr χ)
  have hz : ∀ z, ρ.rk (∑ i ∈ d.incidences z, lineMatrix d hr χ i) ≤
      if z ∈ d.exceptional then (r : ℝ) else 2 := by
    intro z
    split_ifs with hzE
    · simpa using ρ.le_card_width (∑ i ∈ d.incidences z, lineMatrix d hr χ i)
    · let p := d.partition hr ⟨z, hzE⟩
      exact rk_two_blocks_le ρ (d.incidences z) (lineMatrix d hr χ) p.zero p.one
        p.disjoint p.cover
        (fun u j => χ (((d.presentation hr).l (⟨z, hzE⟩, false) u j)⁻¹))
        (fun v k => χ ((d.presentation hr).rr (⟨z, hzE⟩, false) v k))
        (fun u j => χ (((d.presentation hr).l (⟨z, hzE⟩, true) u j)⁻¹))
        (fun v k => χ ((d.presentation hr).rr (⟨z, hzE⟩, true) v k))
        (lineMatrix_block d hr χ (⟨z, hzE⟩, false))
        (lineMatrix_block d hr χ (⟨z, hzE⟩, true))
  have hcard : Fintype.card (Fin 20 → ZMod q) = q ^ 20 := by simp
  have hE : d.exceptional.card ≤ q ^ 20 := by
    rw [← hcard]
    exact Finset.card_le_univ _
  calc ∑ i, ρ.rk (lineMatrix d hr χ i)
      ≤ ∑ z, ρ.rk (∑ i ∈ d.incidences z, lineMatrix d hr χ i) := hcert
    _ ≤ ∑ z, (if z ∈ d.exceptional then (r : ℝ) else 2) := Finset.sum_le_sum (fun z _ => hz z)
    _ = Fintype.card (Fin 20 → ZMod q) * 2 + d.exceptional.card * ((r : ℝ) - 2) :=
        sum_ite_mem_const _ _ _
    _ = ((2 * (q ^ 20 - d.exceptional.card) + r * d.exceptional.card : ℕ) : ℝ) := by
        rw [hcard]
        push_cast [Nat.cast_sub hE]
        ring

/-- `thm:collapse` for the group ring `K[G]` of a division ring `K` of characteristic `q`. -/
theorem collapse_groupRing (K : Type*) [DivisionRing K] [CharP K q]
    (ρ : RankFn (MonoidAlgebra K (d.presentation hr).GroupType)) :
    ∑ i, ρ.rk (lineMatrix d hr (MonoidAlgebra.of K (d.presentation hr).GroupType) i) ≤
        ((2 * (q ^ 20 - d.exceptional.card) + r * d.exceptional.card : ℕ) : ℝ) ∧
      4 * (2 * (q ^ 20 - d.exceptional.card) + r * d.exceptional.card) <
        Fintype.card d.Label * r :=
  collapse d hr ρ
    (MonoidAlgebra.singleOneRingHom.comp (ZMod.castHom (dvd_refl q) K))
    (MonoidAlgebra.of K (d.presentation hr).GroupType)

end NonSofic
