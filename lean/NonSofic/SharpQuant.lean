import NonSofic.SharpConstants
import NonSofic.DataBounds
import FiniteLean.GroupTheory.OAI.GroupTheory.Hyperbolic.Main

/-! `thm:ineq`/`thm:quant` for OpenAI's presentation.  `σ : Edge → Sym(Ω)` assigns permutations
to generators; `triangleSupport` = points moved by `σ(θ_{b,i,u,v})`; `RectFix σ e` = every
rectangular word fixes `≤ e` points.  `presentation_quant_lemma22` takes `N ≥ m/(2C)`,
`r|E| ≤ m`, `100C ≤ r` as hypotheses (not exposed by OAI). -/

namespace NonSofic

open OAI.Release075 Approx252
open scoped BigOperators

section Presentation

variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The number of points moved by the triangle relator `θ_{b,i,u,v} = L x R⁻¹` under an
assignment `σ` of permutations to the generators. -/
noncomputable def triangleSupport (σ : (d.presentation hr).Edge → Equiv.Perm Ω) (b : d.BlockIndex)
    (i : (d.block hr b).labels) (u v : Fin r) : ℕ :=
  (σ (.inr (.inl ⟨b, u, ((d.block hr b).coordinates i).1 + (v.val : ZMod (d.block hr b).s)⟩)) *
    σ (.inl (i.val, u, v)) *
    (σ (.inr (.inr ⟨b, v, ((d.block hr b).coordinates i).2 +
      (u.val : ZMod (d.block hr b).t)⟩)))⁻¹).support.card

/-- Every nondegenerate rectangular word of the assignment fixes at most `e` points. -/
def RectFix (σ : (d.presentation hr).Edge → Equiv.Perm Ω) (e : ℕ) : Prop :=
  ∀ i u u' v v', u ≠ u' → v ≠ v' →
    fixCount (σ (.inl (i, u, v)) * (σ (.inl (i, u', v)))⁻¹ * σ (.inl (i, u', v')) *
      (σ (.inl (i, u, v')))⁻¹) ≤ e

/-- **Theorem `thm:ineq`** for OpenAI's presentation, in counts: if every rectangular word fixes
at most `e` points with `(r-1)² e ≤ |Ω|`, then
`N r |Ω| ≤ 4 (2m + r|E|) |Ω| + 4 ∑_t |supp σ(θ_t)|`, i.e. `∑_t δ_t ≥ N r/4 - 2m - r|E| = Γ/4`
(`δ_t = |supp σ(θ_t)| / |Ω|`, the sum running over all triangle relators `t = (b, i, u, v)`). -/
theorem presentation_ineq (hq : r < q)
    (σ : (d.presentation hr).Edge → Equiv.Perm Ω) (e : ℕ)
    (hrect : RectFix d hr σ e) (he : (r - 1) ^ 2 * e ≤ Fintype.card Ω) :
    Fintype.card d.Label * r * Fintype.card Ω ≤
      4 * (2 * q ^ 20 + r * d.exceptional.card) * Fintype.card Ω +
        4 * ∑ b : d.BlockIndex, ∑ i : (d.block hr b).labels, ∑ u, ∑ v,
          triangleSupport d hr σ b i u v := by
  classical
  have h := approx_rank_ineq_sharp_reg (Ω := Ω) r q hq
    (lineIncidence d.mark (fun i => (d.direction i).rep))
    (fun z i => gridLagrange d.scalarGrid (d.mark i) z) d.exceptional
    (fun i u v => σ (.inl (i, u, v))) e
    (by intro i u u' v v' hu hv; exact hrect i u u' v v' hu hv) he
    (grid_line_certificate d.scalarGrid d.mark (fun i => (d.direction i).rep) d.marks_mem
      d.marks_injective (fun i => (d.direction i).rep_nonzero)
      (by simpa using d.degree_cutoff (two_hundred_le d)))
    (fun z => ∑ c : Bool, ∑ i : (d.block hr (z, c)).labels, ∑ u, ∑ v,
      triangleSupport d hr σ (z, c) i u v) (by
      intro z
      try dsimp only
      rw [Fintype.sum_bool]
      exact two_block_model_rank_le_sum _ _ (d.partition hr z).zero (d.partition hr z).one
        (d.partition hr z).disjoint (d.partition hr z).cover
        (fun u j => σ (.inr (.inl ⟨(z, false), u, j⟩)))
        (fun v j => σ (.inr (.inr ⟨(z, false), v, j⟩)))
        (fun u j => σ (.inr (.inl ⟨(z, true), u, j⟩)))
        (fun v j => σ (.inr (.inr ⟨(z, true), v, j⟩))))
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card] at h
  rw [← Fintype.sum_prod_type'] at h
  exact h

/-- Common core of `thm:quant`: the sharp obstruction for the presentation, budget left open. -/
theorem presentation_quant_core (hq : r < q)
    (σ : (d.presentation hr).Edge → Equiv.Perm Ω) (e k : ℕ)
    (hrect : RectFix d hr σ e) (he : (r - 1) ^ 2 * e ≤ Fintype.card Ω)
    (hk : ∀ b i u v, triangleSupport d hr σ b i u v ≤ k)
    (hbud : 4 * (2 * q ^ 20 + r * d.exceptional.card) * Fintype.card Ω +
      4 * ((∑ z, (lineIncidence d.mark (fun i => (d.direction i).rep) z).card) * (r * r * k)) <
        Fintype.card d.Label * r * Fintype.card Ω) : False := by
  classical
  apply no_model_of_line_blocks_sharp (Ω := Ω) r q hq d.scalarGrid d.mark
    (fun i => (d.direction i).rep) d.marks_mem d.marks_injective
    (fun i => (d.direction i).rep_nonzero)
    (by simpa only [Fintype.card_fin] using d.degree_cutoff (two_hundred_le d))
    d.exceptional (fun i u v => σ (.inl (i, u, v))) e k
    (by intro i u u' v v' hu hv; exact hrect i u u' v v' hu hv) he
    (by
      intro z hz
      let p := d.partition hr ⟨z, hz⟩
      refine ⟨p.zero, p.one, p.disjoint, p.cover, ?_, ?_⟩
      · exact ⟨fun u j => σ (.inr (.inl ⟨(⟨z, hz⟩, false), u, j⟩)),
          fun v j => σ (.inr (.inr ⟨(⟨z, hz⟩, false), v, j⟩)),
          fun i u v => hk (⟨z, hz⟩, false) i u v⟩
      · exact ⟨fun u j => σ (.inr (.inl ⟨(⟨z, hz⟩, true), u, j⟩)),
          fun v j => σ (.inr (.inr ⟨(⟨z, hz⟩, true), v, j⟩)),
          fun i u v => hk (⟨z, hz⟩, true) i u v⟩)
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using hbud

/-- **Theorem `thm:quant`, general data**: if every rectangular word fixes at most a fraction
`1/(r-1)²` of `Ω`, some triangle relator moves at least a fraction `ε₀ = 1/(4 r² N (q-1))`. -/
theorem presentation_quant (hq : r < q)
    (σ : (d.presentation hr).Edge → Equiv.Perm Ω) (e k : ℕ)
    (hrect : RectFix d hr σ e) (he : (r - 1) ^ 2 * e ≤ Fintype.card Ω)
    (hk : ∀ b i u v, triangleSupport d hr σ b i u v ≤ k)
    (hk' : 4 * r ^ 2 * Fintype.card d.Label * (q - 1) * k < Fintype.card Ω) : False :=
  presentation_quant_core d hr hq σ e k hrect he hk
    (budget_general r q (Fintype.card d.Label) (q ^ 20) d.exceptional.card
      (Fintype.card Ω) _ k d.budget
      (sum_card_lineIncidence_le q d.mark (fun i => (d.direction i).rep)) hk')

/-- **Theorem `thm:quant`, data of OpenAI's Lemma 2.2**, `ε₀ = 1/(6 r q)`, with `N ≥ m/(2C)`,
`r|E| ≤ m`, `100 C ≤ r` as hypotheses (paper: `C = 100²⁰`; not recorded by OAI's data). -/
theorem presentation_quant_lemma22 (hq : r < q) (C : ℕ) (hC : 0 < C)
    (hm : q ^ 20 ≤ 2 * C * Fintype.card d.Label)
    (hE : r * d.exceptional.card ≤ q ^ 20) (hr100 : 100 * C ≤ r)
    (σ : (d.presentation hr).Edge → Equiv.Perm Ω) (e k : ℕ)
    (hrect : RectFix d hr σ e) (he : (r - 1) ^ 2 * e ≤ Fintype.card Ω)
    (hk : ∀ b i u v, triangleSupport d hr σ b i u v ≤ k)
    (hk' : 6 * r * q * k < Fintype.card Ω) : False := by
  have hN : 0 < Fintype.card d.Label := by
    rcases Nat.eq_zero_or_pos (Fintype.card d.Label) with h | h
    · have hb := d.budget
      rw [h] at hb
      simp at hb
    · exact h
  exact presentation_quant_core d hr hq σ e k hrect he hk
    (budget_lemma22 C r q (Fintype.card d.Label) (q ^ 20) d.exceptional.card
      (Fintype.card Ω) _ k hN hm hE hr100 hC
      (sum_card_lineIncidence_le q d.mark (fun i => (d.direction i).rep)) hk')

end Presentation

end NonSofic
