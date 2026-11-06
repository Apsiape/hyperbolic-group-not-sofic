import FiniteLean.GroupTheory.OAI.GroupTheory.Hyperbolic.Incidence

/-! `200 ≤ q` follows from the data: if `q < 200` then `|S| = ⌊q/100⌋ ≤ 1`, so there is at most one
label (`marks_injective`, `marks_mem`); a regular point (`exists_regular`) then forces
`4 r² ≤ 1` (`degree`), i.e. `r = 0`, contradicting the budget. -/

namespace NonSofic

open OAI.Release075

theorem two_hundred_le {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) : 200 ≤ q := by
  classical
  by_contra hq
  have hS : d.scalarGrid.card ≤ 1 := by rw [d.grid_card]; omega
  have hN : Fintype.card d.Label ≤ 1 := by
    have h := Fintype.card_le_of_injective
      (fun i : d.Label => fun t : Fin 20 => (⟨d.mark i t, d.marks_mem i t⟩ : {x // x ∈ d.scalarGrid}))
      (fun i j h => d.marks_injective (funext fun t => congrArg Subtype.val (congrFun h t)))
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] at h
    exact h.trans ((Nat.pow_le_pow_left hS 20).trans (by simp))
  obtain ⟨z, hz⟩ := d.exists_regular
  have h4 : 4 * r ^ 2 ≤ 1 :=
    ((d.degree z hz).trans ((Finset.card_filter_le _ _).trans_eq Finset.card_univ)).trans hN
  have hr : r = 0 := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exact h
    · nlinarith [Nat.mul_le_mul h h]
  have hb := d.budget
  subst hr
  simp at hb

end NonSofic
