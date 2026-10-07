import OAI.GroupTheory.Hyperbolic.Main

/-! Audit of the imported inputs for OpenAI math family 252.
This file does not formalize the non-soficity transfer. -/

open OAI.Release075

-- Statements as elaborated
#check @OAI.Release075.main
#check @OAI.Release075.TorsionFree
#check @OAI.Release075.WordHyperbolic
#check @OAI.Release075.BlockPresentation.relators
#check @OAI.Release075.BlockPresentation.triangleWord
#check @OAI.Release075.BlockPresentation.triangle_relation
#check @OAI.Release075.MarkedLineData.RectangularNontriviality
#check @OAI.Release075.MarkedLineData.rectangular_nontriviality
#check @OAI.Release075.RectanglesSurvive
#check @OAI.Release075.MarkedLineData.budget
#check @OAI.Release075.exists_markedLineData
#check @OAI.Release075.grid_line_certificate
#check @OAI.Release075.rank_budget_of_line_certificate
#check @OAI.Release075.rank_reduction_half
#check @OAI.Release075.finite_quotient_rank_obstruction
#check @OAI.Release075.not_residuallyFinite_of_line_blocks
#check @OAI.Release075.MarkedLineData.presentation_torsionFree
#check @OAI.Release075.MarkedLineData.presentation_finiteOrder_eq_one
#check @OAI.Release075.MarkedLineData.presentation_wordHyperbolic
#check @OAI.Release075.MarkedLineData.presentation_cochainBound
#check @OAI.Release075.MarkedLineData.actual_presentation_not_residuallyFinite
#check @OAI.Release075.MarkedLineData.presentation_not_residuallyFinite

-- Axiom audit
#print axioms OAI.Release075.main
#print axioms OAI.Release075.BlockPresentation.triangle_relation
#print axioms OAI.Release075.MarkedLineData.rectangular_nontriviality
#print axioms OAI.Release075.MarkedLineData.budget
#print axioms OAI.Release075.exists_markedLineData
#print axioms OAI.Release075.large_prime_grid_outcome
#print axioms OAI.Release075.incidence_numeric_budget
#print axioms OAI.Release075.grid_line_certificate
#print axioms OAI.Release075.rank_budget_of_line_certificate
#print axioms OAI.Release075.rank_reduction_half
#print axioms OAI.Release075.nonsingular_rank_reduction_half
#print axioms OAI.Release075.finite_quotient_rank_obstruction
#print axioms OAI.Release075.not_residuallyFinite_of_line_blocks
#print axioms OAI.Release075.quotientMatrix_rank_mod_lower
#print axioms OAI.Release075.two_block_quotient_rank_le
#print axioms OAI.Release075.MarkedLineData.presentation_torsionFree
#print axioms OAI.Release075.MarkedLineData.presentation_finiteOrder_eq_one
#print axioms OAI.Release075.MarkedLineData.presentation_wordHyperbolic
#print axioms OAI.Release075.MarkedLineData.presentation_cochainBound
#print axioms OAI.Release075.MarkedLineData.actual_presentation_not_residuallyFinite
#print axioms OAI.Release075.MarkedLineData.presentation_not_residuallyFinite

/-! Comparator emulation: the challenge file's definitions, re-entered verbatim in a fresh
namespace, are definitionally the repository's, and the challenge statement follows. -/
namespace Challenge252
universe u

def TorsionFree (G : Type u) [Group G] : Prop :=
  ∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1

def Geodesic {V : Type u} (X : SimpleGraph V) {x y : V} (p : X.Walk x y) : Prop :=
  p.length = X.dist x y

def SideThin {V : Type u} (X : SimpleGraph V) (δ : ℕ) {x y z : V}
    (p : X.Walk x y) (q : X.Walk y z) (r : X.Walk z x) : Prop :=
  ∀ a ∈ p.support, ∃ b, (b ∈ q.support ∨ b ∈ r.support) ∧ X.dist a b ≤ δ

def WordHyperbolic (G : Type u) [Group G] : Prop :=
  ∃ S : Set G, S.Finite ∧ (SimpleGraph.mulCayley S).Connected ∧
    ∃ δ : ℕ, ∀ (x y z : G)
      (p : (SimpleGraph.mulCayley S).Walk x y)
      (q : (SimpleGraph.mulCayley S).Walk y z)
      (r : (SimpleGraph.mulCayley S).Walk z x),
      Geodesic (SimpleGraph.mulCayley S) p →
      Geodesic (SimpleGraph.mulCayley S) q →
      Geodesic (SimpleGraph.mulCayley S) r →
      SideThin (SimpleGraph.mulCayley S) δ p q r ∧
      SideThin (SimpleGraph.mulCayley S) δ q r p ∧
      SideThin (SimpleGraph.mulCayley S) δ r p q

example (G : Type u) [Group G] : TorsionFree G = OAI.Release075.TorsionFree G := rfl
example (G : Type u) [Group G] : WordHyperbolic G = OAI.Release075.WordHyperbolic G := rfl

theorem main : ∃ (G : Type) (_ : Group G),
    TorsionFree G ∧ WordHyperbolic G ∧ ¬ Group.ResiduallyFinite G :=
  OAI.Release075.main

end Challenge252

#print axioms Challenge252.main

/-! Item (e) in the 0/1 form: a 0/1 integer matrix with exactly r ones per row
satisfies the row-norm hypothesis of `rank_reduction_half`. -/
theorem zeroOne_rank_reduction {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ ℤ) (r : ℕ) (hr : 1 ≤ r)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1)
    (hones : ∀ i, (Finset.univ.filter (fun j => M i j = 1)).card = r)
    (q : ℕ) [Fact q.Prime] (hqr : r < q) :
    (M.map (Int.cast : ℤ → ℝ)).rank ≤ 2 * (M.map (Int.cast : ℤ → ZMod q)).rank := by
  classical
  have hrow : ∀ i, ∑ j, (M i j : ℝ) ^ 2 ≤ (r : ℝ) := by
    intro i
    have hsq : ∀ j, (M i j : ℝ) ^ 2 = if M i j = 1 then 1 else 0 := by
      intro j
      rcases h01 i j with h | h <;> simp [h]
    simp only [hsq, Finset.sum_boole]
    exact_mod_cast (hones i).le
  exact rank_reduction_half M (r : ℝ) (by exact_mod_cast hr) hrow q (by exact_mod_cast hqr)

#print axioms zeroOne_rank_reduction
