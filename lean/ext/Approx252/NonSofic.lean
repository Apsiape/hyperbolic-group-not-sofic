import Approx252.Sofic
import OAI.GroupTheory.Hyperbolic.Main

/-!
# A torsion-free word-hyperbolic group that is not sofic

The presented group `(d.presentation hr).GroupType` of `OAI.Release075` is not sofic: a sofic
approximation on the finite set of all words of length at most four in the generators and their
inverses would give an approximate permutation model contradicting `no_model_of_line_blocks`.
-/

namespace Approx252

open OAI.Release075
open scoped BigOperators Pointwise

theorem rel_of_eq {G : Type*} [Group G] {x l ρ : G} (h : x = l⁻¹ * ρ) : l * x * ρ⁻¹ = 1 := by
  rw [h]; group

theorem presentation_not_sofic {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)
    (hr : 0 < r) (hq : r < q) (hq200 : 200 ≤ q) : ¬ IsSofic (d.presentation hr).GroupType := by
  classical
  intro hsofic
  -- numerics of the fixed data
  have hbud := d.budget
  have hNle := d.card_labels_le
  have hN : 0 < Fintype.card d.Label := by
    rcases Nat.eq_zero_or_pos (Fintype.card d.Label) with h | h
    · rw [h] at hbud
      simp at hbud
    · exact h
  have hr2 : 2 ≤ r := by
    by_contra hlt
    have h1 : Fintype.card d.Label * r ≤ Fintype.card d.Label * 1 :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨i₀⟩ : Nonempty d.Label := Fintype.card_pos_iff.mp hN
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  -- the finite set `F`: all products of four elements of `gens ∪ gens⁻¹ ∪ {1}`
  let P := d.presentation hr
  let gens : Finset P.GroupType := Finset.univ.image P.edge
  let F₁ : Finset P.GroupType := gens ∪ gens.image (fun g => g⁻¹) ∪ {1}
  let F : Finset P.GroupType := F₁ * F₁ * F₁ * F₁
  have h1F₁ : (1 : P.GroupType) ∈ F₁ := Finset.mem_union_right _ (Finset.mem_singleton_self 1)
  have hgenF₁ : ∀ e, P.edge e ∈ F₁ := fun e =>
    Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem P.edge (Finset.mem_univ e)))
  have hinvF₁ : ∀ e, (P.edge e)⁻¹ ∈ F₁ := fun e =>
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun g => g⁻¹) (Finset.mem_image_of_mem P.edge (Finset.mem_univ e))))
  have hF4 : ∀ a ∈ F₁, ∀ b ∈ F₁, ∀ c ∈ F₁, ∀ e ∈ F₁, a * b * c * e ∈ F :=
    fun a ha b hb c hc e he =>
      Finset.mul_mem_mul (Finset.mul_mem_mul (Finset.mul_mem_mul ha hb) hc) he
  have hF3 : ∀ a ∈ F₁, ∀ b ∈ F₁, ∀ c ∈ F₁, a * b * c ∈ F := fun a ha b hb c hc => by
    have h := hF4 a ha b hb c hc 1 h1F₁
    rwa [mul_one] at h
  have hF2 : ∀ a ∈ F₁, ∀ b ∈ F₁, a * b ∈ F := fun a ha b hb => by
    have h := hF3 a ha b hb 1 h1F₁
    rwa [mul_one] at h
  have hF1 : ∀ a ∈ F₁, a ∈ F := fun a ha => by
    have h := hF2 a ha 1 h1F₁
    rwa [mul_one] at h
  have h1F : (1 : P.GroupType) ∈ F := hF1 1 h1F₁
  -- the accuracy
  let N : ℕ := Fintype.card d.Label
  let M : ℕ := 40 * (N * q * r ^ 2)
  have hNqr : 0 < N * q * r ^ 2 := Nat.mul_pos (Nat.mul_pos hN hqpos) (pow_pos hr 2)
  have hM40 : 40 ≤ M := Nat.le_mul_of_pos_right 40 hNqr
  have hMpos : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  let ε : ℝ := 1 / M
  have hε : 0 < ε := by positivity
  have hε1 : ε < 1 := by
    rw [div_lt_one hMR]
    have : (40 : ℝ) ≤ M := by exact_mod_cast hM40
    linarith
  obtain ⟨n, φ, hmul, hsep, hnpos⟩ := hsofic.exists_approx F ε hε
  -- the model and its defect counts
  let x : d.Label → Fin r → Fin r → Equiv.Perm (Fin n) := fun i u v => φ (P.x i u v)
  let B : ℝ := ε * n
  have hBnn : 0 ≤ B := mul_nonneg hε.le (Nat.cast_nonneg n)
  let k : ℕ := Nat.floor (5 * B)
  let e : ℕ := Nat.floor (8 * B)
  have hk : (k : ℝ) ≤ 5 * B := Nat.floor_le (by positivity)
  have he : (e : ℝ) ≤ 8 * B := Nat.floor_le (by positivity)
  have hrect := d.rectangular_nontriviality hr
  -- `n > 0`, from one nontrivial rectangular word in `F`
  let u₀ : Fin r := ⟨0, by omega⟩
  let u₁ : Fin r := ⟨1, by omega⟩
  have hu01 : u₀ ≠ u₁ := by simp [u₀, u₁, Fin.ext_iff]
  have hw0 : P.x i₀ u₀ u₀ * (P.x i₀ u₁ u₀)⁻¹ * P.x i₀ u₁ u₁ * (P.x i₀ u₀ u₁)⁻¹ ≠ 1 :=
    hrect i₀ u₀ u₁ u₀ u₁ hu01 hu01
  have hw0F : P.x i₀ u₀ u₀ * (P.x i₀ u₁ u₀)⁻¹ * P.x i₀ u₁ u₁ * (P.x i₀ u₀ u₁)⁻¹ ∈ F :=
    hF4 _ (hgenF₁ _) _ (hinvF₁ _) _ (hgenF₁ _) _ (hinvF₁ _)
  have hn : 0 < n := hnpos _ hw0F hw0 hε1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- the obstruction
  apply no_model_of_line_blocks (Ω := Fin n) r q hq d.scalarGrid d.mark
    (fun i => (d.direction i).rep) d.marks_mem d.marks_injective
    (fun i => (d.direction i).rep_nonzero)
    (by simpa only [Fintype.card_fin] using d.degree_cutoff hq200)
    d.exceptional x e k ?_ ?_ ?_ ?_
  · -- rectangles are almost free
    intro i u u' v v' hu hv
    have hne := hrect i u u' v v' hu hv
    have hb := rectangle_fixCount_le φ F B hmul hsep h1F (P.x i u v) (P.x i u' v) (P.x i u' v')
      (P.x i u v') hne
      (hF1 _ (hgenF₁ _)) (hF1 _ (hgenF₁ _)) (hF1 _ (hinvF₁ _)) (hF1 _ (hgenF₁ _))
      (hF1 _ (hgenF₁ _)) (hF1 _ (hinvF₁ _))
      (hF2 _ (hgenF₁ _) _ (hinvF₁ _)) (hF3 _ (hgenF₁ _) _ (hinvF₁ _) _ (hgenF₁ _))
      (hF4 _ (hgenF₁ _) _ (hinvF₁ _) _ (hgenF₁ _) _ (hinvF₁ _))
    exact Nat.le_floor hb
  · -- `r² e ≤ n`
    rw [Fintype.card_fin]
    have hle : (8 * r ^ 2 : ℕ) ≤ M := by
      have : 8 * r ^ 2 ≤ 40 * (N * q * r ^ 2) := by
        calc 8 * r ^ 2 = 8 * (1 * 1 * r ^ 2) := by ring
          _ ≤ 40 * (N * q * r ^ 2) := by gcongr <;> omega
      exact this
    have hle' : (8 * (r : ℝ) ^ 2) ≤ M := by exact_mod_cast hle
    have h8 : 8 * (r : ℝ) ^ 2 * ε ≤ 1 := by
      rw [show ε = 1 / (M : ℝ) from rfl, mul_one_div]
      exact (div_le_one hMR).mpr hle'
    have hreal : (r : ℝ) ^ 2 * e ≤ n := by
      calc (r : ℝ) ^ 2 * e ≤ (r : ℝ) ^ 2 * (8 * B) := by gcongr
        _ = (8 * (r : ℝ) ^ 2 * ε) * n := by simp only [B]; ring
        _ ≤ 1 * n := by gcongr
        _ = n := one_mul _
    exact_mod_cast hreal
  · -- the two Cartesian blocks at a regular point, with approximate relations
    intro z hz
    let p := d.partition hr ⟨z,hz⟩
    refine ⟨p.zero, p.one, p.disjoint, p.cover, ?_, ?_⟩
    · refine ⟨fun u j => φ (P.l (⟨z,hz⟩,false) u j), fun v j => φ (P.rr (⟨z,hz⟩,false) v j), ?_⟩
      intro i u v
      have hrel := P.triangle_relation (⟨z,hz⟩,false) i u v
      have hb := relator_support_le φ F B hmul h1F _ _ _ (rel_of_eq hrel)
        (hF1 _ (hgenF₁ _)) (hF1 _ (hgenF₁ _)) (hF2 _ (hgenF₁ _) _ (hgenF₁ _))
        (hF1 _ (hgenF₁ _)) (hF1 _ (hinvF₁ _))
      exact Nat.le_floor hb
    · refine ⟨fun u j => φ (P.l (⟨z,hz⟩,true) u j), fun v j => φ (P.rr (⟨z,hz⟩,true) v j), ?_⟩
      intro i u v
      have hrel := P.triangle_relation (⟨z,hz⟩,true) i u v
      have hb := relator_support_le φ F B hmul h1F _ _ _ (rel_of_eq hrel)
        (hF1 _ (hgenF₁ _)) (hF1 _ (hgenF₁ _)) (hF2 _ (hgenF₁ _) _ (hgenF₁ _))
        (hF1 _ (hgenF₁ _)) (hF1 _ (hinvF₁ _))
      exact Nat.le_floor hb
  · -- the budget
    rw [Fintype.card_fin]
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    have hS := sum_card_lineIncidence_le q d.mark (fun i => (d.direction i).rep)
    have hS' : ((∑ z, (lineIncidence d.mark (fun i => (d.direction i).rep) z).card : ℕ) : ℝ) ≤
        (N : ℝ) * q := by
      have : (∑ z, (lineIncidence d.mark (fun i => (d.direction i).rep) z).card) ≤ N * q :=
        hS.trans (Nat.mul_le_mul_left _ (Nat.sub_le q 1))
      exact_mod_cast this
    have hA : (4 * (2 * (q : ℝ) ^ 20 + (r : ℝ) * (d.exceptional.card : ℝ))) + 1 ≤
        (N : ℝ) * r := by
      have : 4 * (2 * q ^ 20 + r * d.exceptional.card) + 1 ≤ N * r := hbud
      exact_mod_cast this
    have hA' : (4 * (2 * (q : ℝ) ^ 20 + (r : ℝ) * (d.exceptional.card : ℝ))) * n + n ≤
        (N : ℝ) * r * n := by
      calc (4 * (2 * (q : ℝ) ^ 20 + (r : ℝ) * (d.exceptional.card : ℝ))) * n + n
          = ((4 * (2 * (q : ℝ) ^ 20 + (r : ℝ) * (d.exceptional.card : ℝ))) + 1) * n := by ring
        _ ≤ (N : ℝ) * r * n := mul_le_mul_of_nonneg_right hA hnR.le
    have h20 : 20 * (N : ℝ) * q * (r : ℝ) ^ 2 * ε ≤ 1 / 2 := by
      rw [show ε = 1 / (M : ℝ) from rfl, mul_one_div, div_le_iff₀ hMR]
      have hMeq : ((20 * (N * q * r ^ 2) : ℕ) : ℝ) * 2 = M := by
        have : 20 * (N * q * r ^ 2) * 2 = M := by simp only [M]; ring
        exact_mod_cast this
      push_cast at hMeq
      linarith
    have hprod : (4 : ℝ) * (((∑ z, (lineIncidence d.mark (fun i => (d.direction i).rep) z).card :
        ℕ) : ℝ) * ((r : ℝ) * (r : ℝ) * (k : ℝ))) ≤ 1 / 2 * n := by
      calc (4 : ℝ) * (((∑ z, (lineIncidence d.mark (fun i => (d.direction i).rep) z).card :
            ℕ) : ℝ) * ((r : ℝ) * (r : ℝ) * (k : ℝ)))
          ≤ 4 * (((N : ℝ) * q) * ((r : ℝ) * (r : ℝ) * (5 * B))) := by gcongr
        _ = (20 * (N : ℝ) * q * (r : ℝ) ^ 2 * ε) * n := by simp only [B]; ring
        _ ≤ 1 / 2 * n := mul_le_mul_of_nonneg_right h20 hnR.le
    have goalR : (4 * (2 * (q : ℝ) ^ 20 + (r : ℝ) * (d.exceptional.card : ℝ))) * (n : ℝ) +
        (4 : ℝ) * (((∑ z, (lineIncidence d.mark (fun i => (d.direction i).rep) z).card :
          ℕ) : ℝ) * ((r : ℝ) * (r : ℝ) * (k : ℝ))) < (N : ℝ) * (r : ℝ) * (n : ℝ) := by
      linarith
    exact_mod_cast goalR

/-- **Theorem.** There is a torsion-free word-hyperbolic group that is not sofic. -/
theorem exists_torsionFree_wordHyperbolic_not_sofic :
    ∃ (G : Type) (_ : Group G), TorsionFree G ∧ WordHyperbolic G ∧ ¬ IsSofic G := by
  obtain ⟨q,r,hq,hr,hrq,hrb,⟨d⟩⟩ := exists_markedLineData
  let : Fact q.Prime := ⟨hq⟩
  have hq200 : 200 ≤ q := by
    have hb : 200 ≤ 100*100^20 := by norm_num
    omega
  exact ⟨(d.presentation hr).GroupType, inferInstance,
    d.presentation_torsionFree hr, d.presentation_wordHyperbolic hr,
    presentation_not_sofic d hr hrq hq200⟩

end Approx252
