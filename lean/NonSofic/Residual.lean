import Approx252.NonSofic
import FiniteLean.GroupTheory.Sofic.Closure
import NonSofic.DataBounds

/-!
# Lemma `lem:models` for a homomorphism, and Corollary `cor:residual`

`presentation_hom_not_sofic` is `Approx252.presentation_not_sofic` with the identity of `G`
replaced by an arbitrary homomorphism `π : G →* H` under which every rectangular word survives
(paper, Lemma `lem:models` with Theorem `thm:quant`): such an `H` is not sofic.  The proof is
the original one, applied to `φ ∘ π` and to the images under `π` of the finite set of words of
length at most four; the triangle relations are transported by `π`.

`exists_rect_word_killed_by_sofic` is Corollary `cor:residual`: one fixed rectangular word
`w₀ ≠ 1` dies under every homomorphism from `G` to a sofic group (in a fixed universe `u`).
-/

namespace NonSofic

open OAI.Release075 Approx252
open scoped BigOperators Pointwise

theorem presentation_hom_not_sofic {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)
    (hr : 0 < r) (hq : r < q) {H : Type*} [Group H]
    (π : (d.presentation hr).GroupType →* H)
    (hπ : ∀ i u u' v v', u ≠ u' → v ≠ v' →
      π ((d.presentation hr).x i u v) * (π ((d.presentation hr).x i u' v))⁻¹ *
        π ((d.presentation hr).x i u' v') * (π ((d.presentation hr).x i u v'))⁻¹ ≠ 1) :
    ¬ IsSofic H := by
  classical
  have hq200 : 200 ≤ q := two_hundred_le d
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
  let gens : Finset H := Finset.univ.image (fun e => π (P.edge e))
  let F₁ : Finset H := gens ∪ gens.image (fun g => g⁻¹) ∪ {1}
  let F : Finset H := F₁ * F₁ * F₁ * F₁
  have h1F₁ : (1 : H) ∈ F₁ := Finset.mem_union_right _ (Finset.mem_singleton_self 1)
  have hgenF₁ : ∀ e, π (P.edge e) ∈ F₁ := fun e =>
    Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem (fun e => π (P.edge e)) (Finset.mem_univ e)))
  have hinvF₁ : ∀ e, (π (P.edge e))⁻¹ ∈ F₁ := fun e =>
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun g => g⁻¹)
        (Finset.mem_image_of_mem (fun e => π (P.edge e)) (Finset.mem_univ e))))
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
  have h1F : (1 : H) ∈ F := hF1 1 h1F₁
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
  let x : d.Label → Fin r → Fin r → Equiv.Perm (Fin n) := fun i u v => φ (π (P.x i u v))
  let B : ℝ := ε * n
  have hBnn : 0 ≤ B := mul_nonneg hε.le (Nat.cast_nonneg n)
  let k : ℕ := Nat.floor (5 * B)
  let e : ℕ := Nat.floor (8 * B)
  have hk : (k : ℝ) ≤ 5 * B := Nat.floor_le (by positivity)
  have he : (e : ℝ) ≤ 8 * B := Nat.floor_le (by positivity)
  have hrect := hπ
  -- `n > 0`, from one nontrivial rectangular word in `F`
  let u₀ : Fin r := ⟨0, by omega⟩
  let u₁ : Fin r := ⟨1, by omega⟩
  have hu01 : u₀ ≠ u₁ := by simp [u₀, u₁, Fin.ext_iff]
  have hw0 : π (P.x i₀ u₀ u₀) * (π (P.x i₀ u₁ u₀))⁻¹ * π (P.x i₀ u₁ u₁) *
      (π (P.x i₀ u₀ u₁))⁻¹ ≠ 1 :=
    hrect i₀ u₀ u₁ u₀ u₁ hu01 hu01
  have hw0F : π (P.x i₀ u₀ u₀) * (π (P.x i₀ u₁ u₀))⁻¹ * π (P.x i₀ u₁ u₁) *
      (π (P.x i₀ u₀ u₁))⁻¹ ∈ F :=
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
    have hb := rectangle_fixCount_le φ F B hmul hsep h1F (π (P.x i u v)) (π (P.x i u' v))
      (π (P.x i u' v')) (π (P.x i u v')) hne
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
    · refine ⟨fun u j => φ (π (P.l (⟨z,hz⟩,false) u j)), fun v j => φ (π (P.rr (⟨z,hz⟩,false) v j)), ?_⟩
      intro i u v
      have hrel := congrArg π (P.triangle_relation (⟨z,hz⟩,false) i u v)
      rw [map_mul, map_inv] at hrel
      have hb := relator_support_le φ F B hmul h1F _ _ _ (rel_of_eq hrel)
        (hF1 _ (hgenF₁ _)) (hF1 _ (hgenF₁ _)) (hF2 _ (hgenF₁ _) _ (hgenF₁ _))
        (hF1 _ (hgenF₁ _)) (hF1 _ (hinvF₁ _))
      exact Nat.le_floor hb
    · refine ⟨fun u j => φ (π (P.l (⟨z,hz⟩,true) u j)), fun v j => φ (π (P.rr (⟨z,hz⟩,true) v j)), ?_⟩
      intro i u v
      have hrel := congrArg π (P.triangle_relation (⟨z,hz⟩,true) i u v)
      rw [map_mul, map_inv] at hrel
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


/-- The index set of the rectangular words: `(i, u, u', v, v')` with `u ≠ u'`, `v ≠ v'`. -/
abbrev RectIndex {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) : Type :=
  {x : d.Label × Fin r × Fin r × Fin r × Fin r // x.2.1 ≠ x.2.2.1 ∧ x.2.2.2.1 ≠ x.2.2.2.2}

/-- The rectangular word `w_{i,u,u',v,v'} = x_{iuv} x_{iu'v}⁻¹ x_{iu'v'} x_{iuv'}⁻¹`. -/
noncomputable def rectWord {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
    (x : RectIndex d) : (d.presentation hr).GroupType :=
  (d.presentation hr).x x.val.1 x.val.2.1 x.val.2.2.2.1 *
    ((d.presentation hr).x x.val.1 x.val.2.2.1 x.val.2.2.2.1)⁻¹ *
    (d.presentation hr).x x.val.1 x.val.2.2.1 x.val.2.2.2.2 *
    ((d.presentation hr).x x.val.1 x.val.2.1 x.val.2.2.2.2)⁻¹

theorem rectWord_ne_one {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
    (x : RectIndex d) : rectWord d hr x ≠ 1 :=
  d.rectangular_nontriviality hr x.val.1 x.val.2.1 x.val.2.2.1 x.val.2.2.2.1 x.val.2.2.2.2
    x.property.1 x.property.2

universe u

/-- **Corollary `cor:residual`.**  Some fixed rectangular word `w₀ ≠ 1` of `G` lies in the kernel
of every homomorphism from `G` to a sofic group (of the universe `u`). -/
theorem exists_rect_word_killed_by_sofic {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)
    (hr : 0 < r) (hq : r < q) :
    ∃ x : RectIndex d, rectWord d hr x ≠ 1 ∧
      ∀ (H : Type u) [Group H], IsSofic H → ∀ π : (d.presentation hr).GroupType →* H,
        π (rectWord d hr x) = 1 := by
  classical
  by_contra hcon
  have hsurv : ∀ x : RectIndex d, ∃ (H : Type u) (_ : Group H), IsSofic H ∧
      ∃ π : (d.presentation hr).GroupType →* H, π (rectWord d hr x) ≠ 1 := by
    intro x
    by_contra hx
    apply hcon
    refine ⟨x, rectWord_ne_one d hr x, ?_⟩
    intro H _ hs π
    by_contra hπ
    exact hx ⟨H, inferInstance, hs, π, hπ⟩
  choose H hH hs π hπ using hsurv
  letI : ∀ x, Group (H x) := hH
  let πall : (d.presentation hr).GroupType →* (∀ x, H x) := MonoidHom.pi π
  have hsP : IsSofic (∀ x, H x) := isSofic_pi hs
  apply presentation_hom_not_sofic d hr hq πall ?_ hsP
  intro i u u' v v' hu hv hw
  apply hπ ⟨(i, u, u', v, v'), hu, hv⟩
  have h := congrFun hw ⟨(i, u, u', v, v'), hu, hv⟩
  simpa [rectWord, πall, map_mul, map_inv] using h

/-- In particular every quotient of `G` in which all rectangular words survive is non-sofic. -/
theorem quotient_not_sofic {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)
    (hr : 0 < r) (hq : r < q) {H : Type*} [Group H]
    (π : (d.presentation hr).GroupType →* H)
    (hπ : ∀ x : RectIndex d, π (rectWord d hr x) ≠ 1) : ¬ IsSofic H := by
  apply presentation_hom_not_sofic d hr hq π
  intro i u u' v v' hu hv
  have h := hπ ⟨(i, u, u', v, v'), hu, hv⟩
  simpa [rectWord, map_mul, map_inv] using h

/-- The witness of `cor:residual`, chosen once (from the statement for groups in `Type`). -/
noncomputable def residualWitness {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)
    (hr : 0 < r) (hq : r < q) : RectIndex d :=
  (exists_rect_word_killed_by_sofic.{0} d hr hq).choose

theorem residualWitness_ne_one {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)
    (hr : 0 < r) (hq : r < q) : rectWord d hr (residualWitness d hr hq) ≠ 1 :=
  (exists_rect_word_killed_by_sofic.{0} d hr hq).choose_spec.1

/-- **Corollary `cor:residual`, universe-independent witness.**  The single word
`w₀ = rectWord (residualWitness d hr hq) ≠ 1` dies under every homomorphism to a sofic group in
any universe: `G ⧸ ker π` lies in `Type` and embeds in `H`, so it is sofic. -/
theorem residualWitness_killed {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)
    (hr : 0 < r) (hq : r < q) (H : Type u) [Group H] (hH : IsSofic H)
    (π : (d.presentation hr).GroupType →* H) :
    π (rectWord d hr (residualWitness d hr hq)) = 1 := by
  have hQ : IsSofic ((d.presentation hr).GroupType ⧸ π.ker) :=
    IsSofic.of_injective (QuotientGroup.kerLift π) (QuotientGroup.kerLift_injective π) hH
  have h := (exists_rect_word_killed_by_sofic.{0} d hr hq).choose_spec.2 _ hQ
    (QuotientGroup.mk' π.ker)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  exact MonoidHom.mem_ker.mp h

/-- `cor:residual` with the witness chosen before the universe of the target. -/
theorem exists_rect_word_killed_by_sofic_univ {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)
    (hr : 0 < r) (hq : r < q) :
    ∃ x : RectIndex d, x = residualWitness d hr hq ∧ rectWord d hr x ≠ 1 ∧
      ∀ (H : Type u) [Group H], IsSofic H → ∀ π : (d.presentation hr).GroupType →* H,
        π (rectWord d hr x) = 1 :=
  ⟨_, rfl, residualWitness_ne_one d hr hq, fun H _ hH π => residualWitness_killed d hr hq H hH π⟩

end NonSofic
