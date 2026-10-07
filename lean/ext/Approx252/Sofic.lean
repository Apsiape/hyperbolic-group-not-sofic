import Approx252.PermModel

/-!
# Sofic groups and the bridge to approximate permutation models

`IsSofic G` is the standard metric definition (Gromov, Weiss; Elek–Szabó; Pestov's survey): for
every finite `F ⊆ G` and `ε > 0` there are `n` and `φ : G → Sym(n)` with
`d_H(φ(gh), φ(g)φ(h)) ≤ ε` for `g, h ∈ F` and `d_H(φ(g), 1) ≥ 1 - ε` for `g ∈ F ∖ {1}`, where
`d_H` is the normalized Hamming distance.  Non-strict inequalities are used, which is the weakest
of the standard equivalent variants (so `¬ IsSofic` is the strongest).

The bridge lemmas convert an `(F, ε)`-approximation into exact counts: every triangle relator
`l x ρ⁻¹ = 1` of `G` gives a permutation `φ(l) φ(x) φ(ρ)⁻¹` moving at most `5 ε n` points, and
every nontrivial word `x₁ x₂⁻¹ x₃ x₄⁻¹ ∈ F` gives a permutation
`φ(x₁) φ(x₂)⁻¹ φ(x₃) φ(x₄)⁻¹` fixing at most `8 ε n` points.
-/

namespace Approx252

open scoped BigOperators

section Hamming

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The number of points at which two permutations disagree. -/
def dis (σ τ : Equiv.Perm Ω) : ℕ := (σ⁻¹ * τ).support.card

theorem dis_comm (σ τ : Equiv.Perm Ω) : dis σ τ = dis τ σ := by
  unfold dis
  rw [← Equiv.Perm.support_inv, mul_inv_rev, inv_inv]

theorem dis_le_card (σ τ : Equiv.Perm Ω) : dis σ τ ≤ Fintype.card Ω :=
  Finset.card_le_univ _

theorem dis_triangle (σ τ υ : Equiv.Perm Ω) : dis σ υ ≤ dis σ τ + dis τ υ := by
  unfold dis
  have h : σ⁻¹ * υ = (σ⁻¹ * τ) * (τ⁻¹ * υ) := by group
  rw [h]
  exact (Finset.card_le_card (Equiv.Perm.support_mul_le _ _)).trans (Finset.card_union_le _ _)

theorem dis_mul_left (ρ σ τ : Equiv.Perm Ω) : dis (ρ * σ) (ρ * τ) = dis σ τ := by
  unfold dis
  have h : (ρ * σ)⁻¹ * (ρ * τ) = σ⁻¹ * τ := by group
  rw [h]

theorem dis_mul_right (σ τ ρ : Equiv.Perm Ω) : dis (σ * ρ) (τ * ρ) = dis σ τ := by
  unfold dis
  have h : (σ * ρ)⁻¹ * (τ * ρ) = ρ⁻¹ * (σ⁻¹ * τ) * ρ⁻¹⁻¹ := by group
  rw [h, Equiv.Perm.card_support_conj]

theorem dis_one_right (σ : Equiv.Perm Ω) : dis σ 1 = σ.support.card := by
  simp [dis, Equiv.Perm.support_inv]

theorem fixCount_le_fixCount_add_dis (σ τ : Equiv.Perm Ω) :
    fixCount σ ≤ fixCount τ + dis σ τ := by
  unfold fixCount dis
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.Perm.mem_support, Equiv.Perm.mul_apply]
  by_cases h : τ c = c
  · exact Or.inl h
  · right
    intro h'
    apply h
    rw [Equiv.Perm.inv_eq_iff_eq] at h'
    exact h'.trans hc

end Hamming

/-- Normalized Hamming distance on `Sym(n)`. -/
noncomputable def hammingDist {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : ℝ := (dis σ τ : ℝ) / n

/-- **Sofic groups** (standard metric definition).  For every finite set `F ⊆ G` and every
`ε > 0` there is an `(F, ε)`-almost homomorphism into a finite symmetric group: almost
multiplicative on `F` in normalized Hamming distance, and mapping each `g ∈ F ∖ {1}` to a
permutation at normalized Hamming distance at least `1 - ε` from the identity. -/
def IsSofic (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (φ : G → Equiv.Perm (Fin n)),
    (∀ g ∈ F, ∀ h ∈ F, hammingDist (φ (g * h)) (φ g * φ h) ≤ ε) ∧
    (∀ g ∈ F, g ≠ 1 → 1 - ε ≤ hammingDist (φ g) 1)

/-- A sofic approximation in counting form. -/
theorem IsSofic.exists_approx {G : Type*} [Group G] (hG : IsSofic G) (F : Finset G) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ (n : ℕ) (φ : G → Equiv.Perm (Fin n)),
      (∀ g ∈ F, ∀ h ∈ F, (dis (φ (g * h)) (φ g * φ h) : ℝ) ≤ ε * n) ∧
      (∀ g ∈ F, g ≠ 1 → (fixCount (φ g) : ℝ) ≤ ε * n) ∧
      (∀ g ∈ F, g ≠ 1 → ε < 1 → 0 < n) := by
  obtain ⟨n, φ, hmul, hsep⟩ := hG F ε hε
  refine ⟨n, φ, ?_, ?_, ?_⟩
  · intro g hg h hh
    have hd := hmul g hg h hh
    unfold hammingDist at hd
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : dis (φ (g * h)) (φ g * φ h) = 0 := by
        have := dis_le_card (φ (g * h)) (φ g * φ h)
        simpa using this
      simp [h0]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rwa [div_le_iff₀ hn'] at hd
  · intro g hg hg1
    have hd := hsep g hg hg1
    unfold hammingDist at hd
    rw [dis_one_right] at hd
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : fixCount (φ g) = 0 := by
        have := fixCount_le_card (φ g)
        simpa using this
      simp [h0]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [le_div_iff₀ hn'] at hd
      have hfix := fixCount_add_card_support (φ g)
      rw [Fintype.card_fin] at hfix
      have hfix' : (fixCount (φ g) : ℝ) + ((φ g).support.card : ℝ) = n := by
        exact_mod_cast hfix
      linarith
  · intro g hg hg1 hε1
    have hd := hsep g hg hg1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      unfold hammingDist at hd
      simp at hd
      linarith
    · exact hn

section Words

variable {G : Type*} [Group G] {n : ℕ}

theorem dis_one_le (φ : G → Equiv.Perm (Fin n)) (F : Finset G) (B : ℝ)
    (hmul : ∀ g ∈ F, ∀ h ∈ F, (dis (φ (g * h)) (φ g * φ h) : ℝ) ≤ B)
    (h1 : (1 : G) ∈ F) : (dis (φ 1) 1 : ℝ) ≤ B := by
  have h := hmul 1 h1 1 h1
  rw [one_mul] at h
  have e : dis (φ 1) (φ 1 * φ 1) = dis 1 (φ 1) := by
    rw [← dis_mul_left (φ 1) 1 (φ 1), mul_one]
  rw [e, dis_comm] at h
  exact h

theorem dis_inv_le (φ : G → Equiv.Perm (Fin n)) (F : Finset G) (B : ℝ)
    (hmul : ∀ g ∈ F, ∀ h ∈ F, (dis (φ (g * h)) (φ g * φ h) : ℝ) ≤ B)
    (h1 : (1 : G) ∈ F) (g : G) (hg : g ∈ F) (hgi : g⁻¹ ∈ F) :
    (dis (φ g⁻¹) (φ g)⁻¹ : ℝ) ≤ 2 * B := by
  have h := hmul g⁻¹ hgi g hg
  rw [inv_mul_cancel] at h
  have h0 := dis_one_le φ F B hmul h1
  have htri := dis_triangle (φ g⁻¹ * φ g) (φ 1) 1
  rw [dis_comm (φ g⁻¹ * φ g) (φ 1)] at htri
  have hr : dis (φ g⁻¹ * φ g) 1 = dis (φ g⁻¹) (φ g)⁻¹ := by
    rw [← dis_mul_right (φ g⁻¹) (φ g)⁻¹ (φ g), inv_mul_cancel]
  rw [hr] at htri
  have c := (Nat.cast_le (α := ℝ)).mpr htri
  push_cast at c
  linarith

/-- A triangle relator `l x ρ⁻¹ = 1` of `G` is satisfied by the model up to `5 B` points. -/
theorem relator_support_le (φ : G → Equiv.Perm (Fin n)) (F : Finset G) (B : ℝ)
    (hmul : ∀ g ∈ F, ∀ h ∈ F, (dis (φ (g * h)) (φ g * φ h) : ℝ) ≤ B)
    (h1 : (1 : G) ∈ F) (l x ρ : G) (hrel : l * x * ρ⁻¹ = 1)
    (hl : l ∈ F) (hx : x ∈ F) (hlx : l * x ∈ F) (hρ : ρ ∈ F) (hρi : ρ⁻¹ ∈ F) :
    ((φ l * φ x * (φ ρ)⁻¹).support.card : ℝ) ≤ 5 * B := by
  rw [← dis_one_right]
  have e1 : dis (φ l * φ x * (φ ρ)⁻¹) (φ (l * x) * (φ ρ)⁻¹) = dis (φ l * φ x) (φ (l * x)) :=
    dis_mul_right _ _ _
  have e2 : dis (φ (l * x) * (φ ρ)⁻¹) (φ (l * x) * φ ρ⁻¹) = dis (φ ρ)⁻¹ (φ ρ⁻¹) :=
    dis_mul_left _ _ _
  have e3 : φ (l * x * ρ⁻¹) = φ 1 := by rw [hrel]
  have t1 := dis_triangle (φ l * φ x * (φ ρ)⁻¹) (φ (l * x) * (φ ρ)⁻¹) 1
  have t2 := dis_triangle (φ (l * x) * (φ ρ)⁻¹) (φ (l * x) * φ ρ⁻¹) 1
  have t3 := dis_triangle (φ (l * x) * φ ρ⁻¹) (φ (l * x * ρ⁻¹)) 1
  rw [e1] at t1
  rw [e2] at t2
  rw [e3] at t3
  have b1 := hmul l hl x hx
  rw [dis_comm] at b1
  have b2 := dis_inv_le φ F B hmul h1 ρ hρ hρi
  rw [dis_comm] at b2
  have b3 := hmul (l * x) hlx ρ⁻¹ hρi
  rw [e3, dis_comm] at b3
  have b4 := dis_one_le φ F B hmul h1
  have c1 := (Nat.cast_le (α := ℝ)).mpr t1
  have c2 := (Nat.cast_le (α := ℝ)).mpr t2
  have c3 := (Nat.cast_le (α := ℝ)).mpr t3
  push_cast at c1 c2 c3
  linarith

/-- A nontrivial word `x₁ x₂⁻¹ x₃ x₄⁻¹ ∈ F` of `G` is modelled by a permutation with at most
`8 B` fixed points. -/
theorem rectangle_fixCount_le (φ : G → Equiv.Perm (Fin n)) (F : Finset G) (B : ℝ)
    (hmul : ∀ g ∈ F, ∀ h ∈ F, (dis (φ (g * h)) (φ g * φ h) : ℝ) ≤ B)
    (hsep : ∀ g ∈ F, g ≠ 1 → (fixCount (φ g) : ℝ) ≤ B)
    (h1 : (1 : G) ∈ F) (x₁ x₂ x₃ x₄ : G) (hw : x₁ * x₂⁻¹ * x₃ * x₄⁻¹ ≠ 1)
    (m1 : x₁ ∈ F) (m2 : x₂ ∈ F) (m2i : x₂⁻¹ ∈ F) (m3 : x₃ ∈ F) (m4 : x₄ ∈ F) (m4i : x₄⁻¹ ∈ F)
    (m12 : x₁ * x₂⁻¹ ∈ F) (m123 : x₁ * x₂⁻¹ * x₃ ∈ F) (mw : x₁ * x₂⁻¹ * x₃ * x₄⁻¹ ∈ F) :
    (fixCount (φ x₁ * (φ x₂)⁻¹ * φ x₃ * (φ x₄)⁻¹) : ℝ) ≤ 8 * B := by
  have hfix := hsep _ mw hw
  have t0 := fixCount_le_fixCount_add_dis (φ x₁ * (φ x₂)⁻¹ * φ x₃ * (φ x₄)⁻¹)
    (φ (x₁ * x₂⁻¹ * x₃ * x₄⁻¹))
  have t1 := dis_triangle (φ x₁ * (φ x₂)⁻¹ * φ x₃ * (φ x₄)⁻¹)
    (φ x₁ * φ x₂⁻¹ * φ x₃ * (φ x₄)⁻¹) (φ (x₁ * x₂⁻¹ * x₃ * x₄⁻¹))
  have t2 := dis_triangle (φ x₁ * φ x₂⁻¹ * φ x₃ * (φ x₄)⁻¹)
    (φ (x₁ * x₂⁻¹) * φ x₃ * (φ x₄)⁻¹) (φ (x₁ * x₂⁻¹ * x₃ * x₄⁻¹))
  have t3 := dis_triangle (φ (x₁ * x₂⁻¹) * φ x₃ * (φ x₄)⁻¹)
    (φ (x₁ * x₂⁻¹ * x₃) * (φ x₄)⁻¹) (φ (x₁ * x₂⁻¹ * x₃ * x₄⁻¹))
  have t4 := dis_triangle (φ (x₁ * x₂⁻¹ * x₃) * (φ x₄)⁻¹)
    (φ (x₁ * x₂⁻¹ * x₃) * φ x₄⁻¹) (φ (x₁ * x₂⁻¹ * x₃ * x₄⁻¹))
  have e1 : dis (φ x₁ * (φ x₂)⁻¹ * φ x₃ * (φ x₄)⁻¹) (φ x₁ * φ x₂⁻¹ * φ x₃ * (φ x₄)⁻¹) =
      dis (φ x₂)⁻¹ (φ x₂⁻¹) := by
    rw [dis_mul_right, dis_mul_right, dis_mul_left]
  have e2 : dis (φ x₁ * φ x₂⁻¹ * φ x₃ * (φ x₄)⁻¹) (φ (x₁ * x₂⁻¹) * φ x₃ * (φ x₄)⁻¹) =
      dis (φ x₁ * φ x₂⁻¹) (φ (x₁ * x₂⁻¹)) := by
    rw [dis_mul_right, dis_mul_right]
  have e3 : dis (φ (x₁ * x₂⁻¹) * φ x₃ * (φ x₄)⁻¹) (φ (x₁ * x₂⁻¹ * x₃) * (φ x₄)⁻¹) =
      dis (φ (x₁ * x₂⁻¹) * φ x₃) (φ (x₁ * x₂⁻¹ * x₃)) := dis_mul_right _ _ _
  have e4 : dis (φ (x₁ * x₂⁻¹ * x₃) * (φ x₄)⁻¹) (φ (x₁ * x₂⁻¹ * x₃) * φ x₄⁻¹) =
      dis (φ x₄)⁻¹ (φ x₄⁻¹) := dis_mul_left _ _ _
  rw [e1] at t1
  rw [e2] at t2
  rw [e3] at t3
  rw [e4] at t4
  have b1 := dis_inv_le φ F B hmul h1 x₂ m2 m2i
  have b2 := hmul x₁ m1 x₂⁻¹ m2i
  have b3 := hmul (x₁ * x₂⁻¹) m12 x₃ m3
  have b4 := dis_inv_le φ F B hmul h1 x₄ m4 m4i
  have b5 := hmul (x₁ * x₂⁻¹ * x₃) m123 x₄⁻¹ m4i
  rw [dis_comm] at b1 b2 b3 b4 b5
  have c0 := (Nat.cast_le (α := ℝ)).mpr t0
  have c1 := (Nat.cast_le (α := ℝ)).mpr t1
  have c2 := (Nat.cast_le (α := ℝ)).mpr t2
  have c3 := (Nat.cast_le (α := ℝ)).mpr t3
  have c4 := (Nat.cast_le (α := ℝ)).mpr t4
  push_cast at c0 c1 c2 c3 c4
  linarith

end Words

end Approx252
