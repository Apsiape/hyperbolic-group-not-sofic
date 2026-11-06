import FiniteLean.GroupTheory.Sofic.Basic
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Algebra.Group.Subgroup.Basic

/-! Closure properties of `Approx252.IsSofic`: subgroups (`IsSofic.of_injective`,
`IsSofic.subgroup`) and finite direct products (`isSofic_pi`, tensor models with `ε/(|J|+1)`:
`d(⊗σ_j, ⊗τ_j) = 1 - ∏ (1 - d(σ_j, τ_j))`, `hammingDist_tensorPerm`). -/

namespace NonSofic

open Approx252
open scoped BigOperators

section Perm

variable {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']

theorem dis_eq_card_sub_fixCount (σ τ : Equiv.Perm Ω) :
    (dis σ τ : ℝ) = Fintype.card Ω - fixCount (σ⁻¹ * τ) := by
  have h := fixCount_add_card_support (σ⁻¹ * τ)
  have h' : ((fixCount (σ⁻¹ * τ) : ℕ) : ℝ) + (((σ⁻¹ * τ).support.card : ℕ) : ℝ) =
      Fintype.card Ω := by exact_mod_cast h
  unfold dis
  linarith

theorem permCongr_mul' (e : Ω ≃ Ω') (p p' : Equiv.Perm Ω) :
    e.permCongr (p * p') = e.permCongr p * e.permCongr p' := by
  ext x
  simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply]

theorem permCongr_one' (e : Ω ≃ Ω') : e.permCongr (1 : Equiv.Perm Ω) = 1 := by
  ext x
  simp [Equiv.permCongr_apply]

theorem permCongr_inv' (e : Ω ≃ Ω') (p : Equiv.Perm Ω) :
    (e.permCongr p)⁻¹ = e.permCongr p⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← permCongr_mul', mul_inv_cancel, permCongr_one']

theorem fixCount_permCongr (e : Ω ≃ Ω') (σ : Equiv.Perm Ω) :
    fixCount (e.permCongr σ) = fixCount σ := by
  unfold fixCount
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  symm
  exact Fintype.card_congr (e.subtypeEquiv (fun a => by simp [Equiv.permCongr_apply]))

theorem hammingDist_nonneg {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : 0 ≤ hammingDist σ τ := by
  unfold hammingDist
  positivity

theorem hammingDist_le_one {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : hammingDist σ τ ≤ 1 := by
  unfold hammingDist
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_one hn']
    have h := dis_le_card σ τ
    rw [Fintype.card_fin] at h
    exact_mod_cast h

end Perm

section Pi

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The product permutation `(c_j)_j ↦ (σ_j c_j)_j`. -/
def piPerm {Ω : J → Type*} (σ : ∀ j, Equiv.Perm (Ω j)) : Equiv.Perm (∀ j, Ω j) :=
  Equiv.piCongrRight σ

theorem piPerm_apply {Ω : J → Type*} (σ : ∀ j, Equiv.Perm (Ω j)) (c : ∀ j, Ω j) (j : J) :
    piPerm σ c j = σ j (c j) := rfl

theorem piPerm_mul {Ω : J → Type*} (σ τ : ∀ j, Equiv.Perm (Ω j)) :
    piPerm (fun j => σ j * τ j) = piPerm σ * piPerm τ := by
  ext c j
  rfl

theorem piPerm_one {Ω : J → Type*} : piPerm (fun j => (1 : Equiv.Perm (Ω j))) = 1 := by
  ext c j
  rfl

theorem piPerm_inv {Ω : J → Type*} (σ : ∀ j, Equiv.Perm (Ω j)) :
    (piPerm σ)⁻¹ = piPerm (fun j => (σ j)⁻¹) := by
  rw [inv_eq_iff_mul_eq_one, ← piPerm_mul]
  ext c j
  simp [piPerm_apply]

theorem fixCount_piPerm {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
    (ρ : ∀ j, Equiv.Perm (Ω j)) : fixCount (piPerm ρ) = ∏ j, fixCount (ρ j) := by
  unfold fixCount
  calc (Finset.univ.filter fun c => piPerm ρ c = c).card
      = Fintype.card {c // piPerm ρ c = c} := (Fintype.card_subtype _).symm
    _ = Fintype.card (∀ j, {a // ρ j a = a}) :=
        Fintype.card_congr ((Equiv.subtypeEquivRight
          (p := fun c => piPerm ρ c = c) (q := fun c => ∀ j, ρ j (c j) = c j)
          (fun c => funext_iff)).trans (Equiv.subtypePiEquivPi (p := fun j b => ρ j b = b)))
    _ = ∏ j, Fintype.card {a // ρ j a = a} := Fintype.card_pi
    _ = ∏ j, (Finset.univ.filter fun a => ρ j a = a).card := by
        simp only [Fintype.card_subtype]

/-- The tensor (product) model on `Fin (∏ n_j)`. -/
noncomputable def tensorPerm {n : J → ℕ} (σ : ∀ j, Equiv.Perm (Fin (n j))) :
    Equiv.Perm (Fin (Fintype.card (∀ j, Fin (n j)))) :=
  (Fintype.equivFin (∀ j, Fin (n j))).permCongr (piPerm σ)

theorem tensorPerm_mul {n : J → ℕ} (σ τ : ∀ j, Equiv.Perm (Fin (n j))) :
    tensorPerm (fun j => σ j * τ j) = tensorPerm σ * tensorPerm τ := by
  unfold tensorPerm
  rw [piPerm_mul, permCongr_mul']

theorem tensorPerm_one {n : J → ℕ} :
    tensorPerm (fun j => (1 : Equiv.Perm (Fin (n j)))) = 1 := by
  unfold tensorPerm
  rw [piPerm_one, permCongr_one']

/-- Normalized Hamming distance of tensor models: `1 - ∏_j (1 - d_j)`. -/
theorem hammingDist_tensorPerm {n : J → ℕ} (hn : ∀ j, 0 < n j)
    (σ τ : ∀ j, Equiv.Perm (Fin (n j))) :
    hammingDist (tensorPerm σ) (tensorPerm τ) = 1 - ∏ j, (1 - hammingDist (σ j) (τ j)) := by
  have hcard : Fintype.card (∀ j, Fin (n j)) = ∏ j, n j := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
  have hpos : (0 : ℝ) < ∏ j, (n j : ℝ) := Finset.prod_pos (fun j _ => by exact_mod_cast hn j)
  have hj : ∀ j, (1 : ℝ) - hammingDist (σ j) (τ j) =
      (fixCount ((σ j)⁻¹ * τ j) : ℝ) / n j := by
    intro j
    have hnj : (n j : ℝ) ≠ 0 := by exact_mod_cast (hn j).ne'
    unfold hammingDist
    rw [dis_eq_card_sub_fixCount, Fintype.card_fin, sub_div, div_self hnj]
    ring
  rw [Finset.prod_congr rfl (fun j _ => hj j), Finset.prod_div_distrib]
  unfold hammingDist tensorPerm
  rw [dis_eq_card_sub_fixCount, Fintype.card_fin, permCongr_inv', ← permCongr_mul',
    fixCount_permCongr, piPerm_inv, ← piPerm_mul, fixCount_piPerm, hcard]
  push_cast
  rw [sub_div, div_self hpos.ne']

theorem one_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ j ∈ s, 0 ≤ a j) (h1 : ∀ j ∈ s, a j ≤ 1) :
    1 - ∏ j ∈ s, a j ≤ ∑ j ∈ s, (1 - a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    have hs0 : ∀ i ∈ s, 0 ≤ a i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hs1 : ∀ i ∈ s, a i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hP1 : ∏ i ∈ s, a i ≤ 1 := Finset.prod_le_one₀ hs0 hs1
    have haj0 : 0 ≤ a j := h0 j (Finset.mem_insert_self j s)
    have haj1 : a j ≤ 1 := h1 j (Finset.mem_insert_self j s)
    have ih' := ih hs0 hs1
    nlinarith [mul_le_mul_of_nonneg_right haj1 (sub_nonneg.mpr hP1)]

theorem prod_le_of_mem {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ j ∈ s, 0 ≤ a j) (h1 : ∀ j ∈ s, a j ≤ 1) {j₀ : ι} (hj₀ : j₀ ∈ s) :
    ∏ j ∈ s, a j ≤ a j₀ := by
  rw [← Finset.mul_prod_erase s a hj₀]
  exact mul_le_of_le_one_right (h0 j₀ hj₀)
    (Finset.prod_le_one₀ (fun j hj => h0 j (Finset.mem_of_mem_erase hj))
      (fun j hj => h1 j (Finset.mem_of_mem_erase hj)))

end Pi

/-- A sofic approximation can always be taken on a nonempty set. -/
theorem IsSofic.exists_pos {G : Type*} [Group G] (hG : IsSofic G) (F : Finset G) (ε : ℝ)
    (hε : 0 < ε) : ∃ n : ℕ, 0 < n ∧ ∃ φ : G → Equiv.Perm (Fin n),
      (∀ g ∈ F, ∀ h ∈ F, hammingDist (φ (g * h)) (φ g * φ h) ≤ ε) ∧
      (∀ g ∈ F, g ≠ 1 → 1 - ε ≤ hammingDist (φ g) 1) := by
  obtain ⟨n, φ, hmul, hsep⟩ := hG F ε hε
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, one_pos, fun _ => 1, ?_, ?_⟩
    · intro g _ h _
      simp [hammingDist, dis, hε.le]
    · intro g hg hg1
      have h := hsep g hg hg1
      simp only [hammingDist, Nat.cast_zero, div_zero] at h
      simp [hammingDist, dis, h]
  · exact ⟨n, hn, φ, hmul, hsep⟩

/-- Soficity passes along injective homomorphisms (to subgroups). -/
theorem IsSofic.of_injective {G H : Type*} [Group G] [Group H] (f : H →* G)
    (hf : Function.Injective f) (hG : IsSofic G) : IsSofic H := by
  classical
  intro F ε hε
  obtain ⟨n, φ, hmul, hsep⟩ := hG (F.image f) ε hε
  refine ⟨n, fun h => φ (f h), ?_, ?_⟩
  · intro g hg h hh
    beta_reduce
    rw [map_mul]
    exact hmul _ (Finset.mem_image_of_mem f hg) _ (Finset.mem_image_of_mem f hh)
  · intro g hg hg1
    exact hsep _ (Finset.mem_image_of_mem f hg) (fun h => hg1 (hf (h.trans (map_one f).symm)))

/-- Subgroups of sofic groups are sofic. -/
theorem IsSofic.subgroup {G : Type*} [Group G] (hG : IsSofic G) (K : Subgroup G) :
    IsSofic K :=
  IsSofic.of_injective K.subtype K.subtype_injective hG

/-- Finite direct products of sofic groups are sofic. -/
theorem isSofic_pi {J : Type*} [Fintype J] [DecidableEq J] {H : J → Type*}
    [∀ j, Group (H j)] (hH : ∀ j, IsSofic (H j)) : IsSofic (∀ j, H j) := by
  classical
  intro F ε hε
  set ε' : ℝ := ε / (Fintype.card J + 1) with hε'def
  have hJ : (0 : ℝ) < Fintype.card J + 1 := by positivity
  have hε' : 0 < ε' := div_pos hε hJ
  have hε'le : ε' ≤ ε := div_le_self hε.le (by linarith [(Nat.cast_nonneg (Fintype.card J) : (0:ℝ) ≤ _)])
  have hsum : (Fintype.card J : ℝ) * ε' ≤ ε := by
    rw [hε'def, mul_div_assoc', div_le_iff₀ hJ]
    nlinarith
  have happrox := fun j => IsSofic.exists_pos (hH j) (F.image (fun g => g j)) ε' hε'
  choose n hn φ hmul hsep using happrox
  refine ⟨Fintype.card (∀ j, Fin (n j)), fun g => tensorPerm (fun j => φ j (g j)), ?_, ?_⟩
  · intro g hg h hh
    beta_reduce
    rw [← tensorPerm_mul, hammingDist_tensorPerm hn]
    have hd : ∀ j, hammingDist (φ j ((g * h) j)) (φ j (g j) * φ j (h j)) ≤ ε' := fun j =>
      hmul j (g j) (Finset.mem_image_of_mem _ hg) (h j) (Finset.mem_image_of_mem _ hh)
    calc 1 - ∏ j, (1 - hammingDist (φ j ((g * h) j)) (φ j (g j) * φ j (h j)))
        ≤ ∑ j, (1 - (1 - hammingDist (φ j ((g * h) j)) (φ j (g j) * φ j (h j)))) :=
          one_sub_prod_le_sum _ (fun j => 1 - hammingDist (φ j ((g * h) j)) (φ j (g j) * φ j (h j)))
            (fun j _ => sub_nonneg.mpr (hammingDist_le_one _ _))
            (fun j _ => sub_le_self 1 (hammingDist_nonneg _ _))
      _ ≤ ∑ _j : J, ε' := Finset.sum_le_sum (fun j _ => by rw [sub_sub_cancel]; exact hd j)
      _ = (Fintype.card J : ℝ) * ε' := by simp
      _ ≤ ε := hsum
  · intro g hg hg1
    obtain ⟨j₀, hj₀⟩ : ∃ j, g j ≠ 1 := by
      by_contra hcon
      exact hg1 (funext fun j => not_not.mp (fun h => hcon ⟨j, h⟩))
    beta_reduce
    have h1 : (1 : Equiv.Perm (Fin (Fintype.card (∀ j, Fin (n j))))) =
        tensorPerm (fun j => (1 : Equiv.Perm (Fin (n j)))) := tensorPerm_one.symm
    rw [h1, hammingDist_tensorPerm hn]
    have hsep₀ := hsep j₀ (g j₀) (Finset.mem_image_of_mem _ hg) hj₀
    have hprod : ∏ j, (1 - hammingDist (φ j (g j)) 1) ≤ 1 - hammingDist (φ j₀ (g j₀)) 1 :=
      prod_le_of_mem Finset.univ (fun j => 1 - hammingDist (φ j (g j)) 1)
        (fun j _ => sub_nonneg.mpr (hammingDist_le_one _ _))
        (fun j _ => sub_le_self 1 (hammingDist_nonneg _ _)) (Finset.mem_univ j₀)
    linarith

end NonSofic
