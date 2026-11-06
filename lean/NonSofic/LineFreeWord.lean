import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-! `lem:free`, free-group part.  `psi p₀ : F({p ≠ p₀}) → F(α)`, `y_p ↦ p p₀⁻¹` (= `π₁(Θ,V)`
for the two-vertex graph `Θ`), is injective (`theta` collapses the tree edge).  For `g ≠ 1`,
`exists_core` gives a nonempty cyclically reduced, sign-alternating (= edge path in `Θ`), even
length (= closed) word `R` with `psi p₀ g = C R C⁻¹`. -/

namespace NonSofic

namespace LineFreeWord

open FreeGroup

variable {α : Type*} [DecidableEq α] (p₀ : α)

/-- `y_p ↦ p p₀⁻¹`. -/
def psi : FreeGroup {p : α // p ≠ p₀} →* FreeGroup α :=
  FreeGroup.lift (fun p => of p.val * (of p₀)⁻¹)

/-- Collapse the tree edge `p₀`. -/
def theta : FreeGroup α →* FreeGroup {p : α // p ≠ p₀} :=
  FreeGroup.lift (fun a => if h : a = p₀ then 1 else of ⟨a, h⟩)

theorem theta_psi (g : FreeGroup {p : α // p ≠ p₀}) : theta p₀ (psi p₀ g) = g := by
  have h : (theta p₀).comp (psi p₀) = MonoidHom.id _ := by
    ext p
    simp [psi, theta, p.property]
  exact DFunLike.congr_fun h g

theorem psi_injective : Function.Injective (psi p₀) :=
  Function.LeftInverse.injective (theta_psi p₀)

/-- The edge path of a letter `y_p^{±1}`. -/
def blk (x : {p : α // p ≠ p₀} × Bool) : List (α × Bool) :=
  if x.2 then [(x.1.val, true), (p₀, false)] else [(p₀, true), (x.1.val, false)]

def expand (L : List ({p : α // p ≠ p₀} × Bool)) : List (α × Bool) := L.flatMap (blk p₀)

theorem mk_blk (x : {p : α // p ≠ p₀} × Bool) : mk (blk p₀ x) = psi p₀ (mk [x]) := by
  obtain ⟨p, b⟩ := x
  have e1 : ∀ a c : α × Bool, (mk [a, c] : FreeGroup α) = mk [a] * mk [c] := fun a c => by
    rw [FreeGroup.mul_mk]
    rfl
  have e2 : ∀ a : α, (mk [(a, true)] : FreeGroup α) = of a := fun a => rfl
  have e3 : ∀ a : α, (mk [(a, false)] : FreeGroup α) = (of a)⁻¹ := fun a => by
    show mk [(a, false)] = (mk [(a, true)])⁻¹
    rw [FreeGroup.inv_mk]
    rfl
  cases b <;> simp [blk, psi, e1, e2, e3, FreeGroup.lift_mk]

theorem mk_expand (L : List ({p : α // p ≠ p₀} × Bool)) :
    mk (expand p₀ L) = psi p₀ (mk L) := by
  induction L with
  | nil =>
    change (1 : FreeGroup α) = psi p₀ 1
    exact (_root_.map_one (psi p₀)).symm
  | cons x L ih =>
    have h1 : expand p₀ (x :: L) = blk p₀ x ++ expand p₀ L := List.flatMap_cons
    have h2 : (mk (x :: L) : FreeGroup {p : α // p ≠ p₀}) = mk [x] * mk L := by
      rw [FreeGroup.mul_mk]
      rfl
    rw [h1, ← FreeGroup.mul_mk, h2, _root_.map_mul, ih, mk_blk]

/-- Consecutive letters have opposite signs (an edge path in the bipartite graph `Θ`). -/
def Alt (L : List (α × Bool)) : Prop := L.IsChain (fun a b => a.2 ≠ b.2)

theorem alt_expand (L : List ({p : α // p ≠ p₀} × Bool)) :
    Alt (expand p₀ L) ∧ ∀ y ∈ (expand p₀ L).head?, y.2 = true := by
  induction L with
  | nil => exact ⟨List.isChain_nil, by simp [expand]⟩
  | cons x L ih =>
    have h1 : expand p₀ (x :: L) = blk p₀ x ++ expand p₀ L := List.flatMap_cons
    obtain ⟨p, b⟩ := x
    rw [h1]
    refine ⟨?_, ?_⟩
    · cases b <;>
      · simp only [blk, Bool.false_eq_true, ite_false, ite_true, List.cons_append,
          List.nil_append]
        rcases hE : expand p₀ L with _ | ⟨y, ys⟩
        · simp [Alt]
        · have hy : y.2 = true := ih.2 y (by simp [hE])
          have hc : Alt (y :: ys) := hE ▸ ih.1
          simp only [Alt, List.isChain_cons_cons] at hc ⊢
          exact ⟨by simp, by simp [hy], hc⟩
    · cases b <;> simp [blk]

theorem length_expand (L : List ({p : α // p ≠ p₀} × Bool)) :
    (expand p₀ L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have h1 : expand p₀ (x :: L) = blk p₀ x ++ expand p₀ L := List.flatMap_cons
    rw [h1, List.length_append, ih, List.length_cons]
    obtain ⟨p, b⟩ := x
    cases b <;> simp [blk] <;> ring

theorem alt_append_cons_cons {L₁ L₂ : List (α × Bool)} {u v : α × Bool}
    (h : Alt (L₁ ++ u :: v :: L₂)) : Alt (L₁ ++ L₂) := by
  unfold Alt at h ⊢
  rw [List.isChain_append] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  rw [List.isChain_cons_cons] at h2
  obtain ⟨huv, h2⟩ := h2
  refine ⟨h1, h2.tail, ?_⟩
  intro x hx y hy
  have hxu : x.2 ≠ u.2 := h3 x hx u rfl
  have hvy : v.2 ≠ y.2 := by
    rcases L₂ with _ | ⟨z, zs⟩
    · simp at hy
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact (List.isChain_cons_cons.mp h2).1
  revert hxu huv hvy
  cases x.2 <;> cases u.2 <;> cases v.2 <;> cases y.2 <;> simp

theorem alt_of_red {L₁ L₂ : List (α × Bool)} (h : Red L₁ L₂) (hA : Alt L₁) :
    Alt L₂ ∧ (Even L₁.length → Even L₂.length) := by
  induction h with
  | refl => exact ⟨hA, id⟩
  | tail _ hs ih =>
    obtain ⟨hA', hE'⟩ := ih
    cases hs with
    | not =>
      refine ⟨alt_append_cons_cons hA', fun he => ?_⟩
      have := hE' he
      simp only [List.length_append, List.length_cons] at this ⊢
      rcases this with ⟨k, hk⟩
      exact ⟨k - 1, by omega⟩

/-- **The cyclically reduced core.**  For `g ≠ 1` there are a conjugator `C` and a nonempty,
cyclically reduced, alternating word `R` of even length with `psi p₀ g = C · R · C⁻¹`. -/
theorem exists_core (g : FreeGroup {p : α // p ≠ p₀}) (hg : g ≠ 1) :
    ∃ R C : List (α × Bool), R ≠ [] ∧ IsCyclicallyReduced R ∧ Alt R ∧ Even R.length ∧
      psi p₀ g = mk C * mk R * (mk C)⁻¹ := by
  set L := (psi p₀ g).toWord with hL
  have hLne : psi p₀ g ≠ 1 := fun h => hg (psi_injective p₀ (h.trans (_root_.map_one (psi p₀)).symm))
  -- `L` is the reduction of the alternating word `expand g.toWord`
  have hexp : mk (expand p₀ g.toWord) = psi p₀ g := by rw [mk_expand, FreeGroup.mk_toWord]
  have hred : Red (expand p₀ g.toWord) L := by
    rw [hL, ← hexp, FreeGroup.toWord_mk]
    exact FreeGroup.reduce.red
  have hAL := alt_of_red hred (alt_expand p₀ g.toWord).1
  have hEL : Even L.length := hAL.2 ⟨g.toWord.length, by rw [length_expand]; ring⟩
  refine ⟨reduceCyclically L, reduceCyclically.conjugator L, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hLne
    have hc := reduceCyclically.conj_conjugator_reduceCyclically L
    rw [h0, List.append_nil] at hc
    have hm := congrArg (FreeGroup.mk (α := α)) hc
    rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, mul_inv_cancel, hL,
      FreeGroup.mk_toWord] at hm
    exact hm.symm
  · exact reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord
  · have hc := reduceCyclically.conj_conjugator_reduceCyclically L
    have hinf : reduceCyclically L <:+: L :=
      ⟨reduceCyclically.conjugator L, FreeGroup.invRev (reduceCyclically.conjugator L), hc⟩
    exact List.IsChain.infix hAL.1 hinf
  · have hc := congrArg List.length (reduceCyclically.conj_conjugator_reduceCyclically L)
    simp only [List.length_append, FreeGroup.invRev_length] at hc
    rcases hEL with ⟨k, hk⟩
    exact ⟨k - (reduceCyclically.conjugator L).length, by omega⟩
  · have hc := reduceCyclically.conj_conjugator_reduceCyclically L
    have hm := congrArg (FreeGroup.mk (α := α)) hc
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, hL,
      FreeGroup.mk_toWord] at hm
    exact hm.symm

/-- The value of a word under `f : α → G`. -/
theorem lift_psi {G : Type*} [Group G] (f : α → G) (g : FreeGroup {p : α // p ≠ p₀}) :
    FreeGroup.lift f (psi p₀ g) = FreeGroup.lift (fun p => f p.val * (f p₀)⁻¹) g := by
  have h : (FreeGroup.lift f).comp (psi p₀) = FreeGroup.lift (fun p => f p.val * (f p₀)⁻¹) := by
    ext p
    simp [psi]
  exact DFunLike.congr_fun h g

/-- Cyclic reducedness, in the indexed form used by the geometric argument. -/
theorem cyc_step {R : List (α × Bool)} (hR : IsCyclicallyReduced R) (n : ℕ) (hn : n < R.length)
    (a b : α × Bool) (ha : R[n]? = some a) (hb : R[(n + 1) % R.length]? = some b) :
    ¬ (b.1 = a.1 ∧ b.2 = !a.2) := by
  rintro ⟨h1, h2⟩
  by_cases hlast : n + 1 < R.length
  · rw [Nat.mod_eq_of_lt hlast] at hb
    have hc := List.isChain_iff_getElem.mp hR.1 n hlast
    rw [List.getElem?_eq_some_iff] at ha hb
    obtain ⟨_, ha⟩ := ha
    obtain ⟨_, hb⟩ := hb
    rw [ha, hb] at hc
    have hab : a.2 = b.2 := hc h1.symm
    rw [h2] at hab
    simp at hab
  · have hn1 : n + 1 = R.length := by omega
    rw [hn1, Nat.mod_self] at hb
    have hlast' : R.getLast? = some a := by
      rw [List.getLast?_eq_getElem?]
      rw [show R.length - 1 = n by omega]
      exact ha
    have hhead : R.head? = some b := by
      rw [List.head?_eq_getElem?]
      exact hb
    have hab : a.2 = b.2 := hR.2 a (Option.mem_def.mpr hlast') b (Option.mem_def.mpr hhead) h1.symm
    rw [h2] at hab
    simp at hab

end LineFreeWord

end NonSofic
