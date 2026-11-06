import FiniteLean.GroupTheory.OAI.GroupTheory.Hyperbolic.Main
import NonSofic.LineFreeWord

/-! `lem:free`.  `xword_not_fillable`: a nonempty cyclically reduced closed word in the x-edges of
one label has no triangle filling (OpenAI's proof of `rectangular_nontriviality` with the
rectangle replaced by an arbitrary such word; every boundary turn compares two distinct
x-edges of label `i`, so `x_turn_large` applies).  `lineSubgroup_free`: the hom
`F({(u,v) ≠ (0,0)}) → G`, `y_{uv} ↦ x_{iuv} x_{i00}⁻¹`, is injective. -/

namespace NonSofic

open OAI.Release075
open scoped BigOperators

namespace LineFree

attribute [local instance] Classical.propDecidable Classical.decEq

variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

/-- One boundary turn between two x-edges of label `i` which is not a backtrack. -/
theorem x_turn_large' (i : d.Label) (a b : (d.presentation hr).OrientedEdge)
    (ha : ∃ u v s, a = (.inl (i, u, v), s)) (hb : ∃ u v s, b = (.inl (i, u, v), s))
    (hnb : b ≠ (d.presentation hr).flipEdge a)
    (ht : (d.presentation hr).edgeTarget ((d.presentation hr).flipEdge b) =
      (d.presentation hr).edgeTarget a)
    (p : (d.allLink hr).Walk (d.linkDirection hr ((d.presentation hr).flipEdge b))
      (d.linkDirection hr a)) (hp : ReducedWalk p) :
    5 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr a)) * p.length := by
  obtain ⟨u, v, s, rfl⟩ := ha
  obtain ⟨u', v', t, rfl⟩ := hb
  refine d.x_turn_large hr i u v u' v' s t ht ?_ p hp
  intro heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  apply hnb
  cases s <;> cases t <;>
    simp_all [BlockPresentation.flipEdge, BlockPresentation.edgeTarget]

/-- **Closed x-paths of one label are not null-homotopic.**  A nonempty word `w` in the oriented
x-edges of a single label `i`, which is cyclically reduced (no letter is followed, cyclically,
by its own reverse), has no planar triangle filling. -/
theorem xword_not_fillable (i : d.Label) (w : List (d.presentation hr).OrientedEdge)
    (hx : ∀ e ∈ w, ∃ u v s, e = ((.inl (i, u, v) : (d.presentation hr).Edge), s))
    (hne : w ≠ [])
    (hcyc : ∀ n, n < w.length → ∀ e e', w[n]? = some e → w[(n + 1) % w.length]? = some e' →
      e' ≠ (d.presentation hr).flipEdge e)
    (hf : Fillable (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
      (d.presentation hr).TriangleFace w) : False := by
  obtain ⟨D, hD⟩ := TriangleFilling.exists_noDipole hf
  have hn : D.boundary ≠ [] := by
    intro hz
    apply hne
    have hw := D.boundary_word
    rw [hz, List.map_nil] at hw
    exact hw.symm
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil D.boundary hn
  apply (d.concreteRibbon hr D b hb).not_all_turns_geodesic
    (d.allLink hr) (d.dartDirection hr D)
    (d.ribbon_adj hr D b hb) (d.ribbon_reduced hr D b hb hD)
    (d.ribbon_closed hr D b hb)
  intro a ha p hp
  have ha' : a.val ∈ D.boundary := (d.ribbon_outer_iff hr D b hb a).mp ha
  have hb' : D.next a.val ∈ D.boundary := (D.boundary_cycle.mem_iff a.val).mpr ha'
  have hal : D.label a.val ∈ w := by
    have hm : D.label a.val ∈ D.boundary.map D.label := List.mem_map.mpr ⟨a.val, ha', rfl⟩
    rwa [D.boundary_word] at hm
  have hbl : D.label (D.next a.val) ∈ w := by
    have hm : D.label (D.next a.val) ∈ D.boundary.map D.label :=
      List.mem_map.mpr ⟨D.next a.val, hb', rfl⟩
    rwa [D.boundary_word] at hm
  -- the position of `a` on the boundary, and of its successor
  obtain ⟨n, hna⟩ := List.mem_iff_getElem?.mp ha'
  obtain ⟨hn, hna'⟩ := List.getElem?_eq_some_iff.mp hna
  have hlen : D.boundary.length = w.length := by
    have h := congrArg List.length D.boundary_word
    simpa using h
  have hpos : 0 < D.boundary.length := by omega
  have hnext : D.boundary[(n + 1) % D.boundary.length]? = some (D.next a.val) := by
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ hpos)]
    congr 1
    rw [D.boundary_cycle.2 _ ha', ← hna', List.formPerm_apply_getElem _ D.boundary_cycle.1]
  have h1 : (D.boundary.map D.label)[n]? = some (D.label a.val) := by
    simp [hna]
  have h2 : (D.boundary.map D.label)[(n + 1) % (D.boundary.map D.label).length]? =
      some (D.label (D.next a.val)) := by
    simp [hnext]
  rw [D.boundary_word] at h1 h2
  have hnb : D.label (D.next a.val) ≠ (d.presentation hr).flipEdge (D.label a.val) :=
    hcyc n (by omega) _ _ h1 h2
  -- the turn at `a`
  rw [d.ribbon_color hr D b hb a]
  have ht : (d.presentation hr).edgeTarget ((d.presentation hr).flipEdge (D.label (D.next a.val))) =
      (d.presentation hr).edgeTarget (D.label a.val) := by
    rw [← D.reverse_label]
    exact D.color_next a.val
  have hs := d.ribbon_direction_step hr D b hb a
  let p' := p.copy hs rfl
  have hp' : ReducedWalk p' := by
    intro j hj
    simpa only [p', SimpleGraph.Walk.getVert_copy] using
      hp j (by simpa only [p', SimpleGraph.Walk.length_copy] using hj)
  have hh := x_turn_large' d hr i _ _ (hx _ hal) (hx _ hbl) hnb ht p' hp'
  have hlen' : p'.length = p.length := SimpleGraph.Walk.length_copy p hs rfl
  change 5 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr (D.label a.val))) *
    p'.length at hh
  rw [hlen'] at hh
  exact hh

section Free

/-- The oriented x-edge of label `i` for a free-group letter `((u, v), s)`. -/
noncomputable def xEdge (i : d.Label) (x : (Fin r × Fin r) × Bool) : (d.presentation hr).OrientedEdge :=
  ((.inl (i, x.1.1, x.1.2) : (d.presentation hr).Edge), x.2)

/-- The source vertex of an x-letter of sign `s`. -/
noncomputable def vert : Bool → (d.presentation hr).Vertex
  | true => .v
  | false => .w

theorem tgt_xEdge (i : d.Label) (x : (Fin r × Fin r) × Bool) :
    (d.presentation hr).edgeTarget (xEdge d hr i x) = vert d hr (!x.2) := by
  obtain ⟨a, s⟩ := x
  cases s <;> rfl

theorem src_xEdge (i : d.Label) (x : (Fin r × Fin r) × Bool) :
    (d.presentation hr).edgeTarget ((d.presentation hr).flipEdge (xEdge d hr i x)) =
      vert d hr x.2 := by
  obtain ⟨a, s⟩ := x
  cases s <;> rfl

theorem flip_xEdge (i : d.Label) (x : (Fin r × Fin r) × Bool) :
    (d.presentation hr).flipEdge (xEdge d hr i x) = xEdge d hr i (x.1, !x.2) := rfl

theorem xEdge_injective (i : d.Label) : Function.Injective (xEdge d hr i) := by
  rintro ⟨⟨u, v⟩, s⟩ ⟨⟨u', v'⟩, s'⟩ h
  simp only [xEdge, Prod.mk.injEq, Sum.inl.injEq] at h
  obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := h
  rfl

theorem wp_congr {a a' b b' : (d.presentation hr).Vertex}
    {w : List (d.presentation hr).OrientedEdge} (ha : a = a') (hb : b = b')
    (h : WordPath (d.presentation hr).flipEdge (d.presentation hr).edgeTarget a b w) :
    WordPath (d.presentation hr).flipEdge (d.presentation hr).edgeTarget a' b' w := by
  subst ha
  subst hb
  exact h

theorem wordPath_cons_x (i : d.Label) (a : Fin r × Fin r) (t : Bool)
    {c : (d.presentation hr).Vertex} {w : List (d.presentation hr).OrientedEdge}
    (h : WordPath (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
      (vert d hr (!t)) c w) :
    WordPath (d.presentation hr).flipEdge (d.presentation hr).edgeTarget (vert d hr t) c
      (xEdge d hr i (a, t) :: w) := by
  have h1 : WordPath (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
      ((d.presentation hr).edgeTarget (xEdge d hr i (a, t))) c w := by
    rw [tgt_xEdge]
    exact h
  have h2 := WordPath.cons (xEdge d hr i (a, t)) h1
  rw [src_xEdge] at h2
  exact h2

/-- An alternating x-word of even length starting with sign `s` is a closed edge path. -/
theorem wordPath_even (i : d.Label) (s : Bool) : ∀ (R : List ((Fin r × Fin r) × Bool)),
    (∀ y ∈ R.head?, y.2 = s) → LineFreeWord.Alt R → Even R.length →
    WordPath (d.presentation hr).flipEdge (d.presentation hr).edgeTarget (vert d hr s)
      (vert d hr s) (R.map (xEdge d hr i))
  | [], _, _, _ => WordPath.nil _
  | [_], _, _, he => absurd he (by simp)
  | (xa, xs) :: (ya, ys) :: R, hs, hA, he => by
    have hx : xs = s := hs (xa, xs) rfl
    obtain ⟨hxy, hA'⟩ := List.isChain_cons_cons.mp hA
    have hy : ys = !s := by
      rw [← hx]
      revert hxy
      cases xs <;> cases ys <;> simp
    have hR : ∀ z ∈ R.head?, z.2 = s := by
      intro z hz
      rcases R with _ | ⟨w, ws⟩
      · simp at hz
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
        rw [← hz]
        have hyz := (List.isChain_cons_cons.mp hA').1
        obtain ⟨wa, wb⟩ := w
        rw [hy] at hyz
        revert hyz
        cases s <;> cases wb <;> simp
    have hE : Even R.length := by
      simp only [List.length_cons] at he
      rcases he with ⟨k, hk⟩
      exact ⟨k - 1, by omega⟩
    have ih := wordPath_even i s R hR hA'.tail hE
    have h2 := wordPath_cons_x d hr i ya ys
      (wp_congr d hr (by rw [hy, Bool.not_not]) rfl ih)
    have h3 := wordPath_cons_x d hr i xa xs (wp_congr d hr (by rw [hx, hy]) rfl h2)
    exact wp_congr d hr (by rw [hx]) rfl h3

/-- The value of an x-word in `G`. -/
theorem wordValue_xEdge (i : d.Label) (R : List ((Fin r × Fin r) × Bool)) :
    (d.presentation hr).wordValue (R.map (xEdge d hr i)) =
      FreeGroup.lift (fun a : Fin r × Fin r => (d.presentation hr).x i a.1 a.2)
        (FreeGroup.mk R) := by
  rw [FreeGroup.lift_mk]
  unfold BlockPresentation.wordValue
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨a, s⟩ -
  cases s <;> rfl

/-- **Lemma `lem:free`.**  The line subgroup `A_i = ⟨x_{iuv} x_{i00}⁻¹⟩` is free on the
`y_{uv} = x_{iuv} x_{i00}⁻¹`, `(u, v) ≠ (0, 0)`. -/
theorem lineSubgroup_free (i : d.Label) :
    Function.Injective (FreeGroup.lift
      (fun p : {p : Fin r × Fin r // p ≠ (⟨0, hr⟩, ⟨0, hr⟩)} =>
        (d.presentation hr).x i p.val.1 p.val.2 *
          ((d.presentation hr).x i ⟨0, hr⟩ ⟨0, hr⟩)⁻¹)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hne
  obtain ⟨R, C, hRne, hcyc, hAlt, hEven, hconj⟩ :=
    LineFreeWord.exists_core ((⟨0, hr⟩, ⟨0, hr⟩) : Fin r × Fin r) g hne
  -- the value of the core is `1`
  have hval : FreeGroup.lift (fun a : Fin r × Fin r => (d.presentation hr).x i a.1 a.2)
      (FreeGroup.mk R) = 1 := by
    have h1 := LineFreeWord.lift_psi ((⟨0, hr⟩, ⟨0, hr⟩) : Fin r × Fin r)
      (fun a : Fin r × Fin r => (d.presentation hr).x i a.1 a.2) g
    rw [hconj, map_mul, map_mul, map_inv] at h1
    have h2 := h1.trans hg
    have key : ∀ A B : (d.presentation hr).GroupType, A * B * A⁻¹ = 1 → B = 1 := by
      intro A B h
      have h3 : B = A⁻¹ * (A * B * A⁻¹) * A := by group
      rw [h3, h]
      group
    exact key _ _ h2
  -- it is a closed, cyclically reduced x-path of label `i`
  obtain ⟨x, R', rfl⟩ := List.exists_cons_of_ne_nil hRne
  have hwp := wordPath_even d hr i x.2 (x :: R') (fun y hy => by
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    rw [hy]) hAlt hEven
  have hwv : (d.presentation hr).wordValue ((x :: R').map (xEdge d hr i)) = 1 := by
    rw [wordValue_xEdge]
    exact hval
  have hfill : Fillable (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
      (d.presentation hr).TriangleFace ((x :: R').map (xEdge d hr i)) := by
    obtain ⟨p, hp⟩ := BlockPresentation.WordPath.exists_raw (d.presentation hr) hwp
    rw [← hp]
    exact (d.presentation hr).nullhomotopic_fillable
      ((d.presentation hr).rawWord_nullhomotopic p (by rw [hp]; exact hwv))
  apply xword_not_fillable d hr i ((x :: R').map (xEdge d hr i)) ?_ (by simp) ?_ hfill
  · intro e he
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp he
    exact ⟨y.1.1, y.1.2, y.2, rfl⟩
  · intro n hn e e' he he' heq
    rw [List.length_map] at hn he'
    rw [List.getElem?_map] at he he'
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp he'
    rw [flip_xEdge] at heq
    have hab := xEdge_injective d hr i heq
    exact LineFreeWord.cyc_step hcyc n hn a b ha hb ⟨by rw [hab], by rw [hab]⟩

end Free

end LineFree

end NonSofic
