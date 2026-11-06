import NonSofic.Collapse
import NonSofic.LineFree
import FiniteLean.GroupTheory.DivisionRing.Adapter
import FiniteLean.GroupTheory.DivisionRing.LineData

/-!
# Theorem `thm:linnell`

Douglas–Mghirbi v1.1.0, Theorem `thm:linnell`: let `K` be a division ring of characteristic `q`
and `Λ` a group containing `G` (an injective homomorphism `ι : G →* Λ`).  Then no ring
homomorphism `φ : K[Λ] → D` to a division ring is Linnell or strongly Hughes-free, and none
satisfies (HF).  (The theorem is stated for every `φ`, injective or not; "Linnell" and "strongly
Hughes-free" include epicness, and the paper's (HF) statement for epic `D` is the special case.)

Here `K` is a division ring with `CharP K q`, the paper's hypothesis (used only to map `ZMod q`
into the centre of `K[Λ]` for `collapse`); the abstract results of `NonSofic.DivisionRing` only
assume that `K` is a `Ring`.

Inputs: `collapse` (Theorem `thm:collapse`, through `SylvesterRankFunction.toRankFn` applied to
`M ↦ rank_D φ(M)`), `LineFree.lineSubgroup_free` (Lemma `lem:free`), and the abstract assembly
`linnell_obstruction_of_lines` (Lemma `lem:fullrank` and the proof of `thm:linnell`).
-/

namespace NonSofic

open OAI.Release075 MonoidAlgebra

variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

/-- **Theorem `thm:linnell`.** -/
theorem linnell (K : Type*) [DivisionRing K] [CharP K q] {Λ : Type*}
    [Group Λ] (ι : (d.presentation hr).GroupType →* Λ) (hι : Function.Injective ι)
    {D : Type*} [DivisionRing D] (φ : MonoidAlgebra K Λ →+* D) :
    ¬ IsLinnell φ ∧ ¬ IsStronglyHughesFree φ ∧ ¬ SatisfiesHF φ := by
  classical
  obtain ⟨h1, h2⟩ := collapse d hr (rankFun φ).toRankFn
    (MonoidAlgebra.singleOneRingHom.comp (ZMod.castHom (dvd_refl q) K))
    ((MonoidAlgebra.of K Λ).comp ι)
  refine linnell_obstruction_of_lines hr (fun i u v => ι ((d.presentation hr).x i u v))
    (fun i => ?_) φ ?_
  · have hcomp : lineHom hr (fun u v => ι ((d.presentation hr).x i u v)) =
        ι.comp (FreeGroup.lift fun p : {p : Fin r × Fin r // p ≠ (⟨0, hr⟩, ⟨0, hr⟩)} =>
          (d.presentation hr).x i p.val.1 p.val.2 *
            ((d.presentation hr).x i ⟨0, hr⟩ ⟨0, hr⟩)⁻¹) := by
      ext p
      simp [lineHom]
    rw [hcomp]
    exact hι.comp (LineFree.lineSubgroup_free d hr i)
  · have hrk : ∀ i, (rankFun φ).toRankFn.rk (lineMatrix d hr ((MonoidAlgebra.of K Λ).comp ι) i) =
        rankD ((Matrix.of fun u v => of K Λ (ι ((d.presentation hr).x i u v))).map φ) :=
      fun i => rankFun_toRankFn_rk φ _
    simp only [hrk] at h1
    generalize (2 * (q ^ 20 - d.exceptional.card) + r * d.exceptional.card : ℕ) = B at h1 h2
    have h2' : (4 : ℝ) * B < Fintype.card d.Label * r := by exact_mod_cast h2
    linarith

end NonSofic
