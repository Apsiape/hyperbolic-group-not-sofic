import NonSofic.Lemma22Quant
import NonSofic.Linnell
import Approx252.NonSofic

/-!
# Headline of Douglas–Mghirbi v1.1.0, for one group

For the data of OpenAI's Lemma 2.2 (`exists_markedLineData_lemma22`, `r = 200·200²⁰`), the group
`G = (d.presentation hr).GroupType` is torsion-free, word-hyperbolic and not sofic
(`thm:main`); for every division ring `K` of characteristic `q`, every group `Λ ⊇ G` and every
ring homomorphism `φ : K[Λ] → D` to a division ring, `φ` is not Linnell, not strongly
Hughes-free and fails (HF) (`thm:linnell`); and `thm:quant` holds with `ε₀ = 1/(6rq)`.
`K`, `Λ`, `D` range over arbitrary universes `u`, `v`, `w` (universe parameters of the theorems).
-/

namespace NonSofic

open OAI.Release075 Approx252

universe u v w

/-- All results for the same data `d`. -/
theorem headline_data :
    ∃ (q r : ℕ) (hq : q.Prime), let _ : Fact q.Prime := ⟨hq⟩
      ∃ (d : MarkedLineData q r) (hr : 0 < r), r = 200*200^20 ∧ r < q ∧
        TorsionFree (d.presentation hr).GroupType ∧
        WordHyperbolic (d.presentation hr).GroupType ∧
        ¬ IsSofic (d.presentation hr).GroupType ∧
        (∀ (K : Type u) [DivisionRing K] [CharP K q] (Λ : Type v) [Group Λ]
          (ι : (d.presentation hr).GroupType →* Λ), Function.Injective ι →
          ∀ (D : Type w) [DivisionRing D] (φ : MonoidAlgebra K Λ →+* D),
            ¬ IsLinnell φ ∧ ¬ IsStronglyHughesFree φ ∧ ¬ SatisfiesHF φ) ∧
        (∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω]
          (σ : (d.presentation hr).Edge → Equiv.Perm Ω) (e k : ℕ),
          RectFix d hr σ e → (r - 1) ^ 2 * e ≤ Fintype.card Ω →
          6 * r * q * k < Fintype.card Ω →
          ∃ b i u v, k < triangleSupport d hr σ b i u v) := by
  obtain ⟨q, r, hq, hr200, hrq, hq200, d, hN, hE⟩ := exists_markedLineData_lemma22
  let : Fact q.Prime := ⟨hq⟩
  have hr : 0 < r := by rw [hr200]; positivity
  refine ⟨q, r, hq, d, hr, hr200, hrq, d.presentation_torsionFree hr,
    d.presentation_wordHyperbolic hr, presentation_not_sofic d hr hrq hq200, ?_, ?_⟩
  · intro K _ _ Λ _ ι hι D _ φ
    exact linnell d hr K ι hι φ
  · intro Ω _ _ σ e k hrect he hk'
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact presentation_quant_lemma22 d hr hrq (200^20) (by positivity) hN (by omega)
      (by rw [hr200]; norm_num) σ e k hrect he hcon hk'

/-- **Headline.** -/
theorem headline :
    ∃ (q : ℕ) (_ : q.Prime) (G : Type) (_ : Group G),
      TorsionFree G ∧ WordHyperbolic G ∧ ¬ IsSofic G ∧
      ∀ (K : Type u) [DivisionRing K] [CharP K q] (Λ : Type v) [Group Λ] (ι : G →* Λ),
        Function.Injective ι → ∀ (D : Type w) [DivisionRing D] (φ : MonoidAlgebra K Λ →+* D),
          ¬ IsLinnell φ ∧ ¬ IsStronglyHughesFree φ ∧ ¬ SatisfiesHF φ := by
  obtain ⟨q, r, hq, d, hr, -, -, h1, h2, h3, h4, -⟩ := headline_data.{u, v, w}
  exact ⟨q, hq, _, inferInstance, h1, h2, h3, h4⟩

end NonSofic
