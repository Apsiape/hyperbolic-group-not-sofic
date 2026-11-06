import NonSofic.SharpQuant
import NonSofic.Lemma22Data

/-!
# Theorem `thm:quant` with `ε₀ = 1/(6 r q)` for the data of OpenAI's Lemma 2.2

For the data produced by `exists_markedLineData_lemma22` (OpenAI's construction, `r = 200·200²⁰`,
with the numerical facts `m ≤ 2·200²⁰·N` and `r|E| ≤ m` now proved), every assignment of
permutations of a nonempty finite set `Ω` to the generators whose rectangular words fix at most a
fraction `1/(r-1)²` of `Ω` has a triangle relator moving more than `k` points, for every `k` with
`6 r q k < |Ω|` — i.e. some relator moves at least a fraction `ε₀ = 1/(6rq)`.  (The paper's
`c = 100⁻²⁰` becomes `1/200²⁰` here; `c r ≥ 100` still holds.)
-/

namespace NonSofic

open OAI.Release075 Approx252

/-- **Theorem `thm:quant`, `ε₀ = 1/(6 r q)`, for the data of OpenAI's Lemma 2.2.** -/
theorem quant_lemma22 :
    ∃ (q r : ℕ) (hq : q.Prime), let _ : Fact q.Prime := ⟨hq⟩
      r = 200*200^20 ∧ r < q ∧ ∃ (d : MarkedLineData q r) (hr : 0 < r),
        ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω]
          (σ : (d.presentation hr).Edge → Equiv.Perm Ω) (e k : ℕ),
          RectFix d hr σ e → (r - 1) ^ 2 * e ≤ Fintype.card Ω →
          6 * r * q * k < Fintype.card Ω →
          ∃ b i u v, k < triangleSupport d hr σ b i u v := by
  obtain ⟨q, r, hq, hr200, hrq, -, d, hN, hE⟩ := exists_markedLineData_lemma22
  let : Fact q.Prime := ⟨hq⟩
  have hr : 0 < r := by rw [hr200]; positivity
  refine ⟨q, r, hq, hr200, hrq, d, hr, ?_⟩
  intro Ω _ _ σ e k hrect he hk'
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  exact presentation_quant_lemma22 d hr hrq (200^20) (by positivity) hN (by omega)
    (by rw [hr200]; norm_num) σ e k hrect he hcon hk'

end NonSofic
