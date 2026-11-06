import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Pure counting/arithmetic for the sharp constants: `sum_rect_count` (`2r³-r²` degenerate
terms, `r²(r-1)²` rectangular ones), `budget_general` (`ε₀ = 1/(4r²N(q-1))`), `budget_lemma22`
(`ε₀ = 1/(6rq)`), `sum_dite_not_mem`. -/

namespace NonSofic

open scoped BigOperators

section Count

/-- The exact count of the second trace expansion: `2r³ - r²` degenerate index choices with
value `D`, and `r²(r-1)²` nondegenerate ones with value at most `e`. -/
theorem sum_rect_count {ι : Type*} [Fintype ι] [DecidableEq ι] (D e : ℝ) :
    (∑ u : ι, ∑ u' : ι, ∑ v : ι, ∑ v' : ι,
      ((if u = u' then D else 0) + (if v = v' then D else 0) -
        (if u = u' ∧ v = v' then D else 0) + (if u ≠ u' ∧ v ≠ v' then e else 0))) =
      (2 * (Fintype.card ι : ℝ) ^ 3 - (Fintype.card ι : ℝ) ^ 2) * D +
        (Fintype.card ι : ℝ) ^ 2 * ((Fintype.card ι : ℝ) - 1) ^ 2 * e := by
  have key : ∀ u u' v v' : ι, (if u ≠ u' ∧ v ≠ v' then e else 0) =
      e - (if u = u' then e else 0) - (if v = v' then e else 0) +
        (if u = u' ∧ v = v' then e else 0) := by
    intro u u' v v'
    by_cases hu : u = u' <;> by_cases hv : v = v' <;> simp [hu, hv]
  simp_rw [key]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_and]
  simp [pow_succ, mul_assoc, sub_mul]
  ring

end Count

section Budget

/-- Arithmetic for `ε₀ = 1/(4 r² N (q-1))`. -/
theorem budget_general (r q N m Ecard D S k : ℕ)
    (hbud : 4 * (2 * m + r * Ecard) < N * r) (hS : S ≤ N * (q - 1))
    (hk : 4 * r ^ 2 * N * (q - 1) * k < D) :
    4 * (2 * m + r * Ecard) * D + 4 * (S * (r * r * k)) < N * r * D := by
  have h1 : S * (r * r * k) ≤ N * (q - 1) * (r * r * k) := Nat.mul_le_mul_right _ hS
  have h1' : 4 * (N * (q - 1) * (r * r * k)) = 4 * r ^ 2 * N * (q - 1) * k := by ring
  have hbud' : 4 * (2 * m + r * Ecard) + 1 ≤ N * r := hbud
  have h2 : (4 * (2 * m + r * Ecard) + 1) * D ≤ N * r * D := Nat.mul_le_mul_right _ hbud'
  rw [add_mul, one_mul] at h2
  omega

/-- Arithmetic for `ε₀ = 1/(6 r q)` under the hypotheses of OpenAI's Lemma 2.2:
`m ≤ 2 C N` (that is `N ≥ c m / 2` with `c = 1/C`), `r|E| ≤ m`, `100 C ≤ r` (`c r ≥ 100`).
The paper takes `C = 100²⁰`. -/
theorem budget_lemma22 (C r q N m Ecard D S k : ℕ) (hN : 0 < N)
    (hm : m ≤ 2 * C * N) (hE : r * Ecard ≤ m) (hr : 100 * C ≤ r) (hC : 0 < C)
    (hS : S ≤ N * (q - 1)) (hk : 6 * r * q * k < D) :
    4 * (2 * m + r * Ecard) * D + 4 * (S * (r * r * k)) < N * r * D := by
  have hq1 : q - 1 ≤ q := Nat.sub_le q 1
  -- `3 · 4 S r² k ≤ 2 N r · (6 r q k)`
  have hA : 3 * (4 * (S * (r * r * k))) ≤ 2 * (N * r) * (6 * r * q * k) := by
    have h1 : S * (r * r * k) ≤ N * q * (r * r * k) :=
      Nat.mul_le_mul_right _ (hS.trans (Nat.mul_le_mul_left _ hq1))
    calc 3 * (4 * (S * (r * r * k))) ≤ 3 * (4 * (N * q * (r * r * k))) := by omega
      _ = 2 * (N * r) * (6 * r * q * k) := by ring
  -- `2 N r · (6 r q k) + 2 N r ≤ 2 N r · D`
  have hB : 2 * (N * r) * (6 * r * q * k) + 2 * (N * r) ≤ 2 * (N * r) * D := by
    have hk1 : 6 * r * q * k + 1 ≤ D := hk
    have := Nat.mul_le_mul_left (2 * (N * r)) hk1
    rw [Nat.mul_add, Nat.mul_one] at this
    exact this
  -- `100 m ≤ 2 N r`
  have hC : 100 * m ≤ 2 * (N * r) := by
    have h1 : 100 * m ≤ 100 * (2 * C * N) := Nat.mul_le_mul_left _ hm
    have h2 : 100 * (2 * C * N) = 2 * N * (100 * C) := by ring
    have h3 : 2 * N * (100 * C) ≤ 2 * N * r := Nat.mul_le_mul_left _ hr
    calc 100 * m ≤ 2 * N * r := by omega
      _ = 2 * (N * r) := by ring
  -- `3 · 4 (2m + r|E|) D ≤ 36 m D` and `100 · 36 m D ≤ 72 N r D`
  have hE' : 4 * (2 * m + r * Ecard) * D ≤ 12 * (m * D) := by
    have : 4 * (2 * m + r * Ecard) ≤ 12 * m := by omega
    calc 4 * (2 * m + r * Ecard) * D ≤ 12 * m * D := Nat.mul_le_mul_right _ this
      _ = 12 * (m * D) := by ring
  have hF : 100 * (m * D) ≤ 2 * (N * r * D) := by
    have := Nat.mul_le_mul_right D hC
    calc 100 * (m * D) = 100 * m * D := by ring
      _ ≤ 2 * (N * r) * D := this
      _ = 2 * (N * r * D) := by ring
  have hNr : 0 < N * r := Nat.mul_pos hN (lt_of_lt_of_le (by omega) hr)
  have hG : 2 * (N * r) * D = 2 * (N * r * D) := by ring
  omega

/-- Summing a defect defined only at regular points. -/
theorem sum_dite_not_mem {P : Type*} [Fintype P] [DecidableEq P] (E : Finset P)
    [Fintype {z // z ∉ E}] (δ : {z // z ∉ E} → ℕ) :
    ∑ z, (if h : z ∈ E then 0 else δ ⟨z, h⟩) = ∑ z : {z // z ∉ E}, δ z := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun z => z ∈ E)
    (fun z => if h : z ∈ E then 0 else δ ⟨z, h⟩)]
  have h0 : ∀ i : {x // x ∈ E}, (if h : i.val ∈ E then 0 else δ ⟨i.val, h⟩) = 0 :=
    fun i => dif_pos i.2
  simp only [h0, Finset.sum_const_zero, zero_add]
  convert Fintype.sum_equiv (Equiv.refl {z // z ∉ E})
    (fun i => if h : i.val ∈ E then 0 else δ ⟨i.val, h⟩) δ (fun i => dif_neg i.2)

end Budget

end NonSofic
