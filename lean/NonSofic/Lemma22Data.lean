import FiniteLean.GroupTheory.OAI.GroupTheory.Hyperbolic.Incidence

/-!
# The data of OpenAI's Lemma 2.2 with the numerical facts used by `thm:quant`

OpenAI's `exists_markedLineData` returns some `MarkedLineData q r` (with `r = 200·200²⁰`) but
records only the budget.  Its alteration step `exists_alteration_budget` picks `ω` with
`cost ω < |S| r - 8 m`, which does not give `r |E| ≤ m`.  Here the same random construction is
run with `ω` chosen so that `cost ω < 𝔼 cost + 1`; then

* `4 r |E| ≤ m` (`exceptionalPoints_card_le`, and the two bounds `hfirst`, `hsecond` from the
  proof of `incidence_numeric_budget`, re-proved here as `numeric_halves`),
* `2·200²⁰·|deletedMarks| < m`, hence `m ≤ 2·200²⁰·N` (`retained_card`, `floor_grid_lower`),
* the budget `4 (2m + r|E|) < N r` follows.

Only OAI's exported lemmas are used; the hexp computation of `exists_alteration_budget` and the
bounds `hfirst`/`hsecond` of `incidence_numeric_budget` are internal to OAI's proofs and are
copied below (marked "copied from OAI", Apache-2.0, openai/math @adc7f12, Incidence.lean).
-/

namespace NonSofic

open OAI.Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

section AlterationCost
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

/-- An alteration whose cost is at most its expectation (up to `+1`).  The expectation bound
`hexp` is copied from the proof of OAI's `exists_alteration_budget`. -/
theorem exists_alteration_cost (S : Finset V) (r T : ℕ) (μ B : ℝ)
    (hμ : 0 < μ) (hT : 2 * (T : ℝ) ≤ μ)
    (hlower : ∀ z : V, μ ≤ pointMean (K := K) S z)
    (hdel : (𝔼 ω : S → Projectivization K V, ((deletedMarks S ω).card : ℝ)) ≤ B) :
    ∃ ω : S → Projectivization K V,
      4*r*((Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card : ℝ) +
        r*(4*(Fintype.card K : ℝ)+1)*((deletedMarks S ω).card : ℝ) <
      16*r*(Fintype.card V : ℝ)/μ + r*(4*(Fintype.card K : ℝ)+1)*B + 1 := by
  let cost : (S → Projectivization K V) → ℝ := fun ω =>
    4*r*((Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card : ℝ) +
    r*(4*(Fintype.card K : ℝ)+1)*((deletedMarks S ω).card : ℝ)
  -- copied from OAI (`exists_alteration_budget`, Incidence.lean)
  have hexp : (𝔼 ω, cost ω) ≤ 16*r*(Fintype.card V : ℝ)/μ +
      r*(4*(Fintype.card K : ℝ)+1)*B := by
    simp only [cost, Finset.expect_add_distrib, ← Finset.mul_expect]
    have hlow := expect_lowDegree_le (K := K) S T μ hμ hT hlower
    have h₁ := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 4*(r : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hdel
      (show 0 ≤ (r : ℝ)*(4*(Fintype.card K : ℝ)+1) by positivity)
    convert add_le_add h₁ h₂ using 2; first | rfl | ring
  exact exists_of_expect_lt cost _ (by linarith)

end AlterationCost

/-- The bounds `hfirst` and `hsecond` from the proof of OAI's `incidence_numeric_budget`
(copied from OAI, Incidence.lean; there they are local `have`s, not exported). -/
theorem numeric_halves {q d r : ℝ} (hd : 1 ≤ d) (hr : r = 200*d) (hq : 1000*d*r^2 ≤ q) :
    2*(16*r*q^20/(q/(4*d))) ≤ q^20 ∧ 2*(r*(4*q+1)*(30*q^12)) ≤ q^20 := by
  have hd0 : 0 < d := by linarith
  have hr1 : 1 ≤ r := by rw [hr]; linarith
  have hr0 : 0 < r := by linarith
  have hrr : r ≤ r^2 := by nlinarith
  have hq128 : 128*r*d ≤ q := by
    calc
      _ ≤ 1000*d*r^2 := by nlinarith [mul_le_mul_of_nonneg_left hrr hd0.le]
      _ ≤ q := hq
  have hq300 : 300*r ≤ q := by
    have h₁ : 300*r ≤ 1000*d*r := by nlinarith
    exact h₁.trans ((mul_le_mul_of_nonneg_left hrr (by positivity : 0 ≤ 1000*d)).trans hq)
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hdp : 0 < 4*d := by positivity
  constructor
  · have hfirst_eq : 16*r*q^20/(q/(4*d)) = 64*r*d*q^19 := by
      field_simp
      ring
    rw [hfirst_eq]
    have h := mul_le_mul_of_nonneg_right hq128 (pow_nonneg hq0.le 19)
    nlinarith only [h]
  · have hq7 : q ≤ q^7 := by simpa using pow_le_pow_right₀ hq1 (show 1 ≤ 7 by norm_num)
    calc
      _ ≤ 300*r*q^13 := by
        have hh := mul_nonneg (show 0 ≤ 60*r*q^12 by positivity) (show 0 ≤ q-1 by linarith)
        nlinarith only [hh]
      _ ≤ q^7*q^13 := by gcongr; exact hq300.trans hq7
      _ = q^20 := by ring

theorem numeric_sum {q d r : ℝ} (hd : 1 ≤ d) (hr : r = 200*d) (hq : 1000*d*r^2 ≤ q) :
    16*r*q^20/(q/(4*d)) + r*(4*q+1)*(30*q^12) ≤ q^20 := by
  have h := numeric_halves hd hr hq
  linarith [h.1, h.2]

/-- Natural-number consequences of the cost bound `4 r L + r (4q+1) D < m + 1` (`r = 200 C`). -/
theorem lemma22_arith (C r q m L D E S N : ℕ) (hr : r = 200*C) (hm : 0 < m)
    (hcost : 4*r*L + r*(4*q+1)*D < m + 1) (hE : E ≤ L + q*D)
    (hS : m ≤ C*S) (hDS : D ≤ S) (hN : N = S - D) :
    4*(r*E) ≤ m ∧ m ≤ 2*C*N ∧ 4*(2*m+r*E) < N*r := by
  subst hr
  have hc : 4*(200*C)*L + 200*C*(4*q+1)*D ≤ m := Nat.lt_succ_iff.mp hcost
  have h1 : 800*C*E ≤ 800*C*(L + q*D) := Nat.mul_le_mul_left (800*C) hE
  have hCD : 200*C*D ≤ 200*C*(4*q+1)*D :=
    Nat.mul_le_mul_right D (Nat.le_mul_of_pos_right (200*C) (by omega))
  have hNS : N + D = S := by omega
  have h2 : 2*C*(N + D) = 2*C*S := by rw [hNS]
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **OpenAI's Lemma 2.2 data, with the facts used for `ε₀ = 1/(6rq)`.**  Same `r`, same prime
range, same random construction as OAI's `exists_markedLineData`; additionally
`m ≤ 2·200²⁰·N` and `4 r |E| ≤ m` (so `r |E| ≤ m`). -/
theorem exists_markedLineData_lemma22 :
    ∃ (q r : ℕ) (hq : q.Prime), let _ : Fact q.Prime := ⟨hq⟩
      r = 200*200^20 ∧ r < q ∧ 200 ≤ q ∧ ∃ d : MarkedLineData q r,
        q^20 ≤ 2*200^20*Fintype.card d.Label ∧ 4*(r*d.exceptional.card) ≤ q^20 := by
  classical
  let r : ℕ := 200*200^20
  have hrdef : r = 200*200^20 := rfl
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (1000*200^20*r^2+400)
  let : Fact q.Prime := ⟨hprime⟩
  let : Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q)) := Fintype.ofFinite _
  have hq200 : 200 ≤ q := by omega
  have hqbig : 1000*200^20*r^2 ≤ q := by omega
  have hrq : r < q := by
    have hh : r < 1000*200^20*r^2+400 := by norm_num [r]
    exact hh.trans_le hq
  obtain ⟨S,_,hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (ZMod q))) (n := q/100) (by
      simpa only [Finset.card_univ,ZMod.card] using Nat.div_le_self q 100)
  -- numerics, as in OAI's `large_prime_grid_outcome`
  have hM : (q : ℝ)^20 ≤ (200:ℝ)^20 * (gridMarks q S).card := by
    rw [gridMarks_card,hS,Nat.cast_pow]
    exact floor_grid_lower hq200
  have hr' : (r : ℝ) = 200*(200:ℝ)^20 := by exact_mod_cast hrdef
  have hq' : 1000*(200:ℝ)^20*(r:ℝ)^2 ≤ q := by exact_mod_cast hqbig
  have hn := incidence_numeric_budget (by norm_num : (1:ℝ) ≤ (200:ℝ)^20) hr' hq' hM
  have hsum := numeric_sum (by norm_num : (1:ℝ) ≤ (200:ℝ)^20) hr' hq'
  have hJ : (q : ℝ)^19 ≤ Fintype.card (Projectivization (ZMod q) (Fin 20 → ZMod q)) := by
    rw [directions_twenty_card]
    push_cast
    exact (geom_sum_twenty_bounds (by exact_mod_cast (show 2 ≤ q by omega))).1
  have hcycle := expect_deletedMarks_le (K := ZMod q) (gridMarks q S) (q : ℝ) (by
    intro s hs
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
    exact cycle_numeric_bound (by exact_mod_cast (show 1 ≤ q by omega)) hJ
      (Finset.mem_Icc.mp hs).2)
  obtain ⟨ω, hω⟩ := exists_alteration_cost (gridMarks q S) r (4*r^2) ((q:ℝ)/(4*(200:ℝ)^20))
    (30*(q:ℝ)^12) hn.1
    (by simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]; nlinarith only [hn.2.1])
    (mean_grid_lower q hq200 S hS) hcycle
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow] at hω
  -- the cost is below `m + 1`
  set L := (Finset.univ.filter (fun z => pointDegree (gridMarks q S) ω z < 4*r^2)).card
    with hL
  set D := (deletedMarks (gridMarks q S) ω).card with hD
  have hcostR := lt_of_lt_of_le hω (add_le_add hsum (le_refl (1 : ℝ)))
  have hcost : 4*r*L + r*(4*q+1)*D < q^20 + 1 := by exact_mod_cast hcostR
  have hE : (exceptionalPoints (gridMarks q S) ω (4*r^2)).card ≤ L + q*D := by
    simpa only [ZMod.card] using exceptionalPoints_card_le (gridMarks q S) ω (4*r^2)
  have hSn : q^20 ≤ 200^20*(gridMarks q S).card := by exact_mod_cast hM
  have hDS : D ≤ (gridMarks q S).card :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_coe _)
  have hpos : 0 < q^20 := pow_pos (Fact.out : q.Prime).pos 20
  obtain ⟨h4E, hN, hbud⟩ := lemma22_arith (200^20) r q (q^20) L D
    (exceptionalPoints (gridMarks q S) ω (4*r^2)).card (gridMarks q S).card
    (Fintype.card (Retained (gridMarks q S) ω)) hrdef hpos hcost hE hSn hDS
    (retained_card _ ω)
  refine ⟨q, r, hprime, hrdef, hrq, hq200, ?_⟩
  refine ⟨{ scalarGrid := S
            grid_card := hS
            Label := Retained (gridMarks q S) ω
            mark := fun i => i.val.val
            direction := fun i => ω i.val
            marks_mem := fun i => Fintype.mem_piFinset.mp i.val.property
            marks_injective := fun _ _ h => Subtype.ext (Subtype.ext h)
            exceptional := exceptionalPoints (gridMarks q S) ω (4*r^2)
            degree := retainedIncidence_card_ge (gridMarks q S) ω (4*r^2)
            budget := hbud
            girth := retained_girth (gridMarks q S) ω }, hN, h4E⟩

end

end NonSofic
