import FiniteLean.GroupTheory.OAI.GroupTheory.Hyperbolic.MatrixRank

/-! Core of `thm:collapse` over an arbitrary ring `R` with `c : ZMod q →+* R`: abstract rank
function `RankFn`, certificate identity `∑_z H(z) ⊗ Z(z) = -⊕_i Y_i` (`certificate_identity`,
`H(z) ⊗ Z = (f ⊗ I) Z (fᵀ ⊗ I)` by `weighted_eq`), `rk_sum_le_certificate`, local
factorization `block_sum_factor` (inner dimension 1 per block), `rk_two_blocks_le`. -/

namespace NonSofic

open OAI.Release075
open scoped BigOperators

/-- Abstract Sylvester matrix rank function on a ring `R`. -/
structure RankFn (R : Type*) [Ring R] where
  rk : ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n],
    Matrix m n R → ℝ
  add_le : ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B : Matrix m n R), rk (A + B) ≤ rk A + rk B
  mul_le_left : ∀ {m n p : Type} [Fintype m] [Fintype n] [Fintype p] [DecidableEq m]
    [DecidableEq n] [DecidableEq p] (A : Matrix m n R) (B : Matrix n p R), rk (A * B) ≤ rk A
  mul_le_right : ∀ {m n p : Type} [Fintype m] [Fintype n] [Fintype p] [DecidableEq m]
    [DecidableEq n] [DecidableEq p] (A : Matrix m n R) (B : Matrix n p R), rk (A * B) ≤ rk B
  le_card_width : ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n R), rk A ≤ Fintype.card n
  sum_le_blockDiagonal : ∀ {m n o : Type} [Fintype m] [Fintype n] [Fintype o] [DecidableEq m]
    [DecidableEq n] [DecidableEq o] (Y : o → Matrix m n R),
    ∑ k, rk (Y k) ≤ rk (Matrix.blockDiagonal Y)

namespace RankFn

variable {R : Type*} [Ring R] (ρ : RankFn R)

theorem rk_zero_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    ρ.rk (0 : Matrix m n R) ≤ 0 := by
  have h0 : (0 : Matrix m n R) = (0 : Matrix m (Fin 0) R) * (0 : Matrix (Fin 0) n R) :=
    (Matrix.zero_mul _).symm
  rw [h0]
  refine (ρ.mul_le_left _ _).trans ?_
  simpa using ρ.le_card_width (0 : Matrix m (Fin 0) R)

theorem rk_sum_le {m n τ : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (s : Finset τ) (A : τ → Matrix m n R) : ρ.rk (∑ t ∈ s, A t) ≤ ∑ t ∈ s, ρ.rk (A t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ρ.rk_zero_le
  | @insert t s ht ih =>
    rw [Finset.sum_insert ht, Finset.sum_insert ht]
    exact (ρ.add_le _ _).trans (by linarith)

theorem rk_neg_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n R) : ρ.rk (-A) ≤ ρ.rk A := by
  have h : -A = A * (-1 : Matrix n n R) := by rw [Matrix.mul_neg, Matrix.mul_one]
  rw [h]
  exact ρ.mul_le_left _ _

end RankFn

section Certificate

variable {R : Type*} [Ring R] {q : ℕ} [NeZero q]

/-- The image of `ZMod q` is central. -/
theorem zmod_image_comm (c : ZMod q →+* R) (x : ZMod q) (y : R) : y * c x = c x * y := by
  rw [← ZMod.natCast_zmod_val x, map_natCast]
  exact (Nat.cast_commute x.val y).symm.eq

/-- `H(z) ⊗ Z` for `H(z) = f(z) f(z)ᵀ` (block index second). -/
def weighted (c : ZMod q →+* R) {I : Type} {r : ℕ} (f : I → ZMod q)
    (Z : Matrix (Fin r) (Fin r) R) : Matrix (Fin r × I) (Fin r × I) R :=
  Matrix.of fun x y => c (f x.2) * Z x.1 y.1 * c (f y.2)

/-- `f ⊗ I_r`. -/
def weightLeft (c : ZMod q →+* R) {I : Type} {r : ℕ} (f : I → ZMod q) :
    Matrix (Fin r × I) (Fin r) R :=
  Matrix.of fun x a' => if x.1 = a' then c (f x.2) else 0

/-- `fᵀ ⊗ I_r`. -/
def weightRight (c : ZMod q →+* R) {I : Type} {r : ℕ} (f : I → ZMod q) :
    Matrix (Fin r) (Fin r × I) R :=
  Matrix.of fun b' y => if b' = y.1 then c (f y.2) else 0

/-- `H(z) ⊗ Z = (f ⊗ I) Z (fᵀ ⊗ I)`. -/
theorem weighted_eq (c : ZMod q →+* R) {I : Type} [Fintype I] {r : ℕ} (f : I → ZMod q)
    (Z : Matrix (Fin r) (Fin r) R) :
    weighted c f Z = weightLeft c f * Z * weightRight c f := by
  ext ⟨a, j⟩ ⟨b, k⟩
  simp [weighted, weightLeft, weightRight, Matrix.mul_apply, ite_mul, mul_ite]

/-- **The certificate identity over `R`**: `∑_z H(z) ⊗ Z(z) = -⊕_i Y_i`. -/
theorem certificate_identity (c : ZMod q →+* R) {P I : Type} [Fintype P] [Fintype I]
    [DecidableEq I] {r : ℕ} (inc : P → Finset I) (f : P → I → ZMod q)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0))
    (Y : I → Matrix (Fin r) (Fin r) R) :
    (∑ z, weighted c (f z) (∑ i ∈ inc z, Y i)) = -Matrix.blockDiagonal Y := by
  ext ⟨a, j⟩ ⟨b, k⟩
  rw [Matrix.sum_apply, Matrix.neg_apply, Matrix.blockDiagonal_apply']
  simp only [weighted, Matrix.of_apply]
  calc ∑ z, c (f z j) * (∑ i ∈ inc z, Y i) a b * c (f z k)
      = ∑ z, ∑ i, (if i ∈ inc z then c (f z j * f z k) else 0) * Y i a b := by
        apply Finset.sum_congr rfl
        intro z _
        rw [mul_assoc, zmod_image_comm c, ← mul_assoc, ← map_mul c, Matrix.sum_apply,
          Finset.mul_sum]
        simp_rw [ite_mul, zero_mul]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ i, (∑ z, if i ∈ inc z then c (f z j * f z k) else 0) * Y i a b := by
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
    _ = ∑ i, (if j = i ∧ k = i then -Y i a b else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        have hc : (∑ z, if i ∈ inc z then c (f z j * f z k) else 0) =
            c (-(if j = i ∧ k = i then 1 else 0)) := by
          rw [← hline i j k, map_sum]
          apply Finset.sum_congr rfl
          intro z _
          split_ifs <;> simp
        rw [hc]
        split_ifs <;> simp
    _ = -(if j = k then Y j a b else 0) := by
        by_cases hjk : j = k
        · subst hjk
          simp
        · rw [if_neg hjk]
          simp only [neg_zero]
          exact Finset.sum_eq_zero (fun i _ => if_neg (fun h => hjk (h.1.trans h.2.symm)))

/-- **Certificate step of `thm:collapse`**: `∑_i rk Y_i ≤ ∑_z rk Z(z)` for every rank function. -/
theorem rk_sum_le_certificate (c : ZMod q →+* R) (ρ : RankFn R) {P I : Type} [Fintype P]
    [Fintype I] [DecidableEq I] {r : ℕ} (inc : P → Finset I) (f : P → I → ZMod q)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0))
    (Y : I → Matrix (Fin r) (Fin r) R) :
    ∑ i, ρ.rk (Y i) ≤ ∑ z, ρ.rk (∑ i ∈ inc z, Y i) := by
  classical
  have hid := certificate_identity c inc f hline Y
  have hbd : Matrix.blockDiagonal Y = -(∑ z, weighted c (f z) (∑ i ∈ inc z, Y i)) := by
    rw [hid, neg_neg]
  calc ∑ i, ρ.rk (Y i) ≤ ρ.rk (Matrix.blockDiagonal Y) := ρ.sum_le_blockDiagonal Y
    _ ≤ ρ.rk (∑ z, weighted c (f z) (∑ i ∈ inc z, Y i)) := by
        rw [hbd]
        exact ρ.rk_neg_le _
    _ ≤ ∑ z, ρ.rk (weighted c (f z) (∑ i ∈ inc z, Y i)) := ρ.rk_sum_le _ _
    _ ≤ ∑ z, ρ.rk (∑ i ∈ inc z, Y i) := by
        apply Finset.sum_le_sum
        intro z _
        rw [weighted_eq]
        exact (ρ.mul_le_left _ _).trans (ρ.mul_le_right _ _)

end Certificate

section Blocks

variable {R : Type*} [Ring R]

/-- **Local factorization**: a Cartesian block of exact relations `Y_i(u,v) =
L(u, α(i)+v) R(v, β(i)+u)` sums to a column times a row (inner dimension one). -/
theorem block_sum_factor {I : Type} {r : ℕ} (b : CartesianBlock I r)
    (Y : I → Matrix (Fin r) (Fin r) R) (L : Fin r → ZMod b.s → R) (Rr : Fin r → ZMod b.t → R)
    (hY : ∀ (i : b.labels) u v, Y i u v =
      L u ((b.coordinates i).1 + (v.val : ZMod b.s)) *
        Rr v ((b.coordinates i).2 + (u.val : ZMod b.t))) :
    ∑ i ∈ b.labels, Y i =
      (Matrix.of fun u (_ : Fin 1) => ∑ j, L u j) * (Matrix.of fun (_ : Fin 1) v => ∑ k, Rr v k) := by
  ext u v
  rw [Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_one]
  simp only [Matrix.of_apply]
  calc (∑ i ∈ b.labels, Y i u v) = ∑ i : b.labels, Y i u v :=
        (Finset.sum_coe_sort b.labels (fun i => Y i u v)).symm
    _ = ∑ i : b.labels, (fun p : ZMod b.s × ZMod b.t => L u p.1 * Rr v p.2) (b.shifted u v i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hY i u v).trans rfl
    _ = ∑ p : ZMod b.s × ZMod b.t, L u p.1 * Rr v p.2 :=
        Equiv.sum_comp (b.shifted u v) (fun p : ZMod b.s × ZMod b.t => L u p.1 * Rr v p.2)
    _ = ∑ j, ∑ k, L u j * Rr v k := Fintype.sum_prod_type _
    _ = (∑ j, L u j) * (∑ k, Rr v k) := by rw [Finset.sum_mul_sum]

theorem rk_block_le_one (ρ : RankFn R) {I : Type} {r : ℕ} (b : CartesianBlock I r)
    (Y : I → Matrix (Fin r) (Fin r) R) (L : Fin r → ZMod b.s → R) (Rr : Fin r → ZMod b.t → R)
    (hY : ∀ (i : b.labels) u v, Y i u v =
      L u ((b.coordinates i).1 + (v.val : ZMod b.s)) *
        Rr v ((b.coordinates i).2 + (u.val : ZMod b.t))) :
    ρ.rk (∑ i ∈ b.labels, Y i) ≤ 1 := by
  rw [block_sum_factor b Y L Rr hY]
  refine (ρ.mul_le_left _ _).trans ?_
  simpa using ρ.le_card_width (Matrix.of fun u (_ : Fin 1) => ∑ j, L u j)

/-- Two blocks at a regular point: `rk Z(z) ≤ 2`. -/
theorem rk_two_blocks_le (ρ : RankFn R) {I : Type} [DecidableEq I] {r : ℕ} (A : Finset I)
    (Y : I → Matrix (Fin r) (Fin r) R) (b₀ b₁ : CartesianBlock I r)
    (hdis : Disjoint b₀.labels b₁.labels) (hunion : b₀.labels ∪ b₁.labels = A)
    (L₀ : Fin r → ZMod b₀.s → R) (R₀ : Fin r → ZMod b₀.t → R)
    (L₁ : Fin r → ZMod b₁.s → R) (R₁ : Fin r → ZMod b₁.t → R)
    (h₀ : ∀ (i : b₀.labels) u v, Y i u v =
      L₀ u ((b₀.coordinates i).1 + (v.val : ZMod b₀.s)) *
        R₀ v ((b₀.coordinates i).2 + (u.val : ZMod b₀.t)))
    (h₁ : ∀ (i : b₁.labels) u v, Y i u v =
      L₁ u ((b₁.coordinates i).1 + (v.val : ZMod b₁.s)) *
        R₁ v ((b₁.coordinates i).2 + (u.val : ZMod b₁.t))) :
    ρ.rk (∑ i ∈ A, Y i) ≤ 2 := by
  rw [← hunion, Finset.sum_union hdis]
  have := (ρ.add_le _ _).trans (add_le_add (rk_block_le_one ρ b₀ Y L₀ R₀ h₀)
    (rk_block_le_one ρ b₁ Y L₁ R₁ h₁))
  linarith

/-- `∑_z (if z ∈ E then a else b) = |P| b + |E| (a - b)`. -/
theorem sum_ite_mem_const {P : Type*} [Fintype P] [DecidableEq P] (E : Finset P) (a b : ℝ) :
    ∑ z, (if z ∈ E then a else b) = Fintype.card P * b + E.card * (a - b) := by
  have h : ∀ z, (if z ∈ E then a else b) = b + (if z ∈ E then a - b else 0) := by
    intro z
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun z _ => h z), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul]

end Blocks

end NonSofic
