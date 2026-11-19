import Mathlib
import AJHandoff.TorusQuantum.PairQFormula
import AJHandoff.TorusQuantum.PairQTOrderFormula
import AJHandoff.TorusQuantum.PairQReducedDegree
import AJTwist.Select.TwSInput

/-!
# The exact colour growth of the reduced satellite sequence

Source: eq. (actual-eta-plus) of Section 6.1 and the display of Section 6.2 of `selection.tex`
(revision 5):

* right-handed companion, `a ≥ 1`: `ν(F_N) = -(N-1)(a N - 1)` (leading coefficient `1`), i.e.
  order `-4 (N-1)(a N - 1)` at `t = 0`;
* mirror companion, `a = -b < 0`: `ν_∞(F_N) = -(b + 1/2) N (N-1)` (leading coefficient
  `(-1)^(N-1)`), i.e. degree `(4b + 2) N (N-1)` in `t`.

Both are stated for an arbitrary input of the exact order (degree) `∓ 4 a n(n+1)`: the term
`n = j` is the unique extremal term of `D_j`, and `j = N - 1` the unique extremal term of `F_N`
(as in the library's `pairQ_tOrder_reducedFormula`, the case `a = r s`, and
`pairQ_intDegree_reducedFormula`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-! ### The order at `t = 0` -/

/-- A power of `-1` is nonzero of order `0`. -/
private theorem pairQTOrder_neg_one_pow_twsAct (n : ℕ) :
    (-1 : RatFunc ℚ) ^ n ≠ 0 ∧ pairQTOrder ((-1 : RatFunc ℚ) ^ n) = 0 := by
  have h1 : pairQTOrder (1 : RatFunc ℚ) = 0 := by simpa using pairQTOrder_X_zpow 0
  refine ⟨pow_ne_zero n (neg_ne_zero.mpr one_ne_zero), ?_⟩
  rcases neg_one_pow_eq_or (RatFunc ℚ) n with h | h
  · rw [h, h1]
  · rw [h, pairQTOrder_neg, h1]

/-- Twice the exponent `n(n+1)/2` is `n(n+1)`. -/
private theorem two_mul_triangle_twsAct (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ℤ) * 2 = (n : ℤ) * ((n : ℤ) + 1) := by
  exact_mod_cast Nat.div_two_mul_two_of_even (Nat.even_mul_succ_self n)

/-- The term `n` of the sum defining `D_j` is nonzero of order `2n(n+1) - 4a n(n+1)`. -/
private theorem pairQTOrder_cycloCoeff_term_twsAct {u : ℕ → RatFunc ℚ} {a : ℤ}
    (hu : ∀ n : ℕ, u n ≠ 0 ∧ pairQTOrder (u n) = -4 * a * n * ((n : ℤ) + 1)) (j n : ℕ) :
    (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) ≠ 0 ∧
      pairQTOrder ((-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))) =
        2 * (n : ℤ) * ((n : ℤ) + 1) - 4 * a * n * ((n : ℤ) + 1) := by
  have h := pairQTOrder_div_eq
    (pairQTOrder_mul_eq (pairQTOrder_mul_eq (pairQTOrder_neg_one_pow_twsAct n)
      (pairQTOrder_qParam_pow_eq (n * (n + 1) / 2))) (hu n))
    (pairQTOrder_mul_eq (pairQTOrder_qPochhammer_qParam (j - n))
      (pairQTOrder_qPochhammer_qParam (j + n + 1)))
  refine ⟨h.1, h.2.trans ?_⟩
  linear_combination 2 * two_mul_triangle_twsAct n

/-- The sum defining `D_j` is nonzero of order `2j(j+1) - 4a j(j+1)`: its term `n = j` has the
least order. -/
private theorem pairQTOrder_cycloCoeff_sum_twsAct {u : ℕ → RatFunc ℚ} {a : ℤ} (ha : 1 ≤ a)
    (hu : ∀ n : ℕ, u n ≠ 0 ∧ pairQTOrder (u n) = -4 * a * n * ((n : ℤ) + 1)) (j : ℕ) :
    ∑ n ∈ Finset.range (j + 1), (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) ≠ 0 ∧
      pairQTOrder (∑ n ∈ Finset.range (j + 1),
        (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
          (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))) =
        2 * (j : ℤ) * ((j : ℤ) + 1) - 4 * a * j * ((j : ℤ) + 1) := by
  refine pairQTOrder_sum_eq_of_lt (a := j) (Finset.mem_range.mpr (by omega))
    (pairQTOrder_cycloCoeff_term_twsAct hu j j) fun n hn hnj ↦ Or.inr ?_
  rw [(pairQTOrder_cycloCoeff_term_twsAct hu j n).2]
  have hn' : (n : ℤ) + 1 ≤ j := by
    have := Finset.mem_range.mp hn
    omega
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have h1 : (n : ℤ) * ((n : ℤ) + 1) < (j : ℤ) * ((j : ℤ) + 1) := by nlinarith
  have h2 := mul_pos (show (0 : ℤ) < 4 * a - 2 by omega) (sub_pos.mpr h1)
  linarith

/-- `D_j` is nonzero of order `4j - 2(2a - 1) j(j+1)`. -/
private theorem pairQTOrder_cycloCoeff_twsAct {u : ℕ → RatFunc ℚ} {a : ℤ} (ha : 1 ≤ a)
    (hu : ∀ n : ℕ, u n ≠ 0 ∧ pairQTOrder (u n) = -4 * a * n * ((n : ℤ) + 1)) (j : ℕ) :
    pairQCycloCoeff u j ≠ 0 ∧
      pairQTOrder (pairQCycloCoeff u j) =
        4 * (j : ℤ) - 2 * (2 * a - 1) * j * ((j : ℤ) + 1) := by
  have h1 := pairQTOrder_one_sub_qParam_zpow_of_pos (k := 1) one_pos
  rw [zpow_one] at h1
  have h := pairQTOrder_mul_eq (pairQTOrder_mul_eq
    (pairQTOrder_mul_eq (pairQTOrder_qParam_pow_eq j) h1)
    (pairQTOrder_qPochhammer_qParam j)) (pairQTOrder_cycloCoeff_sum_twsAct ha hu j)
  refine ⟨h.1, h.2.trans ?_⟩
  ring

/-- The cyclotomic kernel `C_j(N)`, `j < N`, is nonzero of order `2j(j+1) - 4jN`. -/
private theorem pairQTOrder_cyclotomicKernel_of_lt_twsAct {N : ℕ} (j : ℕ) (hj : j < N) :
    cyclotomicKernel j N ≠ 0 ∧ pairQTOrder (cyclotomicKernel j N) =
      2 * (j : ℤ) * ((j : ℤ) + 1) - 4 * (j : ℤ) * N := by
  induction j with
  | zero =>
    rw [cyclotomicKernel, Finset.Icc_eq_empty (by omega), Finset.prod_empty]
    exact ⟨one_ne_zero, by simpa using pairQTOrder_X_zpow 0⟩
  | succ j ih =>
    have h1 := pairQTOrder_one_sub_qParam_zpow_of_pos (k := ((j + 1 : ℕ) : ℤ) + N) (by omega)
    have h2 := pairQTOrder_one_sub_qParam_zpow_of_neg (k := ((j + 1 : ℕ) : ℤ) - N) (by omega)
    have h3 := pairQTOrder_mul_eq (ih (by omega)) (pairQTOrder_mul_eq h1 h2)
    rw [cyclotomicKernel, Finset.prod_Icc_succ_top (by omega)]
    refine ⟨h3.1, h3.2.trans ?_⟩
    push_cast
    ring

/-- If `u_n` is nonzero of order `-4 a n(n+1)` at `t = 0` with `a ≥ 1`, the finite transform
`F_N` is nonzero of order `-4 (N-1)(a N - 1)`. -/
theorem tws_tOrder_reducedFormula_of_input {u : ℕ → RatFunc ℚ} {a : ℤ} (ha : 1 ≤ a)
    (hu : ∀ n : ℕ, u n ≠ 0 ∧ pairQTOrder (u n) = -4 * a * n * ((n : ℤ) + 1)) {N : ℕ}
    (hN : 1 ≤ N) :
    pairQReducedFormula u N ≠ 0 ∧
      pairQTOrder (pairQReducedFormula u N) = -4 * ((N : ℤ) - 1) * (a * N - 1) := by
  have hterm : ∀ j : ℕ, j < N → cyclotomicKernel j N * pairQCycloCoeff u j ≠ 0 ∧
      pairQTOrder (cyclotomicKernel j N * pairQCycloCoeff u j) =
        4 * (j : ℤ) - 4 * (j : ℤ) * N - 4 * (a - 1) * j * ((j : ℤ) + 1) :=
    fun j hj ↦ by
      have h := pairQTOrder_mul_eq (pairQTOrder_cyclotomicKernel_of_lt_twsAct j hj)
        (pairQTOrder_cycloCoeff_twsAct ha hu j)
      refine ⟨h.1, h.2.trans ?_⟩
      ring
  rw [pairQReducedFormula]
  refine pairQTOrder_sum_eq_of_lt (a := N - 1) (Finset.mem_range.mpr (by omega))
    ⟨(hterm (N - 1) (by omega)).1, ?_⟩ fun j hj hjN ↦ Or.inr ?_
  · rw [(hterm (N - 1) (by omega)).2, Nat.cast_sub hN]
    push_cast
    ring
  · have hj' : j < N := Finset.mem_range.mp hj
    rw [(hterm j hj').2]
    have h1 : (j : ℤ) + 2 ≤ N := by omega
    have h2 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    have h3 : (j : ℤ) * ((j : ℤ) + 1) ≤ ((N : ℤ) - 1) * N := by nlinarith
    have h4 : (j : ℤ) * ((N : ℤ) - 1) < ((N : ℤ) - 1) * ((N : ℤ) - 1) :=
      mul_lt_mul_of_pos_right (by omega) (by omega)
    have h5 : (a - 1) * ((j : ℤ) * ((j : ℤ) + 1)) ≤ (a - 1) * (((N : ℤ) - 1) * N) :=
      mul_le_mul_of_nonneg_left h3 (by omega)
    linarith

/-! ### The degree -/

/-- A natural power of `q` is nonzero of degree `4k` in `t`. -/
private theorem intDegree_qParam_pow_twsAct (k : ℕ) :
    qParam ^ k ≠ 0 ∧ (qParam ^ k).intDegree = 4 * (k : ℤ) :=
  ⟨pow_ne_zero k qParam_ne_zero, by rw [← zpow_natCast, intDegree_qParam_zpow]⟩

/-- `1 - q^k`, `k > 0`, is nonzero of degree `4k` in `t`. -/
private theorem intDegree_one_sub_qParam_zpow_of_pos_twsAct {k : ℤ} (hk : 0 < k) :
    1 - qParam ^ k ≠ 0 ∧ (1 - qParam ^ k).intDegree = 4 * k := by
  rw [sub_eq_neg_add]
  refine intDegree_add_eq_of_lt
    ⟨neg_ne_zero.mpr (zpow_ne_zero k qParam_ne_zero), ?_⟩ (Or.inr ?_)
  · rw [RatFunc.intDegree_neg, intDegree_qParam_zpow]
  · rw [RatFunc.intDegree_one]
    omega

/-- `1 - q^k`, `k < 0`, is nonzero of degree `0` in `t`. -/
private theorem intDegree_one_sub_qParam_zpow_of_neg_twsAct {k : ℤ} (hk : k < 0) :
    1 - qParam ^ k ≠ 0 ∧ (1 - qParam ^ k).intDegree = 0 := by
  rw [sub_eq_add_neg]
  refine intDegree_add_eq_of_lt ⟨one_ne_zero, RatFunc.intDegree_one⟩ (Or.inr ?_)
  rw [RatFunc.intDegree_neg, intDegree_qParam_zpow]
  omega

/-- The `q`-Pochhammer symbol `(q; q)_k` is nonzero of degree `2k(k+1)` in `t`. -/
private theorem intDegree_qPochhammer_qParam_twsAct (k : ℕ) :
    qPochhammer qParam k ≠ 0 ∧
      (qPochhammer qParam k).intDegree = 2 * (k : ℤ) * ((k : ℤ) + 1) := by
  induction k with
  | zero =>
    rw [qPochhammer, Finset.prod_range_zero]
    exact ⟨one_ne_zero, by rw [RatFunc.intDegree_one]; simp⟩
  | succ k ih =>
    have h1 := intDegree_one_sub_qParam_zpow_of_pos_twsAct (k := (k : ℤ) + 1) (by omega)
    rw [zpow_add₀ qParam_ne_zero, zpow_one, zpow_natCast, mul_comm] at h1
    have h2 := intDegree_mul_eq ih h1
    rw [qPochhammer, Finset.prod_range_succ]
    refine ⟨h2.1, h2.2.trans ?_⟩
    push_cast
    ring

/-- A power of `-1` is nonzero of degree `0`. -/
private theorem intDegree_neg_one_pow_twsAct (n : ℕ) :
    (-1 : RatFunc ℚ) ^ n ≠ 0 ∧ ((-1 : RatFunc ℚ) ^ n).intDegree = 0 := by
  refine ⟨pow_ne_zero n (neg_ne_zero.mpr one_ne_zero), ?_⟩
  rcases neg_one_pow_eq_or (RatFunc ℚ) n with h | h
  · rw [h, RatFunc.intDegree_one]
  · rw [h, RatFunc.intDegree_neg, RatFunc.intDegree_one]

/-- The term `n ≤ j` of the sum defining `D_j` is nonzero of degree
`(4b - 2) n(n+1) - 4(j+1)²` in `t`. -/
private theorem intDegree_cycloCoeff_term_twsAct {u : ℕ → RatFunc ℚ} {b : ℤ}
    (hu : ∀ n : ℕ, u n ≠ 0 ∧ (u n).intDegree = 4 * b * n * ((n : ℤ) + 1)) {j n : ℕ}
    (hn : n ≤ j) :
    (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) ≠ 0 ∧
      ((-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))).intDegree =
        (4 * b - 2) * n * ((n : ℤ) + 1) - 4 * ((j : ℤ) + 1) ^ 2 := by
  have h := intDegree_div_eq
    (intDegree_mul_eq (intDegree_mul_eq (intDegree_neg_one_pow_twsAct n)
      (intDegree_qParam_pow_twsAct (n * (n + 1) / 2))) (hu n))
    (intDegree_mul_eq (intDegree_qPochhammer_qParam_twsAct (j - n))
      (intDegree_qPochhammer_qParam_twsAct (j + n + 1)))
  refine ⟨h.1, h.2.trans ?_⟩
  rw [Nat.cast_sub hn, Nat.cast_add, Nat.cast_add, Nat.cast_one]
  linear_combination 2 * two_mul_triangle_twsAct n

/-- The sum defining `D_j` is nonzero of degree `(4b - 2) j(j+1) - 4(j+1)²`: its term `n = j`
dominates. -/
private theorem intDegree_cycloCoeff_sum_twsAct {u : ℕ → RatFunc ℚ} {b : ℤ} (hb : 1 ≤ b)
    (hu : ∀ n : ℕ, u n ≠ 0 ∧ (u n).intDegree = 4 * b * n * ((n : ℤ) + 1)) (j : ℕ) :
    ∑ n ∈ Finset.range (j + 1), (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) ≠ 0 ∧
      (∑ n ∈ Finset.range (j + 1), (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))).intDegree =
        (4 * b - 2) * j * ((j : ℤ) + 1) - 4 * ((j : ℤ) + 1) ^ 2 := by
  refine intDegree_sum_eq_of_lt (a := j) (Finset.mem_range.mpr (by omega))
    (intDegree_cycloCoeff_term_twsAct hu le_rfl) fun n hn hnj ↦ Or.inr ?_
  have hnj' : n ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  rw [(intDegree_cycloCoeff_term_twsAct hu hnj').2]
  have hn' : (n : ℤ) + 1 ≤ j := by omega
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have h1 : (n : ℤ) * ((n : ℤ) + 1) < (j : ℤ) * ((j : ℤ) + 1) := by nlinarith
  have h2 := mul_pos (show (0 : ℤ) < 4 * b - 2 by omega) (sub_pos.mpr h1)
  linarith

/-- `D_j` is nonzero of degree `(4b - 4) j(j+1)` in `t`. -/
private theorem intDegree_cycloCoeff_twsAct {u : ℕ → RatFunc ℚ} {b : ℤ} (hb : 1 ≤ b)
    (hu : ∀ n : ℕ, u n ≠ 0 ∧ (u n).intDegree = 4 * b * n * ((n : ℤ) + 1)) (j : ℕ) :
    pairQCycloCoeff u j ≠ 0 ∧
      (pairQCycloCoeff u j).intDegree = (4 * b - 4) * j * ((j : ℤ) + 1) := by
  have h1 := intDegree_one_sub_qParam_zpow_of_pos_twsAct (k := 1) one_pos
  rw [zpow_one] at h1
  have h := intDegree_mul_eq (intDegree_mul_eq
    (intDegree_mul_eq (intDegree_qParam_pow_twsAct j) h1)
    (intDegree_qPochhammer_qParam_twsAct j)) (intDegree_cycloCoeff_sum_twsAct hb hu j)
  refine ⟨h.1, h.2.trans ?_⟩
  ring

/-- The cyclotomic kernel `C_j(N)`, `j < N`, is nonzero of degree `4jN + 2j(j+1)` in `t`. -/
private theorem intDegree_cyclotomicKernel_of_lt_twsAct {N : ℕ} (j : ℕ) (hj : j < N) :
    cyclotomicKernel j N ≠ 0 ∧ (cyclotomicKernel j N).intDegree =
      4 * (j : ℤ) * N + 2 * (j : ℤ) * ((j : ℤ) + 1) := by
  induction j with
  | zero =>
    rw [cyclotomicKernel, Finset.Icc_eq_empty (by omega), Finset.prod_empty]
    exact ⟨one_ne_zero, by rw [RatFunc.intDegree_one]; simp⟩
  | succ j ih =>
    have h1 := intDegree_one_sub_qParam_zpow_of_pos_twsAct
      (k := ((j + 1 : ℕ) : ℤ) + N) (by omega)
    have h2 := intDegree_one_sub_qParam_zpow_of_neg_twsAct
      (k := ((j + 1 : ℕ) : ℤ) - N) (by omega)
    have h3 := intDegree_mul_eq (ih (by omega)) (intDegree_mul_eq h1 h2)
    rw [cyclotomicKernel, Finset.prod_Icc_succ_top (by omega)]
    refine ⟨h3.1, h3.2.trans ?_⟩
    push_cast
    ring

/-- If `u_n` is nonzero of degree `4 b n(n+1)` with `b ≥ 1`, the finite transform `F_N` is
nonzero of degree `(4b + 2) N (N-1)`. -/
theorem tws_intDegree_reducedFormula_of_input {u : ℕ → RatFunc ℚ} {b : ℤ} (hb : 1 ≤ b)
    (hu : ∀ n : ℕ, u n ≠ 0 ∧ (u n).intDegree = 4 * b * n * ((n : ℤ) + 1)) {N : ℕ}
    (hN : 1 ≤ N) :
    pairQReducedFormula u N ≠ 0 ∧
      (pairQReducedFormula u N).intDegree = (4 * b + 2) * N * ((N : ℤ) - 1) := by
  have hterm : ∀ j : ℕ, j < N → cyclotomicKernel j N * pairQCycloCoeff u j ≠ 0 ∧
      (cyclotomicKernel j N * pairQCycloCoeff u j).intDegree =
        4 * (j : ℤ) * N + (4 * b - 2) * j * ((j : ℤ) + 1) :=
    fun j hj ↦ by
      have h := intDegree_mul_eq (intDegree_cyclotomicKernel_of_lt_twsAct j hj)
        (intDegree_cycloCoeff_twsAct hb hu j)
      refine ⟨h.1, h.2.trans ?_⟩
      ring
  rw [pairQReducedFormula]
  refine intDegree_sum_eq_of_lt (a := N - 1) (Finset.mem_range.mpr (by omega))
    ⟨(hterm (N - 1) (by omega)).1, ?_⟩ fun j hj hjN ↦ Or.inr ?_
  · rw [(hterm (N - 1) (by omega)).2, Nat.cast_sub hN]
    push_cast
    ring
  · have hj' : j < N := Finset.mem_range.mp hj
    rw [(hterm j hj').2]
    have h1 : (j : ℤ) + 2 ≤ N := by omega
    have h2 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    have h3 : (j : ℤ) * ((j : ℤ) + 1) ≤ ((N : ℤ) - 1) * N := by nlinarith
    have h4 : (j : ℤ) * N < ((N : ℤ) - 1) * N :=
      mul_lt_mul_of_pos_right (by omega) (by omega)
    have h5 : (4 * b - 2) * ((j : ℤ) * ((j : ℤ) + 1)) ≤ (4 * b - 2) * (((N : ℤ) - 1) * N) :=
      mul_le_mul_of_nonneg_left h3 (by omega)
    linarith

end AJConjecture
