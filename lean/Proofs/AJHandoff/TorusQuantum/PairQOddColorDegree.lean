import Mathlib
import AJFamily.Quantum.TorusOddColorDegree
import AJHandoff.TorusQuantum.PairQFormula

/-!
# The degree in `t` of the odd colours of `T(r, s)`

For `r, s ≥ 1`: `u_n ≠ 0` and `deg_t u_n = 4(r + s - rs) n`. The term of index `k` of the sum in
`pairQOddColor` has degree `4rs k² + 4(r+s) k` for `k ≥ 0` and `4rs k² - 4(s-r) k - 4` for
`k < 0` (with `deg_t [l] = 2|l| - 2`); the maximum over `-n ≤ k ≤ n` is attained only at `k = n`
(`intDegree_sum_eq_of_lt`), and the prefactor contributes `-4rs n(n+1)`. As
`intDegree_torusOddColor`, whose instance is `(r, s) = (a, 2)`.
-/

noncomputable section

namespace AJConjecture

/-- An integer power of `t` is nonzero of degree its exponent. -/
private theorem intDegree_ratFuncX_zpow_pairQOdd (n : ℤ) :
    (RatFunc.X : RatFunc ℚ) ^ n ≠ 0 ∧ ((RatFunc.X : RatFunc ℚ) ^ n).intDegree = n := by
  refine ⟨zpow_ne_zero n RatFunc.X_ne_zero, ?_⟩
  have hnat : ∀ m : ℕ, ((RatFunc.X : RatFunc ℚ) ^ m).intDegree = m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero m RatFunc.X_ne_zero) RatFunc.X_ne_zero, ih,
        RatFunc.intDegree_X]
      push_cast
      rfl
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, hnat]
  · rw [zpow_neg, RatFunc.intDegree_inv, zpow_natCast, hnat]

/-- A difference of distinct powers of `t` is nonzero of degree the larger exponent. -/
private theorem intDegree_ratFuncX_zpow_sub_zpow_pairQOdd {a b : ℤ} (hab : a ≠ b) :
    (RatFunc.X : RatFunc ℚ) ^ a - RatFunc.X ^ b ≠ 0 ∧
      ((RatFunc.X : RatFunc ℚ) ^ a - RatFunc.X ^ b).intDegree = max a b := by
  have hlt : ∀ c d : ℤ, d < c → (RatFunc.X : RatFunc ℚ) ^ c - RatFunc.X ^ d ≠ 0 ∧
      ((RatFunc.X : RatFunc ℚ) ^ c - RatFunc.X ^ d).intDegree = c := by
    intro c d hdc
    rw [sub_eq_add_neg]
    refine intDegree_add_eq_of_lt (intDegree_ratFuncX_zpow_pairQOdd c) (Or.inr ?_)
    rwa [RatFunc.intDegree_neg, (intDegree_ratFuncX_zpow_pairQOdd d).2]
  rcases lt_or_gt_of_ne hab with h | h
  · have h1 := hlt b a h
    rw [max_eq_right h.le, ← neg_sub, RatFunc.intDegree_neg]
    exact ⟨neg_ne_zero.mpr h1.1, h1.2⟩
  · rw [max_eq_left h.le]
    exact hlt a b h

/-- The quantum integer `[m]`, `m ≠ 0`, is nonzero of degree `2|m| - 2` in `t`. -/
private theorem intDegree_quantumInt_pairQOdd {m : ℤ} (hm : m ≠ 0) :
    quantumInt m ≠ 0 ∧ (quantumInt m).intDegree = max (2 * m) (-(2 * m)) - 2 := by
  have h1 := intDegree_ratFuncX_zpow_sub_zpow_pairQOdd (a := 2 * m) (b := -(2 * m)) (by omega)
  have h2 := intDegree_ratFuncX_zpow_sub_zpow_pairQOdd (a := 2) (b := -2) (by omega)
  exact intDegree_div_eq h1 h2

/-- The term of index `k` of the sum defining `pairQOddColor r s` is nonzero of degree
`4rk(sk+1) + 2|2sk+1| - 2`. -/
private theorem intDegree_pairQOddColor_term (r s : ℕ) (k : ℤ) :
    qParam ^ ((r : ℤ) * k * ((s : ℤ) * k + 1)) * quantumInt (2 * (s : ℤ) * k + 1) ≠ 0 ∧
      (qParam ^ ((r : ℤ) * k * ((s : ℤ) * k + 1)) *
        quantumInt (2 * (s : ℤ) * k + 1)).intDegree =
        4 * ((r : ℤ) * k * ((s : ℤ) * k + 1)) +
          (max (2 * (2 * (s : ℤ) * k + 1)) (-(2 * (2 * (s : ℤ) * k + 1))) - 2) := by
  have hne : 2 * (s : ℤ) * k + 1 ≠ 0 := by
    rw [mul_assoc]
    omega
  exact intDegree_mul_eq ⟨zpow_ne_zero _ qParam_ne_zero, intDegree_qParam_zpow _⟩
    (intDegree_quantumInt_pairQOdd hne)

/-- The sum defining `pairQOddColor r s n` is nonzero of degree `4rs n² + 4(r+s) n`. -/
private theorem intDegree_pairQOddColor_sum (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (n : ℕ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        qParam ^ ((r : ℤ) * k * ((s : ℤ) * k + 1)) * quantumInt (2 * (s : ℤ) * k + 1) ≠ 0 ∧
      (∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        qParam ^ ((r : ℤ) * k * ((s : ℤ) * k + 1)) *
          quantumInt (2 * (s : ℤ) * k + 1)).intDegree =
        4 * (r : ℤ) * s * (n : ℤ) ^ 2 + 4 * ((r : ℤ) + s) * n := by
  have hr0 : (1 : ℤ) ≤ r := by exact_mod_cast hr
  have hs0 : (1 : ℤ) ≤ s := by exact_mod_cast hs
  have hrs : (0 : ℤ) ≤ r * s := by nlinarith
  refine intDegree_sum_eq_of_lt (a := (n : ℤ)) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    ⟨(intDegree_pairQOddColor_term r s n).1, ?_⟩ fun k hk hkn ↦ Or.inr ?_
  · rw [(intDegree_pairQOddColor_term r s n).2, mul_assoc 2 (s : ℤ) n,
      max_eq_left (by nlinarith)]
    ring
  · rw [(intDegree_pairQOddColor_term r s k).2]
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    rw [mul_assoc 2 (s : ℤ) k]
    have hk3 : k < n := lt_of_le_of_ne hk2 hkn
    have h1 : 0 ≤ (r : ℤ) * s * (((n : ℤ) - k) * ((n : ℤ) + k)) :=
      mul_nonneg hrs (mul_nonneg (by omega) (by omega))
    rcases le_or_gt 0 k with h0 | h0
    · have h2 : 0 ≤ (s : ℤ) * k := by nlinarith
      rw [max_eq_left (by omega)]
      nlinarith
    · have h2 : (s : ℤ) * k < 0 := by nlinarith
      have h3 : 0 ≤ (s : ℤ) * ((n : ℤ) + k) := mul_nonneg (by omega) (by omega)
      have h4 : 0 ≤ (r : ℤ) * ((n : ℤ) - k) := mul_nonneg (by omega) (by omega)
      rw [max_eq_right (by omega)]
      nlinarith

theorem pairQ_intDegree_oddColor (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (n : ℕ) :
    pairQOddColor r s n ≠ 0 ∧
      (pairQOddColor r s n).intDegree = 4 * ((r : ℤ) + s - r * s) * n := by
  have h := intDegree_mul_eq
    ⟨zpow_ne_zero (-((r : ℤ) * s * n * ((n : ℤ) + 1))) qParam_ne_zero,
      intDegree_qParam_zpow _⟩ (intDegree_pairQOddColor_sum r s hr hs n)
  refine ⟨h.1, h.2.trans ?_⟩
  ring

end AJConjecture
