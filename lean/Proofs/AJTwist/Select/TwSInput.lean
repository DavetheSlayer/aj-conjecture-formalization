import Mathlib
import AJTwist.TwDefs
import AJHandoff.TorusQuantum.PairQTOrderOddColor
import AJHandoff.TorusQuantum.PairQOddColorDegree

/-!
# The twisted companion input and the Gaussian period inputs

Source: eq. (commoninput) of `transfer.tex` and Section 6.3 of `selection.tex` (revision 5).
With `q = t⁴`, `m = r s` and `a = twIndex η r s ℓ = ± m - ℓ`:

* `twsTorusSum η r s n` is the centred torus sum `V_n(q^{±1})`,
  `V_n(q) = ∑_{k=-n}^{n} q^(r k (s k + 1)) [2 s k + 1]` (`η = true`: `V_n(q)`; `η = false`:
  `V_n(q⁻¹)`, the mirror companion);
* `twsInput η r s ℓ n = q^(-a n(n+1)) V_n(q^{±1})` is the input `v_n` of the finite transform:
  the odd colour `2n + 1` of the zero-framed companion `T(r, ± s)` times the twist eigenvalue
  `q^(ℓ n(n+1))`. For `η = true`, `ℓ = 0` it is the library's `pairQOddColor r s`;
* `twsPeriodInput ℓ c n = q^(ℓ n(n+1)) (q^(c n) - q^(-c(n+1)))` is the half-interval input
  `w_n^{(ℓ,c)} = q^(ℓ n(n+1)) (Q^c - \hat Q^c)` of the Gaussian period `G_c^{(ℓ)}`.

The reduced satellite sequence is `pairQReducedFormula (twsInput η r s ℓ)` and the Gaussian period
is `pairQReducedFormula (twsPeriodInput ℓ c)` (the library's triangular finite transform,
eq. (universalbailey)).

Orders: `V_n(q)` has order `0` at `t = 0` and `V_n(q⁻¹)` has degree `0` (the term `k = 0`
dominates: for `k = p > 0` the least exponent is `p (m p + r - s) > 0`, for `k = -p < 0` it is
`(r p - 1)(s p - 1) > 0`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The centred torus sum `V_n(q)` (`η = true`) or `V_n(q⁻¹)` (`η = false`), where
`V_n(q) = ∑_{k=-n}^{n} q^(r k (s k + 1)) [2 s k + 1]`. -/
def twsTorusSum (η : Bool) (r s n : ℕ) : RatFunc ℚ :=
  ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
    qParam ^ ((if η then 1 else -1) * ((r : ℤ) * k * ((s : ℤ) * k + 1))) *
      quantumInt (2 * (s : ℤ) * k + 1)

/-- The twisted companion input `v_n = q^(-a n(n+1)) V_n(q^{±1})`, `a = twIndex η r s ℓ`. -/
def twsInput (η : Bool) (r s : ℕ) (ℓ : ℤ) (n : ℕ) : RatFunc ℚ :=
  qParam ^ (-(twIndex η r s ℓ * n * ((n : ℤ) + 1))) * twsTorusSum η r s n

/-- The input `w_n^{(ℓ,c)} = q^(ℓ n(n+1)) (q^(c n) - q^(-c(n+1)))` of the Gaussian period
`G_c^{(ℓ)}`. -/
def twsPeriodInput (ℓ c : ℤ) (n : ℕ) : RatFunc ℚ :=
  qParam ^ (ℓ * n * ((n : ℤ) + 1)) * (qParam ^ (c * n) - qParam ^ (-(c * ((n : ℤ) + 1))))

/-- `V_n(q)` as a sum without the chirality sign. -/
private theorem twsTorusSum_true_eq_twsInput (r s n : ℕ) :
    twsTorusSum true r s n = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
      qParam ^ ((r : ℤ) * k * ((s : ℤ) * k + 1)) * quantumInt (2 * (s : ℤ) * k + 1) := by
  simp only [twsTorusSum, ↓reduceIte, one_mul]

/-- `V_n(q⁻¹)` as a sum without the chirality sign. -/
private theorem twsTorusSum_false_eq_twsInput (r s n : ℕ) :
    twsTorusSum false r s n = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
      qParam ^ (-((r : ℤ) * k * ((s : ℤ) * k + 1))) * quantumInt (2 * (s : ℤ) * k + 1) := by
  simp only [twsTorusSum, Bool.false_eq_true, ↓reduceIte, neg_one_mul]

/-- For the right-handed companion without twist the input is the library's odd colours of
`T(r, s)`. -/
theorem twsInput_true_zero (r s : ℕ) : twsInput true r s 0 = pairQOddColor r s := by
  funext n
  simp only [twsInput, twsTorusSum_true_eq_twsInput, pairQOddColor, twIndex, ↓reduceIte, sub_zero,
    Nat.cast_mul]

/-- `V_n(q)` is nonzero of order `0` at `t = 0`. -/
theorem tws_tOrder_torusSum_true (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (n : ℕ) :
    twsTorusSum true r s n ≠ 0 ∧ pairQTOrder (twsTorusSum true r s n) = 0 := by
  have h := pairQTOrder_mul_eq (pairQTOrder_qParam_zpow_eq ((r : ℤ) * s * n * ((n : ℤ) + 1)))
    (pairQ_tOrder_oddColor r s hr hs n)
  have heq : qParam ^ ((r : ℤ) * s * n * ((n : ℤ) + 1)) * pairQOddColor r s n =
      twsTorusSum true r s n := by
    rw [twsTorusSum_true_eq_twsInput, pairQOddColor, ← mul_assoc, ← zpow_add₀ qParam_ne_zero,
      add_neg_cancel, zpow_zero, one_mul]
  rw [heq] at h
  refine ⟨h.1, h.2.trans ?_⟩
  ring

/-- An integer power of `t` is nonzero of degree its exponent. -/
private theorem intDegree_ratFuncX_zpow_twsInput (n : ℤ) :
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
private theorem intDegree_ratFuncX_zpow_sub_zpow_twsInput {a b : ℤ} (hab : a ≠ b) :
    (RatFunc.X : RatFunc ℚ) ^ a - RatFunc.X ^ b ≠ 0 ∧
      ((RatFunc.X : RatFunc ℚ) ^ a - RatFunc.X ^ b).intDegree = max a b := by
  have hlt : ∀ c d : ℤ, d < c → (RatFunc.X : RatFunc ℚ) ^ c - RatFunc.X ^ d ≠ 0 ∧
      ((RatFunc.X : RatFunc ℚ) ^ c - RatFunc.X ^ d).intDegree = c := by
    intro c d hdc
    rw [sub_eq_add_neg]
    refine intDegree_add_eq_of_lt (intDegree_ratFuncX_zpow_twsInput c) (Or.inr ?_)
    rwa [RatFunc.intDegree_neg, (intDegree_ratFuncX_zpow_twsInput d).2]
  rcases lt_or_gt_of_ne hab with h | h
  · have h1 := hlt b a h
    rw [max_eq_right h.le, ← neg_sub, RatFunc.intDegree_neg]
    exact ⟨neg_ne_zero.mpr h1.1, h1.2⟩
  · rw [max_eq_left h.le]
    exact hlt a b h

/-- The quantum integer `[m]`, `m ≠ 0`, is nonzero of degree `2|m| - 2` in `t`. -/
private theorem intDegree_quantumInt_twsInput {m : ℤ} (hm : m ≠ 0) :
    quantumInt m ≠ 0 ∧ (quantumInt m).intDegree = max (2 * m) (-(2 * m)) - 2 := by
  have h1 := intDegree_ratFuncX_zpow_sub_zpow_twsInput (a := 2 * m) (b := -(2 * m)) (by omega)
  have h2 := intDegree_ratFuncX_zpow_sub_zpow_twsInput (a := 2) (b := -2) (by omega)
  exact intDegree_div_eq h1 h2

/-- The term of index `k` of `V_n(q⁻¹)` is nonzero of degree `-4rk(sk+1) + 2|2sk+1| - 2`. -/
private theorem intDegree_twsTorusSum_false_term (r s : ℕ) (k : ℤ) :
    qParam ^ (-((r : ℤ) * k * ((s : ℤ) * k + 1))) * quantumInt (2 * (s : ℤ) * k + 1) ≠ 0 ∧
      (qParam ^ (-((r : ℤ) * k * ((s : ℤ) * k + 1))) *
        quantumInt (2 * (s : ℤ) * k + 1)).intDegree =
        4 * (-((r : ℤ) * k * ((s : ℤ) * k + 1))) +
          (max (2 * (2 * (s : ℤ) * k + 1)) (-(2 * (2 * (s : ℤ) * k + 1))) - 2) := by
  have hne : 2 * (s : ℤ) * k + 1 ≠ 0 := by
    rw [mul_assoc]
    omega
  exact intDegree_mul_eq ⟨zpow_ne_zero _ qParam_ne_zero, intDegree_qParam_zpow _⟩
    (intDegree_quantumInt_twsInput hne)

/-- `V_n(q⁻¹)` is nonzero of degree `0`. -/
theorem tws_intDegree_torusSum_false (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (n : ℕ) :
    twsTorusSum false r s n ≠ 0 ∧ (twsTorusSum false r s n).intDegree = 0 := by
  have hr0 : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have hs0 : (2 : ℤ) ≤ s := by exact_mod_cast hs
  rw [twsTorusSum_false_eq_twsInput]
  refine intDegree_sum_eq_of_lt (a := (0 : ℤ)) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    ⟨(intDegree_twsTorusSum_false_term r s 0).1, ?_⟩ fun k _ hk0 ↦ Or.inr ?_
  · rw [(intDegree_twsTorusSum_false_term r s 0).2]
    simp
  · rw [(intDegree_twsTorusSum_false_term r s k).2, mul_assoc 2 (s : ℤ) k]
    rcases lt_or_gt_of_ne hk0 with h0 | h0
    · have h1 : (s : ℤ) * k < 0 := by nlinarith
      have h2 : (1 : ℤ) ≤ -((r : ℤ) * k) - 1 := by nlinarith
      have h3 : (1 : ℤ) ≤ -((s : ℤ) * k) - 1 := by nlinarith
      have h4 := one_le_mul_of_one_le_of_one_le h2 h3
      rw [max_eq_right (by omega)]
      nlinarith
    · have h1 : 0 < (s : ℤ) * k := by nlinarith
      have h2 : (2 : ℤ) * k ≤ r * k := by nlinarith
      rw [max_eq_left (by omega)]
      nlinarith

/-- The input of the right-handed companion is nonzero of order `-4 a n(n+1)` at `t = 0`. -/
theorem tws_tOrder_input_true (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (ℓ : ℤ) (n : ℕ) :
    twsInput true r s ℓ n ≠ 0 ∧
      pairQTOrder (twsInput true r s ℓ n) = -4 * twIndex true r s ℓ * n * ((n : ℤ) + 1) := by
  have h := pairQTOrder_mul_eq
    (pairQTOrder_qParam_zpow_eq (-(twIndex true r s ℓ * n * ((n : ℤ) + 1))))
    (tws_tOrder_torusSum_true r s hr hs n)
  refine ⟨h.1, h.2.trans ?_⟩
  ring

/-- The input of the mirror companion is nonzero of degree `-4 a n(n+1)`. -/
theorem tws_intDegree_input_false (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (ℓ : ℤ) (n : ℕ) :
    twsInput false r s ℓ n ≠ 0 ∧
      (twsInput false r s ℓ n).intDegree = -4 * twIndex false r s ℓ * n * ((n : ℤ) + 1) := by
  have h := intDegree_mul_eq
    ⟨zpow_ne_zero (-(twIndex false r s ℓ * n * ((n : ℤ) + 1))) qParam_ne_zero,
      intDegree_qParam_zpow _⟩ (tws_intDegree_torusSum_false r s hr hs n)
  refine ⟨h.1, h.2.trans ?_⟩
  ring

end AJConjecture
