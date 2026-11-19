import Mathlib
import AJFamily.Skein.TorusReducedFormulaTwo
import AJConjecture.QAlgQParamBasic
import AJFamily.Quantum.TorusOddColorInt

/-!
# First-order recurrence of the odd colours

The extended odd colours satisfy `u_(n+1) = q^(-4a(n+1)) u_n + h_a(q^n)` for every integer `n`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The denominator `t² - t⁻²` of the quantum integers is not zero. -/
theorem ratFuncX_sq_sub_inv_sq_ne_zero :
    (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ) ≠ 0 := by
  intro h
  have h2 : (2 : ℤ) = -2 := ratFuncX_zpow_injective (sub_eq_zero.mp h)
  omega

/-- A product of two powers of `t` is the power with the summed exponent. -/
private theorem ratFuncX_zpow_mul_zpow_eq_torus {b c d : ℤ} (h : b + c = d) :
    (RatFunc.X : RatFunc ℚ) ^ b * RatFunc.X ^ c = RatFunc.X ^ d := by
  rw [← zpow_add₀ RatFunc.X_ne_zero, h]

/-- The two new terms `s = ±(n+1)` of the theta sum of `T(2, a)`, normalised, are the forcing
term. -/
private theorem torusForcing_eq_theta_end_terms (a : ℕ) (n : ℤ) :
    qParam ^ (-(2 * (a : ℤ) * (n + 1) * (n + 1 + 1))) *
        (qParam ^ ((a : ℤ) * (n + 1) * (2 * (n + 1) + 1)) * quantumInt (4 * (n + 1) + 1) +
          qParam ^ ((a : ℤ) * (-(n + 1)) * (2 * (-(n + 1)) + 1)) *
            quantumInt (4 * (-(n + 1)) + 1)) =
      torusForcing a n := by
  have hq := qParam_ne_zero
  have e1 : qParam ^ (-(2 * (a : ℤ) * (n + 1) * (n + 1 + 1))) *
      qParam ^ ((a : ℤ) * (n + 1) * (2 * (n + 1) + 1)) =
      RatFunc.X ^ (-(4 * (a : ℤ) * (n + 1))) := by
    rw [← zpow_add₀ hq, qParam_zpow_eq_ratFuncX_zpow]
    congr 1
    ring
  have e2 : qParam ^ (-(2 * (a : ℤ) * (n + 1) * (n + 1 + 1))) *
      qParam ^ ((a : ℤ) * (-(n + 1)) * (2 * (-(n + 1)) + 1)) =
      RatFunc.X ^ (-(12 * (a : ℤ) * (n + 1))) := by
    rw [← zpow_add₀ hq, qParam_zpow_eq_ratFuncX_zpow]
    congr 1
    ring
  have t1 : (RatFunc.X : RatFunc ℚ) ^ (-(4 * (a : ℤ) * (n + 1))) *
      RatFunc.X ^ (2 * (4 * (n + 1) + 1)) = RatFunc.X ^ ((8 - 4 * (a : ℤ)) * n + 10 - 4 * a) :=
    ratFuncX_zpow_mul_zpow_eq_torus (by ring)
  have t2 : (RatFunc.X : RatFunc ℚ) ^ (-(4 * (a : ℤ) * (n + 1))) *
      RatFunc.X ^ (-(2 * (4 * (n + 1) + 1))) =
      RatFunc.X ^ (-(4 * (a : ℤ) + 8) * n - 4 * a - 10) :=
    ratFuncX_zpow_mul_zpow_eq_torus (by ring)
  have t3 : (RatFunc.X : RatFunc ℚ) ^ (-(12 * (a : ℤ) * (n + 1))) *
      RatFunc.X ^ (2 * (4 * -(n + 1) + 1)) =
      RatFunc.X ^ (-(12 * (a : ℤ) + 8) * n - 12 * a - 6) :=
    ratFuncX_zpow_mul_zpow_eq_torus (by ring)
  have t4 : (RatFunc.X : RatFunc ℚ) ^ (-(12 * (a : ℤ) * (n + 1))) *
      RatFunc.X ^ (-(2 * (4 * -(n + 1) + 1))) =
      RatFunc.X ^ ((8 - 12 * (a : ℤ)) * n + 6 - 12 * a) :=
    ratFuncX_zpow_mul_zpow_eq_torus (by ring)
  rw [mul_add, ← mul_assoc, ← mul_assoc, e1, e2, torusForcing, quantumInt, quantumInt,
    mul_div_assoc', mul_div_assoc', ← add_div, mul_sub, mul_sub, t1, t2, t3, t4]
  congr 1
  ring

/-- The first-order recurrence of the odd colours of `T(2, a)` at natural indices. -/
private theorem torusOddColor_succ_eq_add_forcing (a : ℕ) (n : ℕ) :
    torusOddColor a (n + 1) =
      qParam ^ (-(4 * (a : ℤ) * ((n : ℤ) + 1))) * torusOddColor a n + torusForcing a n := by
  have hq := qParam_ne_zero
  have hIcc : Finset.Icc (-(((n + 1 : ℕ) : ℤ))) ((n + 1 : ℕ) : ℤ) =
      insert ((n : ℤ) + 1) (insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) n)) := by
    ext s
    simp only [Finset.mem_insert, Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
    omega
  have h1 : (n : ℤ) + 1 ∉ insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) n) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have h2 : -((n : ℤ) + 1) ∉ Finset.Icc (-(n : ℤ)) n := by
    simp only [Finset.mem_Icc]
    omega
  have hpow : qParam ^ (-(2 * (a : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 1 + 1))) =
      qParam ^ (-(4 * (a : ℤ) * ((n : ℤ) + 1))) *
        qParam ^ (-(2 * (a : ℤ) * (n : ℤ) * ((n : ℤ) + 1))) := by
    rw [← zpow_add₀ hq]
    congr 1
    ring
  rw [← torusForcing_eq_theta_end_terms, torusOddColor, torusOddColor, hIcc,
    Finset.sum_insert h1, Finset.sum_insert h2, Nat.cast_add, Nat.cast_one, hpow]
  ring

/-- The reflection `h_a(1/(q² Q)) = q^(4a) Q^(4a) h_a(Q)` of the forcing term. -/
private theorem torusForcing_neg_sub_two (a : ℕ) (m : ℤ) :
    torusForcing a (-m - 2) = qParam ^ (4 * (a : ℤ) * (m + 1)) * torusForcing a m := by
  have k : ∀ b c : ℤ, 4 * (4 * (a : ℤ) * (m + 1)) + b = c →
      qParam ^ (4 * (a : ℤ) * (m + 1)) * (RatFunc.X : RatFunc ℚ) ^ b = RatFunc.X ^ c := by
    intro b c h
    rw [qParam_zpow_eq_ratFuncX_zpow, ← zpow_add₀ RatFunc.X_ne_zero, h]
  have kE := k (-(12 * (a : ℤ) + 8) * m - 12 * a - 6) ((8 - 4 * (a : ℤ)) * (-m - 2) + 10 - 4 * a)
    (by ring)
  have kC := k ((8 - 12 * (a : ℤ)) * m + 6 - 12 * a) (-(4 * (a : ℤ) + 8) * (-m - 2) - 4 * a - 10)
    (by ring)
  have kB := k (-(4 * (a : ℤ) + 8) * m - 4 * a - 10) ((8 - 12 * (a : ℤ)) * (-m - 2) + 6 - 12 * a)
    (by ring)
  have kA := k ((8 - 4 * (a : ℤ)) * m + 10 - 4 * a) (-(12 * (a : ℤ) + 8) * (-m - 2) - 12 * a - 6)
    (by ring)
  rw [torusForcing, torusForcing, mul_div_assoc']
  congr 1
  linear_combination -kE + kC + kB - kA

/-- The forcing term at `n = -1` is `2`. -/
private theorem torusForcing_neg_one (a : ℕ) : torusForcing a (-1) = 2 := by
  have hD := ratFuncX_sq_sub_inv_sq_ne_zero
  rw [torusForcing, div_eq_iff hD,
    show (8 - 4 * (a : ℤ)) * -1 + 10 - 4 * a = 2 by ring,
    show -(4 * (a : ℤ) + 8) * -1 - 4 * a - 10 = -2 by ring,
    show (8 - 12 * (a : ℤ)) * -1 + 6 - 12 * a = -2 by ring,
    show -(12 * (a : ℤ) + 8) * -1 - 12 * a - 6 = 2 by ring]
  ring

/-- The first-order inhomogeneous recurrence of the odd colours of `T(2, a)`, at every
integer. -/
theorem torusOddColorInt_succ (a : ℕ) (n : ℤ) :
    torusOddColorInt a (n + 1) =
      qParam ^ (-(4 * (a : ℤ) * (n + 1))) * torusOddColorInt a n + torusForcing a n := by
  have hq := qParam_ne_zero
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [torusOddColorInt, torusOddColorInt, ite_eq_left hn,
      ite_eq_left (by omega : (0 : ℤ) ≤ (m : ℤ) + 1), Int.toNat_natCast,
      show ((m : ℤ) + 1).toNat = m + 1 by omega]
    exact torusOddColor_succ_eq_add_forcing a m
  · rcases eq_or_lt_of_le (Int.lt_iff_add_one_le.mp hn) with h1 | h1
    · obtain rfl : n = -1 := by omega
      rw [torusOddColorInt, torusOddColorInt, ite_eq_left (by omega : (0 : ℤ) ≤ -1 + 1),
        ite_eq_right (by omega : ¬(0 : ℤ) ≤ -1), torusForcing_neg_one]
      norm_num [torusOddColor_zero_eq_one]
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 2 := ⟨(-n - 2).toNat, by omega⟩
      rw [torusOddColorInt, torusOddColorInt,
        ite_eq_right (by omega : ¬(0 : ℤ) ≤ -(k : ℤ) - 2 + 1),
        ite_eq_right (by omega : ¬(0 : ℤ) ≤ -(k : ℤ) - 2),
        show (-(-(k : ℤ) - 2 + 1) - 1).toNat = k by omega,
        show (-(-(k : ℤ) - 2) - 1).toNat = k + 1 by omega,
        torusOddColor_succ_eq_add_forcing, torusForcing_neg_sub_two,
        show -(4 * (a : ℤ) * (-(k : ℤ) - 2 + 1)) = 4 * (a : ℤ) * ((k : ℤ) + 1) by ring, zpow_neg]
      field_simp
      ring

end AJConjecture
