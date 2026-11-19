import Mathlib
import AJConjecture.QAlgQParamBasic
import AJFamily.Quantum.TorusOddColorRec
import AJHandoff.TorusQuantum.PairQFormula

/-!
# The first-order recurrence of the odd colours of `T(r, s)`

With `u = pairQOddColor r s`, `m = rs`, extended to `ℤ` by `u_(-n-1) = -u_n` (`pairQOddExt`):
`u_(n+1) = q^(-2m(n+1)) u_n + h_(r,s)(n)` at every integer `n` (source Q2/Q3), and `u_0 = 1`.

Route (as `torusOddColorInt_succ`). For `n ≥ 0` the difference `u_(n+1) - q^(-2m(n+1)) u_n`
consists of the two terms `k = ±(n+1)` of the sum defining `u_(n+1)`, which are
`q^((r-m)(n+1)) [2s(n+1)+1]` and `-q^(-(r+m)(n+1)) [2s(n+1)-1]`; written with powers of `t`
these are the four monomials of `pairQForcing`. At `n = -1` the claim is `h(-1) = 2`. For
`n = -p-2`, `p ≥ 0`, it follows from the case `p` and the reflection
`h(-p-2) = q^(2m(p+1)) h(p)`, checked on the four monomials (the exponents `4(r-s-m)` and
`4(s-r-m)` exchange).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `u_0 = 1`. -/
theorem pairQOddColor_zero (r s : ℕ) : pairQOddColor r s 0 = 1 := by
  simp only [pairQOddColor, quantumInt, Nat.cast_zero, neg_zero, Finset.Icc_self,
    Finset.sum_singleton, mul_zero, zero_add, zpow_zero, one_mul, mul_one]
  exact div_self ratFuncX_sq_sub_inv_sq_ne_zero

/-- The odd extension is odd under `n ↦ -n - 1`. -/
theorem pairQOddExt_neg_sub_one (u : ℕ → RatFunc ℚ) (n : ℤ) :
    pairQOddExt u (-n - 1) = -pairQOddExt u n := by
  rcases le_or_gt 0 n with hn | hn
  · rw [pairQOddExt, pairQOddExt, ite_eq_right (by omega), ite_eq_left hn,
      show -(-n - 1) - 1 = n by ring]
  · rw [pairQOddExt, pairQOddExt, ite_eq_left (by omega), ite_eq_right (by omega), neg_neg]

/-- The two new terms `k = ±(n+1)` of the theta sum of `T(r, s)`, normalised, are the forcing
term. -/
private theorem pairQForcing_eq_theta_end_terms (r s : ℕ) (n : ℤ) :
    qParam ^ (-((r : ℤ) * s * (n + 1) * (n + 1 + 1))) *
        (qParam ^ ((r : ℤ) * (n + 1) * ((s : ℤ) * (n + 1) + 1)) *
            quantumInt (2 * (s : ℤ) * (n + 1) + 1) +
          qParam ^ ((r : ℤ) * (-(n + 1)) * ((s : ℤ) * (-(n + 1)) + 1)) *
            quantumInt (2 * (s : ℤ) * (-(n + 1)) + 1)) =
      pairQForcing r s n := by
  have hq := qParam_ne_zero
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have e1 : qParam ^ (-((r : ℤ) * s * (n + 1) * (n + 1 + 1))) *
      qParam ^ ((r : ℤ) * (n + 1) * ((s : ℤ) * (n + 1) + 1)) =
      RatFunc.X ^ (4 * ((r : ℤ) - r * s) * (n + 1)) := by
    rw [← zpow_add₀ hq, qParam_zpow_eq_ratFuncX_zpow]
    congr 1
    ring
  have e2 : qParam ^ (-((r : ℤ) * s * (n + 1) * (n + 1 + 1))) *
      qParam ^ ((r : ℤ) * (-(n + 1)) * ((s : ℤ) * (-(n + 1)) + 1)) =
      RatFunc.X ^ (-4 * ((r : ℤ) + r * s) * (n + 1)) := by
    rw [← zpow_add₀ hq, qParam_zpow_eq_ratFuncX_zpow]
    congr 1
    ring
  have t1 : (RatFunc.X : RatFunc ℚ) ^ (4 * ((r : ℤ) - r * s) * (n + 1)) *
      RatFunc.X ^ (2 * (2 * (s : ℤ) * (n + 1) + 1)) =
      RatFunc.X ^ (4 * ((r : ℤ) + s - r * s) * (n + 1) + 2) := by
    rw [← zpow_add₀ hX]; congr 1; ring
  have t2 : (RatFunc.X : RatFunc ℚ) ^ (4 * ((r : ℤ) - r * s) * (n + 1)) *
      RatFunc.X ^ (-(2 * (2 * (s : ℤ) * (n + 1) + 1))) =
      RatFunc.X ^ (4 * ((r : ℤ) - s - r * s) * (n + 1) - 2) := by
    rw [← zpow_add₀ hX]; congr 1; ring
  have t3 : (RatFunc.X : RatFunc ℚ) ^ (-4 * ((r : ℤ) + r * s) * (n + 1)) *
      RatFunc.X ^ (2 * (2 * (s : ℤ) * -(n + 1) + 1)) =
      RatFunc.X ^ (-4 * ((r : ℤ) + s + r * s) * (n + 1) + 2) := by
    rw [← zpow_add₀ hX]; congr 1; ring
  have t4 : (RatFunc.X : RatFunc ℚ) ^ (-4 * ((r : ℤ) + r * s) * (n + 1)) *
      RatFunc.X ^ (-(2 * (2 * (s : ℤ) * -(n + 1) + 1))) =
      RatFunc.X ^ (4 * ((s : ℤ) - r - r * s) * (n + 1) - 2) := by
    rw [← zpow_add₀ hX]; congr 1; ring
  rw [mul_add, ← mul_assoc, ← mul_assoc, e1, e2, pairQForcing, quantumInt, quantumInt,
    mul_div_assoc', mul_div_assoc', ← add_div]
  congr 1
  linear_combination t1 - t2 + t3 - t4

/-- The first-order recurrence of the odd colours of `T(r, s)` at natural indices. -/
private theorem pairQOddColor_succ_eq_add_forcing (r s : ℕ) (n : ℕ) :
    pairQOddColor r s (n + 1) =
      qParam ^ (-(2 * ((r : ℤ) * s) * ((n : ℤ) + 1))) * pairQOddColor r s n +
        pairQForcing r s n := by
  have hq := qParam_ne_zero
  have hIcc : Finset.Icc (-(((n + 1 : ℕ) : ℤ))) ((n + 1 : ℕ) : ℤ) =
      insert ((n : ℤ) + 1) (insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) n)) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
    omega
  have h1 : (n : ℤ) + 1 ∉ insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) n) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have h2 : -((n : ℤ) + 1) ∉ Finset.Icc (-(n : ℤ)) n := by
    simp only [Finset.mem_Icc]
    omega
  have hpow : qParam ^ (-((r : ℤ) * s * ((n : ℤ) + 1) * ((n : ℤ) + 1 + 1))) =
      qParam ^ (-(2 * ((r : ℤ) * s) * ((n : ℤ) + 1))) *
        qParam ^ (-((r : ℤ) * s * (n : ℤ) * ((n : ℤ) + 1))) := by
    rw [← zpow_add₀ hq]
    congr 1
    ring
  rw [← pairQForcing_eq_theta_end_terms, pairQOddColor, pairQOddColor, hIcc,
    Finset.sum_insert h1, Finset.sum_insert h2, Nat.cast_add, Nat.cast_one, hpow]
  ring

/-- The reflection `h(-p-2) = q^(2m(p+1)) h(p)` of the forcing term. -/
private theorem pairQForcing_neg_sub_two (r s : ℕ) (p : ℤ) :
    pairQForcing r s (-p - 2) = qParam ^ (2 * ((r : ℤ) * s) * (p + 1)) * pairQForcing r s p := by
  have k : ∀ b c : ℤ, 4 * (2 * ((r : ℤ) * s) * (p + 1)) + b = c →
      qParam ^ (2 * ((r : ℤ) * s) * (p + 1)) * (RatFunc.X : RatFunc ℚ) ^ b = RatFunc.X ^ c := by
    intro b c h
    rw [qParam_zpow_eq_ratFuncX_zpow, ← zpow_add₀ RatFunc.X_ne_zero, h]
  have kA := k (4 * ((r : ℤ) + s - r * s) * (p + 1) + 2)
    (-4 * ((r : ℤ) + s + r * s) * (-p - 2 + 1) + 2) (by ring)
  have kB := k (4 * ((r : ℤ) - s - r * s) * (p + 1) - 2)
    (4 * ((s : ℤ) - r - r * s) * (-p - 2 + 1) - 2) (by ring)
  have kC := k (4 * ((s : ℤ) - r - r * s) * (p + 1) - 2)
    (4 * ((r : ℤ) - s - r * s) * (-p - 2 + 1) - 2) (by ring)
  have kD := k (-4 * ((r : ℤ) + s + r * s) * (p + 1) + 2)
    (4 * ((r : ℤ) + s - r * s) * (-p - 2 + 1) + 2) (by ring)
  rw [pairQForcing, pairQForcing, mul_div_assoc']
  congr 1
  linear_combination -kD + kC + kB - kA

/-- The forcing term at `n = -1` is `2`. -/
private theorem pairQForcing_neg_one (r s : ℕ) : pairQForcing r s (-1) = 2 := by
  have hD := ratFuncX_sq_sub_inv_sq_ne_zero
  rw [pairQForcing, div_eq_iff hD,
    show 4 * ((r : ℤ) + s - r * s) * (-1 + 1) + 2 = 2 by ring,
    show 4 * ((r : ℤ) - s - r * s) * (-1 + 1) - 2 = -2 by ring,
    show 4 * ((s : ℤ) - r - r * s) * (-1 + 1) - 2 = -2 by ring,
    show -4 * ((r : ℤ) + s + r * s) * (-1 + 1) + 2 = 2 by ring]
  ring

/-- The recurrence Q2/Q3 of the odd colours of `T(r, s)` at every integer. -/
theorem pairQOddColor_rec (r s : ℕ) (n : ℤ) :
    pairQOddExt (pairQOddColor r s) (n + 1) =
      qParam ^ (-(2 * ((r : ℤ) * s) * (n + 1))) * pairQOddExt (pairQOddColor r s) n +
        pairQForcing r s n := by
  have hq := qParam_ne_zero
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [pairQOddExt, pairQOddExt, ite_eq_left hn,
      ite_eq_left (by omega : (0 : ℤ) ≤ (p : ℤ) + 1), Int.toNat_natCast,
      show ((p : ℤ) + 1).toNat = p + 1 by omega]
    exact pairQOddColor_succ_eq_add_forcing r s p
  · rcases eq_or_lt_of_le (Int.lt_iff_add_one_le.mp hn) with h1 | h1
    · obtain rfl : n = -1 := by omega
      rw [pairQOddExt, pairQOddExt, ite_eq_left (by omega : (0 : ℤ) ≤ -1 + 1),
        ite_eq_right (by omega : ¬(0 : ℤ) ≤ -1), pairQForcing_neg_one]
      norm_num [pairQOddColor_zero]
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) - 2 := ⟨(-n - 2).toNat, by omega⟩
      rw [pairQOddExt, pairQOddExt,
        ite_eq_right (by omega : ¬(0 : ℤ) ≤ -(p : ℤ) - 2 + 1),
        ite_eq_right (by omega : ¬(0 : ℤ) ≤ -(p : ℤ) - 2),
        show (-(-(p : ℤ) - 2 + 1) - 1).toNat = p by omega,
        show (-(-(p : ℤ) - 2) - 1).toNat = p + 1 by omega,
        pairQOddColor_succ_eq_add_forcing, pairQForcing_neg_sub_two,
        show -(2 * ((r : ℤ) * s) * (-(p : ℤ) - 2 + 1)) = 2 * ((r : ℤ) * s) * ((p : ℤ) + 1) by
          ring, zpow_neg]
      field_simp
      ring

end AJConjecture
