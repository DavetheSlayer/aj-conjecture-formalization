import Mathlib
import AJConjecture.QAlgCycloBilateralSumCheb
import AJConjecture.QAlgCycloChebLinear
import AJConjecture.QAlgCycloKernelMoments
import AJFamily.Quantum.TorusCycloBilateral
import AJFamily.Quantum.TorusCycloDefect
import AJFamily.Quantum.TorusCycloReindex

/-!
# Vanishing of the cyclotomic defect

The cyclotomic defect vanishes for `j ≥ a + 3`, by re-indexing the bilateral transform with
`φ = Q^(2a-1) + Q^(2a)`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The bilateral transform is additive. -/
private theorem cycloBilateralSum_add_torusDefect (f g : ℤ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum (fun n ↦ f n + g n) j = cycloBilateralSum f j + cycloBilateralSum g j := by
  simp only [cycloBilateralSum, mul_add, Finset.sum_add_distrib]

/-- The bilateral transform commutes with multiplication by a constant. -/
private theorem cycloBilateralSum_const_mul_torusDefect (c : RatFunc ℚ) (f : ℤ → RatFunc ℚ)
    (j : ℕ) :
    cycloBilateralSum (fun n ↦ c * f n) j = c * cycloBilateralSum f j := by
  simp only [cycloBilateralSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  ring

/-- Integer powers of `q = t⁴` as integer powers of `t`. -/
private theorem qParam_zpow_eq_X_zpow_torusDefect (z : ℤ) :
    qParam ^ z = RatFunc.X ^ (4 * z) := by
  rw [qParam, ← zpow_natCast, ← zpow_mul]
  norm_num

/-- The product of a monomial `Q^k` with the forcing term of `T(2, a)`, as a combination of
four monomials. -/
private theorem zpow_mul_torusForcing_eq_monomials (a : ℕ) (k n : ℤ) :
    qParam ^ (n * k) * torusForcing a n =
      RatFunc.X ^ (10 - 4 * (a : ℤ)) / (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) *
          qParam ^ (n * (k + 2 - a)) +
        (-(RatFunc.X ^ (-4 * (a : ℤ) - 10) / (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))) *
            qParam ^ (n * (k - a - 2)) +
          (-(RatFunc.X ^ (6 - 12 * (a : ℤ)) / (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))) *
              qParam ^ (n * (k + 2 - 3 * a)) +
            RatFunc.X ^ (-12 * (a : ℤ) - 6) / (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) *
              qParam ^ (n * (k - 3 * a - 2)))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have key : ∀ e c s : ℤ, 4 * (n * k) + e = c + 4 * (n * s) →
      RatFunc.X ^ (4 * (n * k)) * RatFunc.X ^ e =
        (RatFunc.X ^ c : RatFunc ℚ) * RatFunc.X ^ (4 * (n * s)) := by
    intro e c s h
    rw [← zpow_add₀ hX, ← zpow_add₀ hX, h]
  have h1 := key ((8 - 4 * (a : ℤ)) * n + 10 - 4 * a) (10 - 4 * (a : ℤ)) (k + 2 - a) (by ring)
  have h2 := key (-(4 * (a : ℤ) + 8) * n - 4 * a - 10) (-4 * (a : ℤ) - 10) (k - a - 2)
    (by ring)
  have h3 := key ((8 - 12 * (a : ℤ)) * n + 6 - 12 * a) (6 - 12 * (a : ℤ)) (k + 2 - 3 * a)
    (by ring)
  have h4 := key (-(12 * (a : ℤ) + 8) * n - 12 * a - 6) (-12 * (a : ℤ) - 6) (k - 3 * a - 2)
    (by ring)
  simp only [qParam_zpow_eq_X_zpow_torusDefect, torusForcing]
  linear_combination (h1 - h2 - h3 + h4) / (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))

/-- The bilateral transform of `Q^k h_a(Q)` vanishes when all four shifted exponents are at
most `j` in absolute value. -/
private theorem cycloBilateralSum_zpow_mul_torusForcing_eq_zero (a : ℕ) {j : ℕ} {k : ℤ}
    (h1 : |k + 2 - a| ≤ (j : ℤ)) (h2 : |k - a - 2| ≤ (j : ℤ))
    (h3 : |k + 2 - 3 * a| ≤ (j : ℤ)) (h4 : |k - 3 * a - 2| ≤ (j : ℤ)) :
    cycloBilateralSum (fun n ↦ qParam ^ (n * k) * torusForcing a n) j = 0 := by
  simp only [zpow_mul_torusForcing_eq_monomials]
  rw [cycloBilateralSum_add_torusDefect, cycloBilateralSum_add_torusDefect,
    cycloBilateralSum_add_torusDefect, cycloBilateralSum_const_mul_torusDefect,
    cycloBilateralSum_const_mul_torusDefect, cycloBilateralSum_const_mul_torusDefect,
    cycloBilateralSum_const_mul_torusDefect, cycloBilateralSum_zpow_eq_zero h1,
    cycloBilateralSum_zpow_eq_zero h2, cycloBilateralSum_zpow_eq_zero h3,
    cycloBilateralSum_zpow_eq_zero h4]
  simp only [mul_zero, add_zero]

/-- The bilateral transform of `Q^k h_a(Q)` vanishes for `2a - 1 ≤ k ≤ 2a + 1` and
`j ≥ a + 3`. -/
private theorem cycloBilateralSum_zpow_mul_torusForcing_eq_zero_of_window (a : ℕ) {j : ℕ}
    (hj : a + 3 ≤ j) {k : ℤ} (hlo : 2 * (a : ℤ) - 1 ≤ k) (hhi : k ≤ 2 * (a : ℤ) + 1) :
    cycloBilateralSum (fun n ↦ qParam ^ (n * k) * torusForcing a n) j = 0 := by
  have hj' : (a : ℤ) + 3 ≤ j := by exact_mod_cast hj
  refine cycloBilateralSum_zpow_mul_torusForcing_eq_zero a ?_ ?_ ?_ ?_ <;>
    rw [abs_le] <;> constructor <;> omega

/-- The forcing side of the re-indexing identity for `φ = Q^d + Q^(d+1)`, `d = 2a - 1`,
vanishes for `j ≥ a + 3`. -/
private theorem cycloBilateralSum_torusDefect_forcing_eq_zero (a d : ℕ)
    (hd : 2 * d + 2 = 4 * a) {j : ℕ} (hj : a + 3 ≤ j) :
    cycloBilateralSum (fun n ↦ (qParam ^ n - qParam ^ j) *
      (qParam ^ ((n + 1) * (d : ℤ)) + qParam ^ ((n + 1) * ((d + 1 : ℕ) : ℤ))) *
        torusForcing a n) j = 0 := by
  have hq := qParam_ne_zero
  have hd' : (d : ℤ) = 2 * a - 1 := by omega
  have hfun : (fun n : ℤ ↦ (qParam ^ n - qParam ^ j) *
      (qParam ^ ((n + 1) * (d : ℤ)) + qParam ^ ((n + 1) * ((d + 1 : ℕ) : ℤ))) *
        torusForcing a n) =
      fun n ↦ qParam ^ (d + 1) * (qParam ^ (n * ((d + 2 : ℕ) : ℤ)) * torusForcing a n) +
        ((qParam ^ d - qParam ^ j * qParam ^ (d + 1)) *
            (qParam ^ (n * ((d + 1 : ℕ) : ℤ)) * torusForcing a n) +
          -(qParam ^ j * qParam ^ d) * (qParam ^ (n * (d : ℤ)) * torusForcing a n)) := by
    funext n
    simp only [zpow_mul, zpow_add_one₀ hq, zpow_natCast]
    ring
  rw [hfun, cycloBilateralSum_add_torusDefect, cycloBilateralSum_add_torusDefect,
    cycloBilateralSum_const_mul_torusDefect, cycloBilateralSum_const_mul_torusDefect,
    cycloBilateralSum_const_mul_torusDefect,
    cycloBilateralSum_zpow_mul_torusForcing_eq_zero_of_window a hj (by push_cast; omega)
      (by push_cast; omega),
    cycloBilateralSum_zpow_mul_torusForcing_eq_zero_of_window a hj (by push_cast; omega)
      (by push_cast; omega),
    cycloBilateralSum_zpow_mul_torusForcing_eq_zero_of_window a hj (by omega) (by omega)]
  simp only [mul_zero, add_zero]

/-- The operator of the re-indexing identity applied to `φ = Q^d + Q^(d+1)`, `d = 2a - 1`, is
`s_d + (1 - qJ) s_(d+1) - qJ s_(d+2)` with `s_e = Q^e + q^(-e) Q^(-e)`. -/
private theorem torusCycloDefect_symbol_eq_reindex_symbol (a d : ℕ) (hd : 2 * d + 2 = 4 * a)
    (j : ℕ) (n : ℤ) :
    (1 - qParam * qParam ^ j * qParam ^ n) *
          (qParam ^ (n * (d : ℤ)) + qParam ^ (n * ((d + 1 : ℕ) : ℤ))) +
        qParam ^ (1 - 4 * (a : ℤ)) * (qParam ^ n - qParam ^ j) *
            qParam ^ (-(4 * (a : ℤ) * n)) *
          (qParam ^ ((n + 1) * (d : ℤ)) + qParam ^ ((n + 1) * ((d + 1 : ℕ) : ℤ))) =
      (qParam ^ (n * (d : ℤ)) + qParam ^ (-(d : ℤ)) * qParam ^ (-(n * (d : ℤ)))) +
        ((1 - qParam * qParam ^ j) * (qParam ^ (n * ((d + 1 : ℕ) : ℤ)) +
            qParam ^ (-((d + 1 : ℕ) : ℤ)) * qParam ^ (-(n * ((d + 1 : ℕ) : ℤ)))) +
          -(qParam * qParam ^ j) * (qParam ^ (n * ((d + 2 : ℕ) : ℤ)) +
            qParam ^ (-((d + 2 : ℕ) : ℤ)) * qParam ^ (-(n * ((d + 2 : ℕ) : ℤ))))) := by
  have hq := qParam_ne_zero
  have hQ : qParam ^ n ≠ 0 := zpow_ne_zero n hq
  have h4a : 4 * (a : ℤ) = ((2 * d + 2 : ℕ) : ℤ) := by exact_mod_cast hd.symm
  have h1 : qParam ^ (1 - 4 * (a : ℤ)) = (qParam ^ (2 * d + 1))⁻¹ := by
    rw [h4a, ← zpow_natCast, ← zpow_neg,
      show (1 : ℤ) - ((2 * d + 2 : ℕ) : ℤ) = -((2 * d + 1 : ℕ) : ℤ) by push_cast; ring]
  have h2 : qParam ^ (-(4 * (a : ℤ) * n)) = ((qParam ^ n) ^ (2 * d + 2))⁻¹ := by
    rw [h4a, ← zpow_natCast, ← zpow_mul, ← zpow_neg, mul_comm]
  rw [h1, h2]
  simp only [zpow_neg, zpow_mul, zpow_add_one₀ hq, zpow_natCast]
  field_simp
  ring

/-- The bilateral transform of the operator applied to `φ = Q^d + Q^(d+1)` against the odd
colours of `T(2, a)` is twice the defect combination. -/
private theorem cycloBilateralSum_torusReindex_symbol_eq (a d : ℕ) (hd : 2 * d + 2 = 4 * a)
    (j : ℕ) :
    cycloBilateralSum (fun n ↦ ((1 - qParam * qParam ^ j * qParam ^ n) *
          (qParam ^ (n * (d : ℤ)) + qParam ^ (n * ((d + 1 : ℕ) : ℤ))) +
        qParam ^ (1 - 4 * (a : ℤ)) * (qParam ^ n - qParam ^ j) *
            qParam ^ (-(4 * (a : ℤ) * n)) *
          (qParam ^ ((n + 1) * (d : ℤ)) + qParam ^ ((n + 1) * ((d + 1 : ℕ) : ℤ)))) *
        torusOddColorInt a n) j =
      2 * (cycloCheb d (torusCyclotomicCoeff a) j +
        (1 - qParam * qParam ^ j) * cycloCheb (d + 1) (torusCyclotomicCoeff a) j -
          qParam * qParam ^ j * cycloCheb (d + 2) (torusCyclotomicCoeff a) j) := by
  have hD : cycloBilateralSum (torusOddColorInt a) = fun i ↦ 2 * torusCyclotomicCoeff a i :=
    funext fun i ↦ (two_mul_torusCyclotomicCoeff a i).symm
  have hfun : (fun n : ℤ ↦ ((1 - qParam * qParam ^ j * qParam ^ n) *
          (qParam ^ (n * (d : ℤ)) + qParam ^ (n * ((d + 1 : ℕ) : ℤ))) +
        qParam ^ (1 - 4 * (a : ℤ)) * (qParam ^ n - qParam ^ j) *
            qParam ^ (-(4 * (a : ℤ) * n)) *
          (qParam ^ ((n + 1) * (d : ℤ)) + qParam ^ ((n + 1) * ((d + 1 : ℕ) : ℤ)))) *
        torusOddColorInt a n) =
      fun n ↦ (qParam ^ (n * (d : ℤ)) + qParam ^ (-(d : ℤ)) * qParam ^ (-(n * (d : ℤ)))) *
          torusOddColorInt a n +
        ((1 - qParam * qParam ^ j) * ((qParam ^ (n * ((d + 1 : ℕ) : ℤ)) +
            qParam ^ (-((d + 1 : ℕ) : ℤ)) * qParam ^ (-(n * ((d + 1 : ℕ) : ℤ)))) *
              torusOddColorInt a n) +
          -(qParam * qParam ^ j) * ((qParam ^ (n * ((d + 2 : ℕ) : ℤ)) +
            qParam ^ (-((d + 2 : ℕ) : ℤ)) * qParam ^ (-(n * ((d + 2 : ℕ) : ℤ)))) *
              torusOddColorInt a n)) := by
    funext n
    rw [torusCycloDefect_symbol_eq_reindex_symbol a d hd j n]
    ring
  rw [hfun, cycloBilateralSum_add_torusDefect, cycloBilateralSum_add_torusDefect,
    cycloBilateralSum_const_mul_torusDefect, cycloBilateralSum_const_mul_torusDefect]
  rw [cycloBilateralSum_cheb d, cycloBilateralSum_cheb (d + 1), cycloBilateralSum_cheb (d + 2),
    hD, cycloCheb_const_mul, cycloCheb_const_mul, cycloCheb_const_mul]
  ring

/-- The defect of the family's cyclotomic coefficients vanishes from `j = a + 3` on. -/
theorem torusCycloDefect_eq_zero (a : ℕ) (ha : 1 ≤ a) {j : ℕ} (hj : a + 3 ≤ j) :
    torusCycloDefect a j = 0 := by
  set d := 2 * a - 1 with hd_def
  have hd : 2 * d + 2 = 4 * a := by omega
  have h := cycloBilateralSum_reindex_torus a
    (fun n ↦ qParam ^ (n * (d : ℤ)) + qParam ^ (n * ((d + 1 : ℕ) : ℤ))) j
  beta_reduce at h
  rw [cycloBilateralSum_torusReindex_symbol_eq a d hd j,
    cycloBilateralSum_torusDefect_forcing_eq_zero a d hd hj, mul_zero] at h
  have h2a : 2 * a = d + 1 := by omega
  have h2a1 : 2 * a + 1 = d + 2 := by omega
  rw [torusCycloDefect, h2a1, h2a, Nat.add_sub_cancel]
  exact (mul_eq_zero.mp h).resolve_left two_ne_zero

end AJConjecture
