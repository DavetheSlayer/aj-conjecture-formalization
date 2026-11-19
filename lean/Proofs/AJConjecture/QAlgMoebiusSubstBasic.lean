import Mathlib
import AJConjecture.QAlgMoebiusSubstMul

/-!
# The stationary substitution: constants, the variable, padding, powers

Consequences of additivity and multiplicativity of `moebiusSubst`: the substitution of `1` in
degree `d` is the padding factor `(x + L)^d`, the substitution of `J` is `x L + 1`, raising the
degree bound by `e` multiplies by `(x + L)^e`, and powers go to powers.
-/

open Polynomial

namespace AJConjecture

/-- The stationary substitution of `1` with degree bound `d` is `(x + L)^d`. -/
theorem moebiusSubst_one (d : ℕ) : moebiusSubst d 1 = (C X + X) ^ d := by
  unfold moebiusSubst
  rw [Finset.sum_eq_single 0]
  · rw [coeff_one, ite_eq_left rfl, C_1, pow_zero, one_mul, one_mul, Nat.sub_zero]
  · intro k _ hk
    rw [coeff_one, ite_eq_right hk, C_0, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos d)) h

/-- The stationary substitution of `J` with degree bound `d + 1` is `(x L + 1)(x + L)^d`. -/
theorem moebiusSubst_X (d : ℕ) : moebiusSubst (d + 1) X = (C X * X + 1) * (C X + X) ^ d := by
  unfold moebiusSubst
  rw [Finset.sum_eq_single 1]
  · rw [coeff_X_one, C_1, pow_one, one_mul, Nat.add_sub_cancel]
  · intro k _ hk
    rw [coeff_X, ite_eq_right hk.symm, C_0, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The stationary substitution is compatible with subtraction. -/
theorem moebiusSubst_sub (d : ℕ) (p p' : ℤ[X][X]) :
    moebiusSubst d (p - p') = moebiusSubst d p - moebiusSubst d p' := by
  simp only [moebiusSubst, coeff_sub, C_sub, sub_mul, Finset.sum_sub_distrib]

/-- Raising the degree bound by `e` multiplies the stationary substitution by `(x + L)^e`. -/
theorem moebiusSubst_add_degree {d : ℕ} (e : ℕ) {p : ℤ[X][X]} (hp : p.natDegree ≤ d) :
    moebiusSubst (d + e) p = moebiusSubst d p * (C X + X) ^ e := by
  have h1 : (1 : ℤ[X][X]).natDegree ≤ e := natDegree_one.le.trans (Nat.zero_le e)
  have h := moebiusSubst_mul hp h1
  rwa [mul_one, moebiusSubst_one] at h

end AJConjecture
