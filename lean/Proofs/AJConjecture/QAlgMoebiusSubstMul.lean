import Mathlib
import AJConjecture.QAlgSymbolPoly

/-!
# The stationary substitution is additive and multiplicative

`moebiusSubst d` is additive and linear over `ℤ[x]`, and
`moebiusSubst (d₁ + d₂) (p p') = moebiusSubst d₁ p · moebiusSubst d₂ p'` when `p`, `p'` have
degrees at most `d₁`, `d₂` in `J`.
-/

open Polynomial

namespace AJConjecture

/-- The stationary substitution is additive. -/
theorem moebiusSubst_add (d : ℕ) (p p' : ℤ[X][X]) :
    moebiusSubst d (p + p') = moebiusSubst d p + moebiusSubst d p' := by
  simp only [moebiusSubst, coeff_add, C_add, add_mul, Finset.sum_add_distrib]

/-- The stationary substitution is linear over the polynomials in `x`. -/
theorem moebiusSubst_C_mul (d : ℕ) (c : ℤ[X]) (p : ℤ[X][X]) :
    moebiusSubst d (C c * p) = C c * moebiusSubst d p := by
  simp only [moebiusSubst, coeff_C_mul, C_mul, Finset.mul_sum, mul_assoc]

/-- The stationary substitution commutes with finite sums. -/
theorem moebiusSubst_finsetSum {ι : Type*} (d : ℕ) (s : Finset ι) (f : ι → ℤ[X][X]) :
    moebiusSubst d (∑ i ∈ s, f i) = ∑ i ∈ s, moebiusSubst d (f i) :=
  map_sum (AddMonoidHom.mk' (moebiusSubst d) (moebiusSubst_add d)) f s

/-- The stationary substitution of a monomial of degree at most `d`. -/
private theorem moebiusSubst_C_mul_X_pow_of_le {d i : ℕ} (hi : i ≤ d) (c : ℤ[X]) :
    moebiusSubst d (C c * X ^ i) = C c * (C X * X + 1) ^ i * (C X + X) ^ (d - i) := by
  unfold moebiusSubst
  rw [Finset.sum_eq_single i]
  · rw [coeff_C_mul, coeff_X_pow_self, mul_one]
  · intro k _ hk
    rw [coeff_C_mul, coeff_X_pow, ite_eq_right hk, mul_zero, C_0, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)) h

/-- A polynomial of degree at most `d` is the sum of its first `d + 1` monomials. -/
private theorem eq_sum_range_C_mul_X_pow_of_natDegree_le {p : ℤ[X][X]} {d : ℕ}
    (hp : p.natDegree ≤ d) : p = ∑ i ∈ Finset.range (d + 1), C (p.coeff i) * X ^ i := by
  conv_lhs => rw [p.as_sum_range' (d + 1) (Nat.lt_succ_of_le hp)]
  exact Finset.sum_congr rfl fun i _ ↦ (C_mul_X_pow_eq_monomial).symm

/-- The stationary substitution is multiplicative on polynomials of bounded degree. -/
theorem moebiusSubst_mul {d₁ d₂ : ℕ} {p p' : ℤ[X][X]} (hp : p.natDegree ≤ d₁)
    (hp' : p'.natDegree ≤ d₂) :
    moebiusSubst (d₁ + d₂) (p * p') = moebiusSubst d₁ p * moebiusSubst d₂ p' := by
  have hmul : p * p' = ∑ i ∈ Finset.range (d₁ + 1), ∑ j ∈ Finset.range (d₂ + 1),
      C (p.coeff i * p'.coeff j) * X ^ (i + j) := by
    conv_lhs => rw [eq_sum_range_C_mul_X_pow_of_natDegree_le hp,
      eq_sum_range_C_mul_X_pow_of_natDegree_le hp', Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [C_mul, pow_add]
    ring
  rw [hmul, moebiusSubst_finsetSum]
  simp only [moebiusSubst_finsetSum]
  conv_rhs => rw [moebiusSubst, moebiusSubst, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
  have hi' : i ≤ d₁ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hj' : j ≤ d₂ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [moebiusSubst_C_mul_X_pow_of_le (Nat.add_le_add hi' hj'),
    show d₁ + d₂ - (i + j) = (d₁ - i) + (d₂ - j) by omega, C_mul, pow_add, pow_add]
  ring

end AJConjecture
