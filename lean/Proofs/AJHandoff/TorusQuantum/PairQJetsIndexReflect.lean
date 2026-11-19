import Mathlib
import AJConjecture.APolynomial
import AJHandoff.TorusQuantum.PairQJetsIndexEmbed

/-!
# T-JETS: values of reversed polynomials at `u = L⁻¹`

For `p ∈ ℂ[z][L]` of degree at most `N` its reflection `p̂(u) = u^N p(1/u)` satisfies, at
`u = l⁻¹` with `l ≠ 0`,
* `p̂ · l^N = p`, `(∂_z p̂) · l^N = ∂_z p`;
* `(∂_u p̂) · l^N = l (N p - l ∂_L p)` (from `u ∂_u p̂ = (N - L ∂_L) p`, reflected).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The coefficients of `L ∂_L p`. -/
theorem coeff_X_mul_derivative_pairQ {R : Type*} [CommSemiring R] (p : R[X]) (n : ℕ) :
    (X * derivative p).coeff n = n * p.coeff n := by
  rcases n with _ | n
  · simp
  · rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- `u ∂_u` of a reflection is the reflection of `N - L ∂_L`. -/
theorem X_mul_derivative_reflect_pairQ {R : Type*} [CommRing R] {p : R[X]} {N : ℕ}
    (hp : p.natDegree ≤ N) :
    X * derivative (reflect N p) = reflect N (C (N : R) * p - X * derivative p) := by
  ext i : 2
  rw [coeff_X_mul_derivative_pairQ, coeff_reflect, coeff_reflect, coeff_sub, coeff_C_mul,
    coeff_X_mul_derivative_pairQ]
  rcases le_or_gt i N with hi | hi
  · rw [revAt_le hi, Nat.cast_sub hi]
    ring
  · rw [revAt_eq_self_of_lt hi, coeff_eq_zero_of_natDegree_lt (hp.trans_lt hi)]
    ring

/-- `L ∂_L` does not raise the degree. -/
theorem natDegree_C_mul_sub_X_mul_derivative_le_pairQ {R : Type*} [CommRing R] {p : R[X]}
    {N : ℕ} (hp : p.natDegree ≤ N) :
    (C (N : R) * p - X * derivative p).natDegree ≤ N := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ ?_
  rw [coeff_sub, coeff_C_mul, coeff_X_mul_derivative_pairQ,
    coeff_eq_zero_of_natDegree_lt (hp.trans_lt hn)]
  ring

/-- The inner derivative commutes with reflection. -/
theorem innerDerivative_reflect_pairQ {A : Type*} [CommSemiring A] (p : A[X][X]) (N : ℕ) :
    innerDerivative (reflect N p) = reflect N (innerDerivative p) := by
  ext i : 2
  rw [coeff_innerDerivative_pairQ, coeff_reflect, coeff_reflect, coeff_innerDerivative_pairQ]

/-- The inner derivative does not raise the degree. -/
theorem natDegree_innerDerivative_le_pairQ {A : Type*} [CommSemiring A] (p : A[X][X]) :
    (innerDerivative p).natDegree ≤ p.natDegree := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ ?_
  rw [coeff_innerDerivative_pairQ, coeff_eq_zero_of_natDegree_lt hn, derivative_zero]

/-- The value of a reflection at `u = l⁻¹`. -/
theorem evalPoint_reflect_inv_pairQ {p : ℂ[X][X]} {N : ℕ} (hp : p.natDegree ≤ N) (z : ℂ)
    {l : ℂ} (hl : l ≠ 0) :
    evalPoint (reflect N p) (z, l⁻¹) * l ^ N = evalPoint p (z, l) := by
  let _ : Invertible l := invertibleOfNonzero hl
  have h := eval₂_reflect_mul_pow (Polynomial.evalRingHom z) l N p hp
  rwa [invOf_eq_inv] at h

/-- The `u`-derivative of a reflection at `u = l⁻¹`. -/
theorem evalPoint_derivative_reflect_inv_pairQ {p : ℂ[X][X]} {N : ℕ} (hp : p.natDegree ≤ N)
    (z : ℂ) {l : ℂ} (hl : l ≠ 0) :
    evalPoint (derivative (reflect N p)) (z, l⁻¹) * l ^ N =
      l * (N * evalPoint p (z, l) - l * evalPoint (derivative p) (z, l)) := by
  have h := evalPoint_reflect_inv_pairQ (natDegree_C_mul_sub_X_mul_derivative_le_pairQ hp) z hl
  rw [← X_mul_derivative_reflect_pairQ hp] at h
  simp only [evalPoint, eval₂_mul, eval₂_X, eval₂_sub, eval₂_C, coe_evalRingHom, eval_natCast]
    at h ⊢
  rw [← h]
  field_simp

/-- The `z`-derivative of a reflection at `u = l⁻¹`. -/
theorem evalPoint_innerDerivative_reflect_inv_pairQ {p : ℂ[X][X]} {N : ℕ}
    (hp : p.natDegree ≤ N) (z : ℂ) {l : ℂ} (hl : l ≠ 0) :
    evalPoint (innerDerivative (reflect N p)) (z, l⁻¹) * l ^ N =
      evalPoint (innerDerivative p) (z, l) := by
  rw [innerDerivative_reflect_pairQ]
  exact evalPoint_reflect_inv_pairQ ((natDegree_innerDerivative_le_pairQ p).trans hp) z hl

end AJConjecture
