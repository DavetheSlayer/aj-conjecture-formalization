import Mathlib
import AJTwist.Quantum.TwQWindowPoly

/-!
# The cleared adjoint raises the degree in `x` by exactly two

This is the new argument of the existence proof (it has no counterpart in the manuscript, which
only needs the nonvanishing of the explicit operators `P_a`): the operator built from an
arbitrary inner relation is nonzero because the adjoint `𝒜_d` of `𝒵` raises the degree in the
colour variable `x = q^N` by exactly one, i.e. the cleared adjoint `twAdjoint d q = q^d x 𝒜_d`
raises it by exactly two, with an explicit leading coefficient.

The degree in `x` (the inner variable) is the degree of the swapped polynomial
(`Polynomial.Bivariate.swap`: `swap (C X) = X`, `swap X = C X`); `(swap n).coeff e` is the
coefficient of `x^e`, a polynomial in `J`.

* `twH_X_mul_twAdjoint` (proved): the definition of `twAdjoint` without `divX`
  (`divX p * X + C (p.coeff 0) = p`, and the constant term in `J` of the bracket vanishes):
  `J · twAdjoint d q n = q^d x J² n + q^(d-1) x n - (1 - qJ)(x - qJ)(q^(d-1) - xJ) n(qJ)`.
* `twH_swap_comp_scale` (proved): the substitution `J ↦ qJ` after the swap acts on the
  coefficients.
* `twH_natDegree_swap_twAdjoint_le`, `twH_coeff_swap_twAdjoint`: if `deg_x n ≤ e` then
  `deg_x (twAdjoint d q n) ≤ e + 2` and
  `[x^(e+2)] twAdjoint d q n = (1 - qJ) · ([x^e] n)(qJ)`.
  Apply `swap` to `twH_X_mul_twAdjoint`: the first two terms have degree `≤ e + 1` in `x`; in
  the third, `(x - qJ)(q^(d-1) - xJ) = -J x² + (q^(d-1) + qJ²) x - q^d J`, so the coefficient of
  `x^(e+2)` on the right is `(1 - qJ) J ([x^e] n)(qJ)`; cancel the factor `J` (`X` is a
  non-zero-divisor of `R[X]`, no hypothesis on `R`).

Checked on random numerators for the windows `d = 0, …, 6` in exact rationals and
`d = 7, 12, 19` in a prime field (scratch `H/h02_sbp.py`, items (c), (d); `H/h05_xdeg0.py`).
-/

open Polynomial Polynomial.Bivariate

noncomputable section

namespace AJConjecture

/-- The cleared adjoint without `divX`. -/
theorem twH_X_mul_twAdjoint {R : Type*} [CommRing R] (d : ℕ) (q : R) (n : R[X][X]) :
    X * twAdjoint d q n =
      C (C (q ^ d) * X) * X ^ 2 * n + C (C (q ^ (d - 1)) * X) * n -
        (1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ (d - 1))) - C X * X) *
          n.comp (C (C q) * X) := by
  have h0 : (C (C (q ^ (d - 1)) * X) * n -
      (1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ (d - 1))) - C X * X) *
        n.comp (C (C q) * X)).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp only [eval_sub, eval_mul, eval_C, eval_X, eval_comp, eval_one, mul_zero, sub_zero,
      one_mul]
    ring
  have h := divX_mul_X_add (C (C (q ^ (d - 1)) * X) * n -
      (1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ (d - 1))) - C X * X) *
        n.comp (C (C q) * X))
  rw [h0, C_0, add_zero] at h
  rw [twAdjoint, mul_add, mul_comm X (divX _), h]
  ring

/-- After the swap, the substitution `J ↦ qJ` acts on the coefficients. -/
theorem twH_swap_comp_scale {R : Type*} [CommRing R] (q : R) (n : R[X][X]) :
    swap (n.comp (C (C q) * X)) = (swap n).map (Polynomial.compRingHom (C q * X)) := by
  induction n using Polynomial.induction_on' with
  | add p r hp hr => rw [add_comp, map_add, map_add, Polynomial.map_add, hp, hr]
  | monomial k a =>
    have h1 : ∀ a : R[X], (a.map C).map (Polynomial.compRingHom (C q * X)) = a.map C := by
      intro a
      rw [Polynomial.map_map]
      congr 1
      ext r
      simp
    rw [← C_mul_X_pow_eq_monomial]
    simp only [mul_comp, C_comp, pow_comp, X_comp, map_mul, map_pow, swap_C, swap_Y,
      Polynomial.map_mul, Polynomial.map_pow, h1, Polynomial.map_C,
      Polynomial.coe_compRingHom_apply, X_comp]

/-- The swapped form of `twH_X_mul_twAdjoint`: the outer variable is now `x`. -/
private theorem swap_X_mul_twAdjoint_xDegree {R : Type*} [CommRing R] (d : ℕ) (q : R)
    (n : R[X][X]) :
    C X * swap (twAdjoint d q n) =
      (C (C (q ^ d) * X ^ 2) + C (C (q ^ (d - 1)))) * X * swap n -
        C (1 - C q * X) * (X - C (C q * X)) * (C (C (q ^ (d - 1))) - C X * X) *
          (swap n).map (Polynomial.compRingHom (C q * X)) := by
  have h := congrArg swap (twH_X_mul_twAdjoint d q n)
  simp only [map_mul, map_add, map_sub, map_pow, map_one, swap_Y, swap_X, swap_C_C,
    twH_swap_comp_scale] at h
  rw [h]
  simp only [C_mul, C_sub, C_pow, C_1]
  ring

/-- The linear factor in `x` of the first two terms. -/
private theorem natDegree_linear_xDegree {R : Type*} [CommRing R] (d : ℕ) (q : R) :
    ((C (C (q ^ d) * X ^ 2) + C (C (q ^ (d - 1)))) * X : R[X][X]).natDegree ≤ 1 := by
  rw [← C_add]
  exact (natDegree_C_mul_le _ _).trans natDegree_X_le

/-- The first linear factor in `x` of the third term. -/
private theorem natDegree_factorA_xDegree {R : Type*} [CommRing R] (q : R) :
    (C (1 - C q * X) * (X - C (C q * X)) : R[X][X]).natDegree ≤ 1 :=
  (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le _)

/-- The second linear factor in `x` of the third term. -/
private theorem natDegree_factorB_xDegree {R : Type*} [CommRing R] (d : ℕ) (q : R) :
    (C (C (q ^ (d - 1))) - C X * X : R[X][X]).natDegree ≤ 1 := by
  have h1 : (C (C (q ^ (d - 1))) : R[X][X]).natDegree ≤ 1 := by
    rw [natDegree_C]
    exact Nat.zero_le 1
  have h2 : (C X * X : R[X][X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
  exact (natDegree_sub_le_of_le h1 h2).trans (max_le le_rfl le_rfl)

/-- Multiplication by `J` does not change the degree in `x`. -/
private theorem natDegree_le_of_C_X_mul_xDegree {R : Type*} [CommRing R] (p : R[X][X]) {k : ℕ}
    (h : (C X * p).natDegree ≤ k) : p.natDegree ≤ k := by
  rw [natDegree_le_iff_coeff_eq_zero] at h ⊢
  intro N hN
  have h1 := h N hN
  rw [coeff_C_mul, ← mul_zero (X : R[X])] at h1
  exact isRegular_X.left h1

/-- The cleared adjoint raises the degree in `x` by at most two. -/
theorem twH_natDegree_swap_twAdjoint_le {R : Type*} [CommRing R] (d : ℕ) (q : R)
    (n : R[X][X]) {e : ℕ} (hn : (swap n).natDegree ≤ e) :
    (swap (twAdjoint d q n)).natDegree ≤ e + 2 := by
  refine natDegree_le_of_C_X_mul_xDegree _ ?_
  rw [swap_X_mul_twAdjoint_xDegree]
  have hm : ((swap n).map (Polynomial.compRingHom (C q * X))).natDegree ≤ e :=
    natDegree_map_le.trans hn
  refine (natDegree_sub_le_of_le
    (natDegree_mul_le_of_le (natDegree_linear_xDegree d q) hn)
    (natDegree_mul_le_of_le (natDegree_mul_le_of_le (natDegree_factorA_xDegree q)
      (natDegree_factorB_xDegree d q)) hm)).trans (max_le (by omega) (by omega))

/-- The coefficient of `x^(e+2)` of the cleared adjoint: `(1 - qJ) · ([x^e] n)(qJ)`. -/
theorem twH_coeff_swap_twAdjoint {R : Type*} [CommRing R] (d : ℕ) (q : R) (n : R[X][X])
    {e : ℕ} (hn : (swap n).natDegree ≤ e) :
    (swap (twAdjoint d q n)).coeff (e + 2) =
      (1 - C q * X) * ((swap n).coeff e).comp (C q * X) := by
  have hm : ((swap n).map (Polynomial.compRingHom (C q * X))).natDegree ≤ e :=
    natDegree_map_le.trans hn
  have h := congrArg (fun p : R[X][X] ↦ p.coeff (e + 2)) (swap_X_mul_twAdjoint_xDegree d q n)
  have h1 : ((C (C (q ^ d) * X ^ 2) + C (C (q ^ (d - 1)))) * X * swap n).coeff (e + 2) = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_mul_le_of_le (natDegree_linear_xDegree d q) hn) (by omega))
  have hA : (C (1 - C q * X) * (X - C (C q * X)) : R[X][X]).coeff 1 = 1 - C q * X := by
    rw [coeff_C_mul, coeff_sub, coeff_X_one, coeff_C_succ, sub_zero, mul_one]
  have hB : (C (C (q ^ (d - 1))) - C X * X : R[X][X]).coeff 1 = -X := by
    rw [coeff_sub, coeff_C_succ, coeff_C_mul, coeff_X_one, mul_one, zero_sub]
  have h2 : (C (1 - C q * X) * (X - C (C q * X)) * (C (C (q ^ (d - 1))) - C X * X) *
      (swap n).map (Polynomial.compRingHom (C q * X))).coeff (e + 2) =
        (1 - C q * X) * -X * ((swap n).coeff e).comp (C q * X) := by
    rw [show e + 2 = 1 + 1 + e by omega, coeff_mul_add_eq_of_natDegree_le
      (natDegree_mul_le_of_le (natDegree_factorA_xDegree q) (natDegree_factorB_xDegree d q)) hm,
      coeff_mul_add_eq_of_natDegree_le (natDegree_factorA_xDegree q)
        (natDegree_factorB_xDegree d q), hA, hB, coeff_map, Polynomial.coe_compRingHom_apply]
  simp only [coeff_sub, coeff_C_mul] at h
  rw [h1, h2] at h
  refine isRegular_X.left ?_
  beta_reduce
  rw [h]
  ring

end AJConjecture
