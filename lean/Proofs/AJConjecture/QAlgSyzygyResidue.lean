import Mathlib
import AJConjecture.QAlgNodeContentSplit
import AJConjecture.QAlgFibreSyzygy
import AJConjecture.QAlgInnerDerivativeBasic

/-!
# The residue of the solution of a Bézout-type equation at a simple crossing (Theorem C)

Let `R, S, Y, U, N ∈ k[M][L]` with `S Y + R U = μ^m N`, `μ = M - m₀`, `deg_L Y < deg R̄`, where
a bar denotes the fibre `M = m₀`. Assume that `l₀` is a common root of `R̄` and `S̄`, that
`R̄ = (L - l₀) R^c` with `R^c` coprime to `S̄` (so `l₀` is a simple root of `R̄` and the only
common root), and that the Jacobian
`J = ∂_L R ∂_M S - ∂_L S ∂_M R` at `(m₀, l₀)` is not zero. Then `Y(0) / μ^m` has at most a simple
pole at `m₀`: `μ Y(0) = μ^m y`, and `y(m₀) l₀ J = -N̄(l₀) R̄(0)`.

Proof by induction on `m`. For `m = 0`, `y = μ Y(0)` and `N̄(l₀) = 0` by evaluating the
equation at `(m₀, l₀)`. For `m ≥ 1` the fibre of the equation is `S̄ Ȳ + R̄ Ū = 0`, so
`Ȳ = α R^c` (`exists_eq_C_mul_of_dvd_mul`) and then `Ū = -α S̄/(L - l₀)`.
If `α = 0` both `Y` and `U` are divisible by `μ`; divide and use the induction hypothesis.
If `α ≠ 0`, apply `innerDerivative` to the equation and evaluate at `(m₀, l₀)`
(`innerDerivative_mul`; `R̄(l₀) = S̄(l₀) = 0`, `R^c(l₀) = R̄'(l₀)`,
`(S̄/(L - l₀))(l₀) = S̄'(l₀)`): `α J = N̄(l₀)` if `m = 1` and `α J = 0` if `m ≥ 2`. Hence
`m = 1`, `y = Y(0)`, `y(m₀) = α R^c(0)` and `R̄(0) = -l₀ R^c(0)`.
-/

open Polynomial

namespace AJConjecture

/-- The derivative in `M` of the equation `S Y + R U = μ^(m+1) N`, at a common zero of the
fibres of `R` and `S`. -/
private theorem eval_fibre_innerDerivative_syzRes {k : Type*} [Field k] {m₀ l₀ : k}
    {R S Y U N : k[X][X]} (m : ℕ)
    (heq : S * Y + R * U = C ((X - C m₀) ^ (m + 1)) * N)
    (hR0 : (R.map (Polynomial.evalRingHom m₀)).eval l₀ = 0)
    (hS0 : (S.map (Polynomial.evalRingHom m₀)).eval l₀ = 0) :
    ((innerDerivative S).map (Polynomial.evalRingHom m₀)).eval l₀ *
          (Y.map (Polynomial.evalRingHom m₀)).eval l₀ +
        ((innerDerivative R).map (Polynomial.evalRingHom m₀)).eval l₀ *
          (U.map (Polynomial.evalRingHom m₀)).eval l₀ =
      ((m + 1 : ℕ) : k) * 0 ^ m * (N.map (Polynomial.evalRingHom m₀)).eval l₀ := by
  have h := congrArg (fun p ↦ ((innerDerivative p).map (Polynomial.evalRingHom m₀)).eval l₀) heq
  simp only [innerDerivative_add, innerDerivative_mul, innerDerivative_C, Polynomial.map_add,
    Polynomial.map_mul, eval_add, eval_mul, hR0, hS0, Polynomial.map_C, eval_C,
    derivative_X_sub_C_pow, coe_evalRingHom, eval_pow, eval_sub, eval_X, sub_self,
    Nat.add_sub_cancel] at h
  rw [zero_pow (Nat.succ_ne_zero m)] at h
  linear_combination h

/-- The case of the residue formula in which the fibre of `Y` does not vanish: the pole is
simple and the residue is given by the Jacobian. -/
private theorem residue_of_fibre_ne_zero_syzRes {k : Type*} [Field k] {m₀ l₀ α : k}
    {R S Y U N : k[X][X]} {Rc : k[X]} (m : ℕ)
    (heq : S * Y + R * U = C ((X - C m₀) ^ (m + 1)) * N)
    (hR : R.map (Polynomial.evalRingHom m₀) = (X - C l₀) * Rc)
    (hS : (S.map (Polynomial.evalRingHom m₀)).eval l₀ = 0)
    (hα : Y.map (Polynomial.evalRingHom m₀) = C α * Rc) (hα0 : α ≠ 0)
    (hU : S.map (Polynomial.evalRingHom m₀) * C α +
      (X - C l₀) * U.map (Polynomial.evalRingHom m₀) = 0)
    (hJ : (derivative (R.map (Polynomial.evalRingHom m₀))).eval l₀ *
          ((innerDerivative S).map (Polynomial.evalRingHom m₀)).eval l₀ -
        (derivative (S.map (Polynomial.evalRingHom m₀))).eval l₀ *
          ((innerDerivative R).map (Polynomial.evalRingHom m₀)).eval l₀ ≠ 0) :
    m = 0 ∧ (Y.coeff 0).eval m₀ * (l₀ *
          ((derivative (R.map (Polynomial.evalRingHom m₀))).eval l₀ *
              ((innerDerivative S).map (Polynomial.evalRingHom m₀)).eval l₀ -
            (derivative (S.map (Polynomial.evalRingHom m₀))).eval l₀ *
              ((innerDerivative R).map (Polynomial.evalRingHom m₀)).eval l₀)) =
        -((N.map (Polynomial.evalRingHom m₀)).eval l₀ *
          (R.map (Polynomial.evalRingHom m₀)).coeff 0) := by
  have hR0 : (R.map (Polynomial.evalRingHom m₀)).eval l₀ = 0 := by
    rw [hR, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
  have hder := eval_fibre_innerDerivative_syzRes m heq hR0 hS
  have hRc_eval : (derivative (R.map (Polynomial.evalRingHom m₀))).eval l₀ = Rc.eval l₀ := by
    rw [hR]
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, eval_add, eval_mul,
      eval_sub, eval_X, eval_C, sub_self, zero_mul, sub_zero, one_mul, add_zero]
  have hY_eval : (Y.map (Polynomial.evalRingHom m₀)).eval l₀ =
      α * (derivative (R.map (Polynomial.evalRingHom m₀))).eval l₀ := by
    rw [hα, hRc_eval, eval_mul, eval_C]
  have hU_eval : (U.map (Polynomial.evalRingHom m₀)).eval l₀ =
      -(α * (derivative (S.map (Polynomial.evalRingHom m₀))).eval l₀) := by
    have h := congrArg (fun p ↦ (derivative p).eval l₀) hU
    simp only [derivative_add, derivative_mul, derivative_C, derivative_sub, derivative_X,
      eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, mul_zero, add_zero,
      sub_zero, one_mul, derivative_zero, eval_zero] at h
    linear_combination h
  rw [hY_eval, hU_eval] at hder
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨rfl, ?_⟩
    have hy : (Y.coeff 0).eval m₀ = α * Rc.coeff 0 := by
      have h := congrArg (fun p ↦ p.coeff 0) hα
      simpa only [coeff_map, coe_evalRingHom, coeff_C_mul] using h
    have hRcoeff : (R.map (Polynomial.evalRingHom m₀)).coeff 0 = -(l₀ * Rc.coeff 0) := by
      rw [hR, mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero]
      ring
    rw [hy, hRcoeff]
    rw [pow_zero] at hder
    linear_combination (l₀ * Rc.coeff 0 : k) * hder
  · exfalso
    apply hJ
    rw [zero_pow hm.ne'] at hder
    have h0 : α * ((derivative (R.map (Polynomial.evalRingHom m₀))).eval l₀ *
          ((innerDerivative S).map (Polynomial.evalRingHom m₀)).eval l₀ -
        (derivative (S.map (Polynomial.evalRingHom m₀))).eval l₀ *
          ((innerDerivative R).map (Polynomial.evalRingHom m₀)).eval l₀) = 0 := by
      linear_combination hder
    exact (mul_eq_zero.mp h0).resolve_left hα0

/-- The residue formula for the equation `S Y + R U = μ^m N` at a simple transversal crossing
of `R` and `S`. -/
theorem exists_mul_eq_pow_mul_of_syzygy {k : Type*} [Field k] {m₀ l₀ : k}
    {R S Y U N : k[X][X]} {Rc : k[X]} (m : ℕ)
    (heq : S * Y + R * U = C ((X - C m₀) ^ m) * N)
    (hY : Y.natDegree < (R.map (Polynomial.evalRingHom m₀)).natDegree)
    (hR : R.map (Polynomial.evalRingHom m₀) = (X - C l₀) * Rc)
    (hS : (S.map (Polynomial.evalRingHom m₀)).eval l₀ = 0)
    (hcop : IsCoprime Rc (S.map (Polynomial.evalRingHom m₀)))
    (hJ : (derivative (R.map (Polynomial.evalRingHom m₀))).eval l₀ *
          ((innerDerivative S).map (Polynomial.evalRingHom m₀)).eval l₀ -
        (derivative (S.map (Polynomial.evalRingHom m₀))).eval l₀ *
          ((innerDerivative R).map (Polynomial.evalRingHom m₀)).eval l₀ ≠ 0) :
    ∃ y : k[X], (X - C m₀) * Y.coeff 0 = (X - C m₀) ^ m * y ∧
      y.eval m₀ * (l₀ *
          ((derivative (R.map (Polynomial.evalRingHom m₀))).eval l₀ *
              ((innerDerivative S).map (Polynomial.evalRingHom m₀)).eval l₀ -
            (derivative (S.map (Polynomial.evalRingHom m₀))).eval l₀ *
              ((innerDerivative R).map (Polynomial.evalRingHom m₀)).eval l₀)) =
        -((N.map (Polynomial.evalRingHom m₀)).eval l₀ *
          (R.map (Polynomial.evalRingHom m₀)).coeff 0) := by
  have hR0 : (R.map (Polynomial.evalRingHom m₀)).eval l₀ = 0 := by
    rw [hR, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
  induction m generalizing Y U N with
  | zero =>
    refine ⟨(X - C m₀) * Y.coeff 0, by rw [pow_zero, one_mul], ?_⟩
    have h := congrArg (fun p ↦ (p.map (Polynomial.evalRingHom m₀)).eval l₀) heq
    simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hR0, hS, pow_zero,
      C_1, one_mul, zero_mul, add_zero] at h
    rw [← h, eval_mul, eval_sub, eval_X, eval_C, sub_self]
    ring
  | succ m ih =>
    have hfib : S.map (Polynomial.evalRingHom m₀) * Y.map (Polynomial.evalRingHom m₀) +
        R.map (Polynomial.evalRingHom m₀) * U.map (Polynomial.evalRingHom m₀) = 0 := by
      have h := congrArg (Polynomial.map (Polynomial.evalRingHom m₀)) heq
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
        Polynomial.map_C, coe_evalRingHom, eval_pow, eval_sub, eval_X, eval_C, sub_self,
        zero_pow (Nat.succ_ne_zero m), C_0, zero_mul] at h
      exact h
    have hYdeg : (Y.map (Polynomial.evalRingHom m₀)).natDegree <
        (R.map (Polynomial.evalRingHom m₀)).natDegree := lt_of_le_of_lt natDegree_map_le hY
    have hdvd : R.map (Polynomial.evalRingHom m₀) ∣
        S.map (Polynomial.evalRingHom m₀) * Y.map (Polynomial.evalRingHom m₀) :=
      ⟨-U.map (Polynomial.evalRingHom m₀), by linear_combination hfib⟩
    obtain ⟨α, hα⟩ := exists_eq_C_mul_of_dvd_mul hR hcop hYdeg hdvd
    have hRc : Rc ≠ 0 := by
      rintro rfl
      rw [hR, mul_zero, natDegree_zero] at hY
      exact absurd hY (Nat.not_lt_zero _)
    have hU : S.map (Polynomial.evalRingHom m₀) * C α +
        (X - C l₀) * U.map (Polynomial.evalRingHom m₀) = 0 := by
      have h : Rc * (S.map (Polynomial.evalRingHom m₀) * C α +
          (X - C l₀) * U.map (Polynomial.evalRingHom m₀)) = 0 := by
        rw [← hfib, hα, hR]
        ring
      exact (mul_eq_zero.mp h).resolve_left hRc
    rcases eq_or_ne α 0 with hα0 | hα0
    · have hYbar : Y.map (Polynomial.evalRingHom m₀) = 0 := by rw [hα, hα0, C_0, zero_mul]
      have hUbar : U.map (Polynomial.evalRingHom m₀) = 0 := by
        rw [hα0, C_0, mul_zero, zero_add] at hU
        exact (mul_eq_zero.mp hU).resolve_left (X_sub_C_ne_zero l₀)
      obtain ⟨Y', rfl⟩ := exists_eq_C_mul_of hYbar
      obtain ⟨U', rfl⟩ := exists_eq_C_mul_of hUbar
      have hμ : (C (X - C m₀) : k[X][X]) ≠ 0 := C_ne_zero.mpr (X_sub_C_ne_zero m₀)
      have heq' : S * Y' + R * U' = C ((X - C m₀) ^ m) * N := by
        apply mul_left_cancel₀ hμ
        rw [pow_succ, C_mul] at heq
        linear_combination heq
      have hY' : Y'.natDegree < (R.map (Polynomial.evalRingHom m₀)).natDegree := by
        rwa [natDegree_C_mul (X_sub_C_ne_zero m₀)] at hY
      obtain ⟨y, hy1, hy2⟩ := ih heq' hY'
      refine ⟨y, ?_, hy2⟩
      rw [coeff_C_mul, pow_succ]
      linear_combination (X - C m₀) * hy1
    · obtain ⟨rfl, hres⟩ := residue_of_fibre_ne_zero_syzRes m heq hR hS hα hα0 hU hJ
      exact ⟨Y.coeff 0, by rw [zero_add, pow_one], hres⟩

end AJConjecture
