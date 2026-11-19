import Mathlib
import AJConjecture.APolynomial
import AJHandoff.LocalTheory.LocSymJetEquation

/-!
# The value of the right-hand side `N*` at the node

At a common root `(z₀, l₀)` of `R*` and `S*` (so `P₀(z₀, l₀) = 0` since `β*(z₀) ≠ 0`), the value
of `N* = β*² 𝒩(P) - c s* (u ∂_u S*)(r* z ∂_z R* - z r*' R*)` is
`s* r* (β* P₁ - c l₀ z₀ ∂_u S* ∂_z R*)` at `(z₀, l₀)`, using `β* p = s* r*` for the leading
coefficients. Port of the library's `eval_nodeRemainder_of_content`; it is stated with the first
jet `P₁` directly (the source's formula (4)) rather than through a Weyl symbol.
-/

open Polynomial

noncomputable section

namespace AJConjecture

set_option linter.unusedVariables false in
theorem eval_locNodeRemainder (c : ℂ) {P : LocOp} {z₀ l₀ : ℂ} {βs ss rs : ℂ[X]}
    {Ss Rs : ℂ[X][X]} (hβs : βs.eval z₀ ≠ 0) (hfac : C βs * opJet0 P = Ss * Rs)
    (hlc : βs * (opJet0 P).coeff P.natDegree = ss * rs)
    (hR : (Rs.map (Polynomial.evalRingHom z₀)).eval l₀ = 0)
    (hS : (Ss.map (Polynomial.evalRingHom z₀)).eval l₀ = 0) :
    ((C (βs ^ 2) * locJetNumer P -
          C (C c * ss) * (X * derivative Ss) *
            (C rs * (C X * innerDerivative Rs) - C (X * derivative rs) * Rs)).map
        (Polynomial.evalRingHom z₀)).eval l₀ =
      ss.eval z₀ * rs.eval z₀ *
        (βs.eval z₀ * evalPoint (opJet1 P) (z₀, l₀) -
          c * l₀ * z₀ * (derivative (Ss.map (Polynomial.evalRingHom z₀))).eval l₀ *
            ((innerDerivative Rs).map (Polynomial.evalRingHom z₀)).eval l₀) := by
  have hP0 : ((opJet0 P).map (Polynomial.evalRingHom z₀)).eval l₀ = 0 := by
    have h1 := congrArg (fun q ↦ (q.map (Polynomial.evalRingHom z₀)).eval l₀) hfac
    simp only [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, coe_evalRingHom, hR,
      mul_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left hβs
  have hP1 : evalPoint (opJet1 P) (z₀, l₀) =
      ((opJet1 P).map (Polynomial.evalRingHom z₀)).eval l₀ := by
    rw [evalPoint, eval_map]
  have hlcm := congrArg (eval z₀) hlc
  rw [eval_mul, eval_mul] at hlcm
  rw [hP1]
  simp only [locJetNumer, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_C, Polynomial.map_X, eval_mul, eval_sub, eval_C, eval_X,
    coe_evalRingHom, eval_pow, hR, hP0, derivative_map, mul_zero, sub_zero]
  linear_combination (βs.eval z₀ * ((opJet1 P).map (Polynomial.evalRingHom z₀)).eval l₀) * hlcm

end AJConjecture
