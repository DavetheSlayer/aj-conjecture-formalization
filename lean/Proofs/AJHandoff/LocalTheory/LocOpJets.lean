import Mathlib
import AJConjecture.QAlgOreMul
import AJConjecture.QAlgInnerDerivative
import AJConjecture.QAlgInnerDerivativeBasic
import AJConjecture.QAlgOreMulBasic
import AJHandoff.LocalTheory.LocJets

/-!
# The residual symbol and the first jet of an operator

For `P = ∑ a_i u^i ∈ ℂ[[h]][z][u]` the residual symbol is `P₀ = ∑ (a_i)₀ u^i ∈ ℂ[z][u]` and the
first jet `P₁ = ∑ (a_i)₁ u^i`. In `ℂ[z][u]` the outer variable is `u` and the inner one `z`.
Since the shift is the identity modulo `h`, `(S ⋆ R)₀ = S₀ R₀`, and expanding the Ore product to
first order gives formula (6) of the source,
`(S ⋆ R)₁ = S₁ R₀ + S₀ R₁ + c (u ∂_u S₀)(z ∂_z R₀)`.

For a right factor `R` of degree `d` with constant and leading coefficients `r₀`, `r_d`, the
logarithmic first jet of `r₀/r_d` (the first logarithmic coefficient of the determinant
`(-1)^d r₀/r_d` of the companion matrix of `r_d⁻¹ R`) is `locLogJetNum R / locLogJetDen R`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The residual symbol `P₀ ∈ ℂ[z][u]` of an operator. -/
def opJet0 (P : LocOp) : ℂ[X][X] := P.map locJet0

/-- The first jet `P₁ ∈ ℂ[z][u]` of an operator. -/
def opJet1 (P : LocOp) : ℂ[X][X] := P.sum fun k a ↦ monomial k (locJet1 a)

/-- The coefficients of the first jet of an operator. -/
private theorem coeff_opJet1_aux (P : LocOp) (k : ℕ) :
    (opJet1 P).coeff k = locJet1 (P.coeff k) := by
  rw [opJet1, Polynomial.sum_def, Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
  · rw [coeff_monomial_same]
  · intro b _ hb
    rw [coeff_monomial_of_ne _ hb.symm]
  · intro h
    rw [Polynomial.notMem_support_iff.1 h, coeff_monomial_same]
    ext n
    rw [coeff_locJet1, coeff_zero, map_zero, coeff_zero]

private theorem opJet1_add_aux (P Q : LocOp) : opJet1 (P + Q) = opJet1 P + opJet1 Q := by
  ext k : 2
  rw [coeff_add, coeff_opJet1_aux, coeff_opJet1_aux, coeff_opJet1_aux, coeff_add, locJet1_add]

private theorem opJet0_add_aux (P Q : LocOp) : opJet0 (P + Q) = opJet0 P + opJet0 Q :=
  Polynomial.map_add _

private theorem opJet0_monomial_aux (k : ℕ) (a : LocPoly) :
    opJet0 (monomial k a) = monomial k (locJet0 a) :=
  Polynomial.map_monomial _

private theorem opJet1_monomial_aux (k : ℕ) (a : LocPoly) :
    opJet1 (monomial k a) = monomial k (locJet1 a) := by
  ext n : 2
  rw [coeff_opJet1_aux]
  rcases eq_or_ne k n with rfl | hne
  · rw [coeff_monomial_same, coeff_monomial_same]
  · rw [coeff_monomial_of_ne _ hne.symm, coeff_monomial_of_ne _ hne.symm]
    ext m
    rw [coeff_locJet1, coeff_zero, map_zero, coeff_zero]

private theorem innerDerivative_monomial_opJets (k : ℕ) (c : ℂ[X]) :
    innerDerivative (monomial k c) = monomial k (derivative c) := by
  unfold innerDerivative
  rw [Polynomial.sum_monomial_index]
  rw [derivative_zero, monomial_zero_right]

private theorem X_mul_derivative_monomial_opJets (i : ℕ) (a : ℂ[X]) :
    (X : ℂ[X][X]) * derivative (monomial i a) = monomial i (C (i : ℂ) * a) := by
  rcases i with _ | i
  · simp
  · rw [derivative_monomial, X_mul_monomial, Nat.add_sub_cancel, ← C_eq_natCast, mul_comm]

theorem opJet0_oreMul (δ : LocDilation) (S R : LocOp) :
    opJet0 (oreMul δ.shiftHom S R) = opJet0 S * opJet0 R := by
  induction S using Polynomial.induction_on' with
  | add p q hp hq => rw [oreMul_add_left, opJet0_add_aux, hp, hq, opJet0_add_aux, add_mul]
  | monomial i a =>
    induction R using Polynomial.induction_on' with
    | add p q hp hq => rw [oreMul_add_right, opJet0_add_aux, hp, hq, opJet0_add_aux, mul_add]
    | monomial k b =>
      rw [oreMul_monomial_monomial, opJet0_monomial_aux, opJet0_monomial_aux,
        opJet0_monomial_aux, monomial_mul_monomial, map_mul, locJet0_shift]

/-- Formula (6): the first jet of an Ore product. -/
theorem opJet1_oreMul (δ : LocDilation) (S R : LocOp) :
    opJet1 (oreMul δ.shiftHom S R) =
      opJet1 S * opJet0 R + opJet0 S * opJet1 R +
        C (C δ.c) * (X * derivative (opJet0 S)) * (C X * innerDerivative (opJet0 R)) := by
  induction S using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [oreMul_add_left, opJet1_add_aux, opJet0_add_aux, derivative_add, hp, hq]
    ring
  | monomial i a =>
    induction R using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [oreMul_add_right, opJet1_add_aux, opJet0_add_aux, innerDerivative_add, hp, hq]
      ring
    | monomial k b =>
      rw [oreMul_monomial_monomial, opJet1_monomial_aux, opJet1_monomial_aux,
        opJet1_monomial_aux, opJet0_monomial_aux, opJet0_monomial_aux,
        X_mul_derivative_monomial_opJets, innerDerivative_monomial_opJets, C_mul_monomial,
        C_mul_monomial, monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial,
        ← map_add, ← map_add, locJet1_mul, locJet1_shift, locJet0_shift]
      refine congrArg (monomial (i + k)) ?_
      rw [C_mul]
      ring

theorem opJet1_C_mul (β : LocPoly) (P : LocOp) :
    opJet1 (C β * P) = C (locJet1 β) * opJet0 P + C (locJet0 β) * opJet1 P := by
  ext k : 2
  rw [coeff_opJet1_aux, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_opJet1_aux,
    locJet1_mul, opJet0, coeff_map, mul_comm (locJet0 β) (locJet1 (P.coeff k)), mul_comm]

/-- The numerator `(r₀)₁ (r_d)₀ - (r₀)₀ (r_d)₁` of the logarithmic first jet of `r₀ / r_d`. -/
def locLogJetNum (R : LocOp) : ℂ[X] :=
  locJet1 (R.coeff 0) * locJet0 R.leadingCoeff - locJet0 (R.coeff 0) * locJet1 R.leadingCoeff

/-- The denominator `(r₀)₀ (r_d)₀` of the logarithmic first jet of `r₀ / r_d`. -/
def locLogJetDen (R : LocOp) : ℂ[X] :=
  locJet0 (R.coeff 0) * locJet0 R.leadingCoeff

/-- The coefficients of the first jet of an operator: `(P₁)_k = (a_k)₁`. -/
theorem coeff_opJet1 (P : LocOp) (k : ℕ) : (opJet1 P).coeff k = locJet1 (P.coeff k) :=
  coeff_opJet1_aux P k

/-- The first jet of an operator is additive. -/
theorem opJet1_add (P Q : LocOp) : opJet1 (P + Q) = opJet1 P + opJet1 Q :=
  opJet1_add_aux P Q

end AJConjecture
