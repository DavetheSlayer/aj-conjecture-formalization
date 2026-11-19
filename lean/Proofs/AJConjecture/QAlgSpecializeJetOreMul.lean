import Mathlib
import AJConjecture.QAlgDualJetBasic
import AJConjecture.QAlgSpecializeOreMul
import AJConjecture.QAlgCoeffShiftBasic
import AJConjecture.QAlgNodeJetBasic
import AJConjecture.QAlgOreMulBasic

/-!
# The first jet of an Ore product

At `t = -1 + ε` the shift `σ^i : M ↦ t^(2i) M` is `M ↦ (1 - 2iε) M`, so for monomials
`(a L^i) ⋆ (b L^k) = a σ^i(b) L^(i+k)` has first jet `a¹ b⁰ + a⁰ (b¹ - 2i M ∂_M b⁰)`. Summing:
`(S ⋆ R)₁ = S₁ R₀ + S₀ R₁ - 2 (L ∂_L S₀)(M ∂_M R₀)`.
Left multiplication by a coefficient obeys the Leibniz rule. Proofs: bilinearity reduces to
monomials in `L`, then to monomials `a(t) M^e` of the coefficients.
-/

open Polynomial

namespace AJConjecture

/-- Base change `ℤ[M] → ℂ[M]` is injective. -/
private theorem map_intCast_injective_specJetOreMul :
    Function.Injective (Polynomial.map (Int.castRingHom ℂ)) :=
  Polynomial.map_injective (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int

/-- The first jet of coefficients is additive. -/
private theorem coeffJet_add_specJetOreMul (a b : Coeff) :
    coeffJet (a + b) = coeffJet a + coeffJet b := by
  apply map_intCast_injective_specJetOreMul
  rw [← complexJet_coeffToComplex, map_add, complexJet_add, Polynomial.map_add,
    complexJet_coeffToComplex, complexJet_coeffToComplex]

/-- The first jet of the zero coefficient. -/
theorem coeffJet_zero : coeffJet 0 = 0 := by
  simp [coeffJet]

/-- The Leibniz rule for the first jet of coefficients. -/
private theorem coeffJet_mul_specJetOreMul (a b : Coeff) :
    coeffJet (a * b) = coeffJet a * b.map (Polynomial.evalRingHom (-1)) +
      a.map (Polynomial.evalRingHom (-1)) * coeffJet b := by
  apply map_intCast_injective_specJetOreMul
  rw [← complexJet_coeffToComplex, map_mul, complexJet_mul, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_mul, complexJet_coeffToComplex,
    complexJet_coeffToComplex, complexSpec_coeffToComplex, complexSpec_coeffToComplex]

/-- The first jet of a shifted coefficient. -/
private theorem coeffJet_coeffShift_specJetOreMul (c : Coeff) :
    coeffJet (coeffShift c) =
      coeffJet c - 2 * X * derivative (c.map (Polynomial.evalRingHom (-1))) := by
  apply map_intCast_injective_specJetOreMul
  rw [← complexJet_coeffToComplex, ← complexShift_coeffToComplex, complexJet_complexShift,
    complexJet_coeffToComplex, complexSpec_coeffToComplex, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_mul, derivative_map, Polynomial.map_X,
    Polynomial.map_ofNat]

/-- The first jet of an iterated shift of a coefficient. -/
private theorem coeffJet_iterate_coeffShift_specJetOreMul (i : ℕ) (c : Coeff) :
    coeffJet (coeffShift^[i] c) =
      coeffJet c - 2 * (i : ℤ[X]) * X * derivative (c.map (Polynomial.evalRingHom (-1))) := by
  induction i generalizing c with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, coeffJet_coeffShift_specJetOreMul,
      map_evalRingHom_coeffShift, Nat.cast_succ]
    ring

/-- The first jet of a monomial in `L`. -/
private theorem specializeJet_monomial_specJetOreMul (n : ℕ) (c : Coeff) :
    specializeJet (monomial n c) = monomial n (coeffJet c) := by
  ext k : 2
  rw [coeff_specializeJet, coeff_monomial_apply, coeff_monomial_apply]
  split_ifs with h
  · rfl
  · exact coeffJet_zero

/-- The value at `t = -1` of a monomial in `L`. -/
private theorem specialize_monomial_specJetOreMul (n : ℕ) (c : Coeff) :
    specialize (monomial n c) = monomial n (c.map (Polynomial.evalRingHom (-1))) := by
  rw [specialize, coe_mapRingHom, map_monomial, coe_mapRingHom]

/-- The derivative in `M` is additive. -/
private theorem coeffDerivative_add_specJetOreMul (p q : ℤ[X][X]) :
    coeffDerivative (p + q) = coeffDerivative p + coeffDerivative q := by
  unfold coeffDerivative
  refine Polynomial.sum_add_index p q _ (fun k ↦ ?_) (fun k a b ↦ ?_)
  · rw [derivative_zero, monomial_zero_right]
  · rw [derivative_add, map_add]

/-- The derivative in `M` of a monomial in `L`. -/
private theorem coeffDerivative_monomial_specJetOreMul (k : ℕ) (c : ℤ[X]) :
    coeffDerivative (monomial k c) = monomial k (derivative c) := by
  unfold coeffDerivative
  rw [Polynomial.sum_monomial_index]
  rw [derivative_zero, monomial_zero_right]

/-- `L ∂_L` of a monomial in `L`. -/
private theorem X_mul_derivative_monomial_specJetOreMul (i : ℕ) (c : ℤ[X]) :
    (X * derivative (monomial i c) : ℤ[X][X]) = monomial i (c * (i : ℤ[X])) := by
  rw [derivative_monomial]
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [Nat.add_sub_cancel, X_mul_monomial]

/-- The first jet of an Ore product of monomials. -/
private theorem specializeJet_oreMul_monomial_specJetOreMul (i k : ℕ) (a b : Coeff) :
    specializeJet (oreMul coeffShift (monomial i a) (monomial k b)) =
      specializeJet (monomial i a) * specialize (monomial k b) +
          specialize (monomial i a) * specializeJet (monomial k b) -
        2 * (X * derivative (specialize (monomial i a))) *
          (C X * coeffDerivative (specialize (monomial k b))) := by
  rw [oreMul_monomial_monomial, specializeJet_monomial_specJetOreMul,
    specializeJet_monomial_specJetOreMul, specializeJet_monomial_specJetOreMul,
    specialize_monomial_specJetOreMul, specialize_monomial_specJetOreMul,
    X_mul_derivative_monomial_specJetOreMul, coeffDerivative_monomial_specJetOreMul,
    C_mul_monomial, monomial_mul_monomial, monomial_mul_monomial, ← C_ofNat, C_mul_monomial,
    monomial_mul_monomial, ← map_add, ← map_sub, coeffJet_mul_specJetOreMul,
    coeffJet_iterate_coeffShift_specJetOreMul, map_evalRingHom_iterate_coeffShift]
  refine congrArg _ ?_
  ring

/-- The first jet at `t = -1` of an Ore product:
`(S ⋆ R)₁ = S₁ R₀ + S₀ R₁ - 2 (L ∂_L S₀)(M ∂_M R₀)`. -/
theorem specializeJet_oreMul (S R : RecOp) :
    specializeJet (oreMul coeffShift S R) =
      specializeJet S * specialize R + specialize S * specializeJet R -
        2 * (X * derivative (specialize S)) * (C X * coeffDerivative (specialize R)) := by
  induction S using Polynomial.induction_on' with
  | add p p' hp hp' =>
    rw [oreMul_add_left, specializeJet_add, hp, hp',
      specializeJet_add, map_add, derivative_add]
    ring
  | monomial i a =>
    induction R using Polynomial.induction_on' with
    | add q q' hq hq' =>
      rw [oreMul_add_right, specializeJet_add, hq, hq',
        specializeJet_add, map_add, coeffDerivative_add_specJetOreMul]
      ring
    | monomial k b => exact specializeJet_oreMul_monomial_specJetOreMul i k a b

/-- The first jet at `t = -1` of a left multiple by a coefficient. -/
theorem specializeJet_C_mul (β : Coeff) (P : RecOp) :
    specializeJet (C β * P) =
      C (coeffJet β) * specialize P +
        C (β.map (Polynomial.evalRingHom (-1))) * specializeJet P := by
  rw [← oreMul_C_left coeffShift, specializeJet_oreMul, ← monomial_zero_left,
    specializeJet_monomial_specJetOreMul, specialize_monomial_specJetOreMul,
    monomial_zero_left, monomial_zero_left, derivative_C, mul_zero, mul_zero, zero_mul,
    sub_zero]

end AJConjecture
