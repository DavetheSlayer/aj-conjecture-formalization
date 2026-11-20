import Mathlib
import AJConjecture.QAlgNodeJet
import AJConjecture.QAlgNodeJetBasic
import AJConjecture.QAlgSpecializeJetOreMul
import AJTwist.Factor.TwFZeroIntegral

/-!
# Rules for the first jet at `t = -1` (Unit PpL, tools)

The first jet `coeffJet c = (∂c/∂t)(-1, ·)` of a coefficient `c ∈ ℤ[t][x]` is a derivation over
the value `c ↦ c(-1, ·)`. The rules below are the private lemmas of
`AJTwist/Factor/TwFZeroJet.lean`, `TwFZeroEven.lean` and `TwFZeroInfinity.lean`, restated
publicly (with the same proofs) so that the nodes of this package share them:

* `ppl_coeffJet_add`, `_neg`, `_sub`, `_mul`, `_sq`, `_C`, `_X`, `_X_pow`, `_one`, `_ofNat`,
  `_monomial`;
* `ppl_eval_derivative_X_pow`: `(t^m)'(-1) = -m (-1)^m`; `ppl_coeffJet_C_X_pow_even`: the value
  and the jet of an even power `t^(2n)` are `1` and `-2n`;
* `ppl_coeffJet_twfSq`: the jet commutes with `x ↦ M²`;
* `ppl_coeffJet_twfShiftX`: the jet of `c(t, t⁴ x)` is `coeffJet c - 4 x ∂_x c(-1, x)`;
* `ppl_map_evalRingHom_twfLin`, `ppl_coeffJet_twfLin`: the linear forms `ℓ_j = t^(4j) x - 1`
  have value `x - 1` and jet `-4 j x`;
* `ppl_logJet_mul`, `ppl_logJet_pow`, `ppl_logJet_twfLin`: logarithmic jets of the form
  `4 s x/(x - 1)` are closed under products and powers, and `ℓ_j` has `s = -j`;
* `ppl_coeff_X_mul_derivative`: `x ∂_x` multiplies the coefficient of `x^n` by `n`.

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Base change `ℤ[M] → ℂ[M]` is injective. -/
private theorem map_intCast_injective_pplJetRules :
    Function.Injective (Polynomial.map (Int.castRingHom ℂ)) :=
  Polynomial.map_injective (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int

/-- The first jet of coefficients is additive. -/
theorem ppl_coeffJet_add (a b : Coeff) : coeffJet (a + b) = coeffJet a + coeffJet b := by
  apply map_intCast_injective_pplJetRules
  rw [← complexJet_coeffToComplex, map_add, complexJet_add, Polynomial.map_add,
    complexJet_coeffToComplex, complexJet_coeffToComplex]

/-- The Leibniz rule for the first jet of coefficients. -/
theorem ppl_coeffJet_mul (a b : Coeff) :
    coeffJet (a * b) = coeffJet a * b.map (Polynomial.evalRingHom (-1)) +
      a.map (Polynomial.evalRingHom (-1)) * coeffJet b := by
  apply map_intCast_injective_pplJetRules
  rw [← complexJet_coeffToComplex, map_mul, complexJet_mul, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_mul, complexJet_coeffToComplex,
    complexJet_coeffToComplex, complexSpec_coeffToComplex, complexSpec_coeffToComplex]

/-- The first jet of a monomial in `x`. -/
theorem ppl_coeffJet_monomial (n : ℕ) (a : ℤ[X]) :
    coeffJet (monomial n a) = monomial n ((derivative a).eval (-1)) := by
  rw [coeffJet, sum_monomial_index]
  rw [derivative_zero, eval_zero, monomial_zero_right]

/-- The first jet of a polynomial in `t` alone. -/
theorem ppl_coeffJet_C (a : ℤ[X]) : coeffJet (C a) = C ((derivative a).eval (-1)) := by
  rw [← monomial_zero_left, ppl_coeffJet_monomial, monomial_zero_left]

/-- The first jet of `x`. -/
theorem ppl_coeffJet_X : coeffJet (X : Coeff) = 0 := by
  rw [← monomial_one_one_eq_X, ppl_coeffJet_monomial, derivative_one, eval_zero,
    monomial_zero_right]

/-- The first jet of a power of `x`. -/
theorem ppl_coeffJet_X_pow (n : ℕ) : coeffJet (X ^ n : Coeff) = 0 := by
  rw [X_pow_eq_monomial, ppl_coeffJet_monomial, derivative_one, eval_zero, monomial_zero_right]

/-- The first jet of `1`. -/
theorem ppl_coeffJet_one : coeffJet (1 : Coeff) = 0 := by
  rw [← C_1, ppl_coeffJet_C, derivative_one, eval_zero, C_0]

/-- The first jet of a numeral. -/
theorem ppl_coeffJet_ofNat (n : ℕ) [n.AtLeastTwo] : coeffJet (OfNat.ofNat n : Coeff) = 0 := by
  rw [← C_ofNat, ppl_coeffJet_C, ← C_ofNat, derivative_C, eval_zero, C_0]

/-- The first jet of an opposite. -/
theorem ppl_coeffJet_neg (a : Coeff) : coeffJet (-a) = -coeffJet a := by
  have h := ppl_coeffJet_add a (-a)
  rw [add_neg_cancel, coeffJet_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The first jet of a difference. -/
theorem ppl_coeffJet_sub (a b : Coeff) : coeffJet (a - b) = coeffJet a - coeffJet b := by
  rw [sub_eq_add_neg, ppl_coeffJet_add, ppl_coeffJet_neg, sub_eq_add_neg]

/-- The first jet of a square. -/
theorem ppl_coeffJet_sq (a : Coeff) :
    coeffJet (a ^ 2) = 2 * a.map (Polynomial.evalRingHom (-1)) * coeffJet a := by
  rw [sq, ppl_coeffJet_mul]
  ring

/-- The derivative of `t^m` at `t = -1`. -/
theorem ppl_eval_derivative_X_pow (m : ℕ) :
    (derivative (X ^ m : ℤ[X])).eval (-1) = -((m : ℤ) * (-1) ^ m) := by
  rcases m with _ | m
  · simp
  · rw [derivative_X_pow, eval_mul, eval_C, eval_pow, eval_X, Nat.add_sub_cancel, pow_succ]
    push_cast
    ring

/-- The value and the first jet of an even power of `t`. -/
theorem ppl_coeffJet_C_X_pow_even (n : ℕ) :
    (C (X ^ (2 * n)) : Coeff).map (Polynomial.evalRingHom (-1 : ℤ)) = 1 ∧
      coeffJet (C (X ^ (2 * n)) : Coeff) = -((2 * n : ℕ) : ℤ[X]) := by
  constructor
  · rw [map_C, coe_evalRingHom, eval_pow, eval_X, Even.neg_one_pow ⟨n, by ring⟩, C_1]
  · rw [ppl_coeffJet_C, ppl_eval_derivative_X_pow, Even.neg_one_pow ⟨n, by ring⟩, mul_one,
      C_neg, eq_intCast (C : ℤ →+* ℤ[X])]
    push_cast
    ring

/-- `x ∂_x` multiplies the coefficient of `x^n` by `n`. -/
theorem ppl_coeff_X_mul_derivative (p : ℤ[X]) (n : ℕ) :
    (X * derivative p).coeff n = (n : ℤ) * p.coeff n := by
  rcases n with _ | n
  · rw [coeff_X_mul_zero, Nat.cast_zero, zero_mul]
  · rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- The first jet commutes with `x ↦ M²`. -/
theorem ppl_coeffJet_twfSq (c : Coeff) : coeffJet (twfSq c) = (coeffJet c).comp (X ^ 2) := by
  induction c using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, ppl_coeffJet_add, hp, hq, ppl_coeffJet_add, add_comp]
  | monomial n a =>
    have h1 : twfSq (monomial n a) = monomial (2 * n) a := by
      change (monomial n a).comp (X ^ 2) = _
      rw [monomial_comp, ← pow_mul, C_mul_X_pow_eq_monomial]
    rw [h1, ppl_coeffJet_monomial, ppl_coeffJet_monomial, monomial_comp, ← pow_mul,
      C_mul_X_pow_eq_monomial]

/-- The value at `t = -1` commutes with `x ↦ M²`. -/
theorem ppl_map_evalRingHom_twfSq (c : Coeff) :
    (twfSq c).map (Polynomial.evalRingHom (-1 : ℤ)) =
      (c.map (Polynomial.evalRingHom (-1 : ℤ))).comp (X ^ 2) := by
  change (c.comp (X ^ 2)).map (Polynomial.evalRingHom (-1 : ℤ)) = _
  rw [map_comp, Polynomial.map_pow, map_X]

/-- The first jet of a shifted coefficient: `x ↦ t⁴ x` is `x ↦ (1 - 4ε) x` at `t = -1 + ε`. -/
theorem ppl_coeffJet_twfShiftX (c : Coeff) :
    coeffJet (twfShiftX c) =
      coeffJet c - 4 * (X * derivative (c.map (Polynomial.evalRingHom (-1 : ℤ)))) := by
  induction c using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, ppl_coeffJet_add, hp, hq, ppl_coeffJet_add, Polynomial.map_add,
      derivative_add]
    ring
  | monomial n a =>
    have h1 : twfShiftX (monomial n a) = monomial n (a * X ^ (4 * n)) := by
      change (monomial n a).comp (C (X ^ 4) * X) = _
      rw [monomial_comp, mul_pow, ← C_pow, ← pow_mul, ← mul_assoc, ← C_mul,
        C_mul_X_pow_eq_monomial]
    have h4 : (4 : ℤ[X]) = C 4 := (C_ofNat 4).symm
    rw [h1, ppl_coeffJet_monomial, ppl_coeffJet_monomial, Polynomial.map_monomial,
      coe_evalRingHom]
    ext k
    rw [coeff_sub, h4, coeff_C_mul, ppl_coeff_X_mul_derivative, coeff_monomial_apply,
      coeff_monomial_apply, coeff_monomial_apply, derivative_mul, eval_add, eval_mul, eval_mul,
      eval_pow, eval_X, ppl_eval_derivative_X_pow, Even.neg_one_pow ⟨2 * n, by ring⟩]
    split_ifs with hk
    · subst hk
      push_cast
      ring
    · ring

/-- At `t = -1` the linear forms `ℓ_j` become `x - 1`. -/
theorem ppl_map_evalRingHom_twfLin (j : ℕ) :
    (twfLin j).map (Polynomial.evalRingHom (-1 : ℤ)) = X - 1 := by
  rw [twfLin, Polynomial.map_sub, Polynomial.map_mul, map_C, map_X, Polynomial.map_one,
    coe_evalRingHom, eval_pow, eval_X, pow_mul]
  norm_num

/-- The first jet of the linear forms `ℓ_j`. -/
theorem ppl_coeffJet_twfLin (j : ℕ) : coeffJet (twfLin j) = -(4 * (j : ℤ[X]) * X) := by
  have hsub : twfLin j = C (X ^ (4 * j)) * X + -1 := by rw [twfLin, sub_eq_add_neg]
  rw [hsub, ppl_coeffJet_add, ppl_coeffJet_neg, ppl_coeffJet_one, ppl_coeffJet_mul,
    ppl_coeffJet_C, ppl_coeffJet_X, map_X, ppl_eval_derivative_X_pow,
    Even.neg_one_pow ⟨2 * j, by ring⟩, mul_zero, add_zero, neg_zero, add_zero, mul_one, C_neg,
    eq_intCast (C : ℤ →+* ℤ[X])]
  push_cast
  ring

/-- Logarithmic first jets of the form `4 s x/(x - 1)` are closed under products. -/
theorem ppl_logJet_mul {f g : Coeff} {s r : ℤ}
    (hf : coeffJet f * (X - 1) =
      4 * (s : ℤ[X]) * X * f.map (Polynomial.evalRingHom (-1 : ℤ)))
    (hg : coeffJet g * (X - 1) =
      4 * (r : ℤ[X]) * X * g.map (Polynomial.evalRingHom (-1 : ℤ))) :
    coeffJet (f * g) * (X - 1) =
      4 * ((s + r : ℤ) : ℤ[X]) * X * (f * g).map (Polynomial.evalRingHom (-1 : ℤ)) := by
  rw [ppl_coeffJet_mul, Polynomial.map_mul, Int.cast_add]
  linear_combination g.map (Polynomial.evalRingHom (-1 : ℤ)) * hf +
    f.map (Polynomial.evalRingHom (-1 : ℤ)) * hg

/-- Logarithmic first jets of the form `4 s x/(x - 1)` are closed under powers. -/
theorem ppl_logJet_pow {f : Coeff} {s : ℤ}
    (hf : coeffJet f * (X - 1) =
      4 * (s : ℤ[X]) * X * f.map (Polynomial.evalRingHom (-1 : ℤ))) (n : ℕ) :
    coeffJet (f ^ n) * (X - 1) =
      4 * (((n : ℤ) * s : ℤ) : ℤ[X]) * X * (f ^ n).map (Polynomial.evalRingHom (-1 : ℤ)) := by
  induction n with
  | zero => simp [ppl_coeffJet_one]
  | succ n ih =>
    have h := ppl_logJet_mul ih hf
    rw [pow_succ, show ((n + 1 : ℕ) : ℤ) * s = (n : ℤ) * s + s by push_cast; ring]
    exact h

/-- The logarithmic first jet of `ℓ_j` is `-4 j x/(x - 1)`. -/
theorem ppl_logJet_twfLin (j : ℕ) :
    coeffJet (twfLin j) * (X - 1) =
      4 * ((-(j : ℤ) : ℤ) : ℤ[X]) * X * (twfLin j).map (Polynomial.evalRingHom (-1 : ℤ)) := by
  rw [ppl_coeffJet_twfLin, ppl_map_evalRingHom_twfLin]
  push_cast
  ring

end AJConjecture
