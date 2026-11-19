import Mathlib
import AJConjecture.QAlgCoeffShift
import AJConjecture.QAlgNodeJet

/-!
# Rules for the jets at `t = -1`

The value at `t = -1` is a ring homomorphism that does not see the shift (`t² = 1`); the first
jet is additive, satisfies the Leibniz rule, and the shift `M ↦ t² M` changes it by
`-2 M ∂_M` of the value (`(t²)' = -2` at `t = -1`: for `f = a(t) M^e`,
`(a t^(2e))'(-1) = a'(-1) - 2e a(-1)`). Base change from `ℤ` commutes with everything.
All proofs: reduce to monomials (`Polynomial.induction_on'`, `Polynomial.sum_monomial_index`).
-/

open Polynomial

namespace AJConjecture

/-- The coefficients of the first jet over `ℂ`. -/
private theorem coeff_complexJet_nodeJetBasic (f : ℂ[X][X]) (e : ℕ) :
    (complexJet f).coeff e = (derivative (f.coeff e)).eval (-1) := by
  unfold complexJet
  rw [Polynomial.sum_def, finsetSum_coeff]
  simp only [coeff_monomial_apply, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.mp h, derivative_zero, eval_zero]

/-- The coefficients of the first jet over `ℤ`. -/
private theorem coeff_coeffJet_nodeJetBasic (c : Coeff) (e : ℕ) :
    (coeffJet c).coeff e = (derivative (c.coeff e)).eval (-1) := by
  unfold coeffJet
  rw [Polynomial.sum_def, finsetSum_coeff]
  simp only [coeff_monomial_apply, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.mp h, derivative_zero, eval_zero]

/-- The first jet of a monomial. -/
private theorem complexJet_monomial_nodeJetBasic (e : ℕ) (a : ℂ[X]) :
    complexJet (monomial e a) = monomial e ((derivative a).eval (-1)) := by
  ext n
  rw [coeff_complexJet_nodeJetBasic, coeff_monomial_apply, coeff_monomial_apply]
  split_ifs with h
  · rfl
  · rw [derivative_zero, eval_zero]

/-- The value at `t = -1` does not see the shift `M ↦ t² M`. -/
theorem complexSpec_complexShift (f : ℂ[X][X]) : complexSpec (complexShift f) = complexSpec f := by
  have hcomp : complexShift f = f.comp (C (X ^ 2) * X : ℂ[X][X]) := rfl
  rw [hcomp, complexSpec, coe_mapRingHom, map_comp]
  simp

/-- The first jet is additive. -/
theorem complexJet_add (f g : ℂ[X][X]) : complexJet (f + g) = complexJet f + complexJet g := by
  ext n
  simp only [coeff_complexJet_nodeJetBasic, coeff_add, derivative_add, eval_add]

/-- The Leibniz rule for the first jet. -/
theorem complexJet_mul (f g : ℂ[X][X]) :
    complexJet (f * g) = complexJet f * complexSpec g + complexSpec f * complexJet g := by
  ext n
  simp only [coeff_complexJet_nodeJetBasic, coeff_add, coeff_mul, derivative_sum, eval_finsetSum,
    derivative_mul, eval_add, eval_mul, Finset.sum_add_distrib, complexSpec, coe_mapRingHom,
    coeff_map, coe_evalRingHom]

/-- The first jet of a shifted coefficient: `(σ f)¹ = f¹ - 2 M ∂_M f⁰`. -/
theorem complexJet_complexShift (f : ℂ[X][X]) :
    complexJet (complexShift f) = complexJet f - 2 * X * derivative (complexSpec f) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, complexJet_add, hp, hq, complexJet_add, map_add, derivative_add]
    ring
  | monomial e a =>
    have hshift : complexShift (monomial e a) = monomial e (a * X ^ (2 * e)) := by
      have hcomp : complexShift (monomial e a) =
          (monomial e a).comp (C (X ^ 2) * X : ℂ[X][X]) := rfl
      rw [hcomp, ← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp, mul_pow,
        ← C_pow, ← pow_mul, ← mul_assoc, ← C_mul, C_mul_X_pow_eq_monomial]
    have hspec : complexSpec (monomial e a) = monomial e (a.eval (-1)) := by
      rw [complexSpec, coe_mapRingHom, map_monomial, coe_evalRingHom]
    rw [hshift, complexJet_monomial_nodeJetBasic, complexJet_monomial_nodeJetBasic, hspec,
      derivative_monomial, derivative_mul, derivative_X_pow]
    have hpow : ((-1 : ℂ) ^ (2 * e)) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      simp
    · have hpow' : ((-1 : ℂ) ^ (2 * e - 1)) = -1 := by
        have h2 : (-1 : ℂ) ^ (2 * e - 1) * (-1) = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), hpow]
        linear_combination -h2
      have hX : (2 * X * monomial (e - 1) (a.eval (-1) * (e : ℂ)) : ℂ[X]) =
          monomial e (2 * (a.eval (-1) * (e : ℂ))) := by
        rw [mul_assoc, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
        obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
        rw [Nat.add_sub_cancel, C_mul, C_mul, C_mul, pow_succ, C_ofNat]
        ring
      rw [hX, ← monomial_sub]
      congr 1
      simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, hpow, hpow',
        Nat.cast_mul, Nat.cast_ofNat]
      ring

/-- Base change commutes with the shift. -/
theorem complexShift_coeffToComplex (c : Coeff) :
    complexShift (coeffToComplex c) = coeffToComplex (coeffShift c) := by
  have hcomp : complexShift (coeffToComplex c) =
      (coeffToComplex c).comp (C (X ^ 2) * X : ℂ[X][X]) := rfl
  have hcomp' : coeffShift c = c.comp (C (X ^ 2) * X : Coeff) := rfl
  rw [hcomp, hcomp', coeffToComplex, coe_mapRingHom, map_comp]
  simp

/-- Base change commutes with the value at `t = -1`. -/
theorem complexSpec_coeffToComplex (c : Coeff) :
    complexSpec (coeffToComplex c) =
      (c.map (Polynomial.evalRingHom (-1))).map (Int.castRingHom ℂ) := by
  rw [complexSpec, coeffToComplex, coe_mapRingHom, coe_mapRingHom, map_map, map_map]
  congr 1
  ext
  · simp
  · simp

/-- Base change commutes with the first jet. -/
theorem complexJet_coeffToComplex (c : Coeff) :
    complexJet (coeffToComplex c) = (coeffJet c).map (Int.castRingHom ℂ) := by
  ext n
  rw [coeff_complexJet_nodeJetBasic, coeff_map, coeff_coeffJet_nodeJetBasic, coeffToComplex,
    coe_mapRingHom, coeff_map, coe_mapRingHom, derivative_map, eval_map]
  have h := eval₂_at_apply (p := derivative (c.coeff n)) (Int.castRingHom ℂ) (-1)
  simpa using h

/-- The coefficients of the symbol are the values at `t = -1` of the coefficients. -/
theorem coeff_specialize (P : RecOp) (k : ℕ) :
    (specialize P).coeff k = (P.coeff k).map (Polynomial.evalRingHom (-1)) := by
  rw [specialize, coe_mapRingHom, coeff_map, coe_mapRingHom]

/-- The coefficients of the first jet of an operator are the first jets of its coefficients. -/
theorem coeff_specializeJet (P : RecOp) (k : ℕ) :
    (specializeJet P).coeff k = coeffJet (P.coeff k) := by
  unfold specializeJet
  rw [Polynomial.sum_def, finsetSum_coeff]
  simp only [coeff_monomial_apply, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.mp h]
    simp [coeffJet]

end AJConjecture
