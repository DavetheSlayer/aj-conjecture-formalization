import Mathlib
import AJConjecture.ExtraFactorPrime
import AJTwist.Quantum.TwQSymbolFacts
import AJTwist.Factor.TwFBlockCount
import AJTwist.Factor.TwFNegNoSeparation

/-!
# `P_(-b)` has no proper right factor (TwF, unit F2)

Source: revision 5, Section 5.4 (`operators.tex`, "Negative effective index"), last display and
"For the two ranges in the display the resulting connected graph obstructs factorization over
`ℂ((ε))(M)`, hence over the embedded `ℚ(t, M)`."

`natDegree_eq_zero_or_of_oreMul_eq_twTransferOp_neg`: for `b ≥ 1`, in every pseudo-factorisation
`β · P_(-b) = S ⋆ R` the right factor has degree `0` or `2b + 2`.

Route: `natDegree_eq_zero_or_of_linked_blocks` with `(G₁, G₂, G₃) = (L - 1, C_b, E)`:
the symbol `specialize_twTransferOp_neg_mul_eq` (reorder the product), full degree
(`natDegree_specialize_twTransferOp`, `natDegree_twTransferOp`, `twWindow_neg_natCast`), the three
primes, the constant coefficients `-1`, `M^(8b-2)`, `M⁴`, pairwise non-association
(`not_toComparison_dvd_twistPolyNeg`; `L - 1` and `E` by degree), and the two links
`toComparison_X_sub_one_dvd_iff_twistPolyNeg_dvd`,
`toComparison_extraFactor_dvd_iff_twistPolyNeg_dvd` (the second read from right to left).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The two polynomials in `M` of the symbol identity of `P_(-b)` are not zero. -/
private theorem symbol_scalars_ne_zero_twfNegIrred (b : ℕ) :
    ((X ^ 2 - 1) ^ (2 * b + 2) * (X ^ 4 - 1) ^ (2 * b + 2) : ℤ[X]) ≠ 0 ∧
      (-((twDet (2 * b + 2) (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1))) : ℤ[X]) ≠
        0 := by
  have h1 : (2 : ℂ) ^ 2 ≠ 1 := by norm_num
  have h2 : (2 : ℂ) ^ 2 ≠ -1 := by norm_num
  refine ⟨mul_ne_zero (pow_ne_zero _ (X_pow_sub_C_ne_zero two_pos 1))
    (pow_ne_zero _ (X_pow_sub_C_ne_zero (by norm_num) 1)), fun h ↦ ?_⟩
  have hev := congrArg (fun p : ℤ[X] ↦ (p.map (Int.castRingHom ℂ)).eval 2) h
  simp only [Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_one, Polynomial.map_comp, map_X, eval_neg, eval_mul,
    eval_pow, eval_sub, eval_add, eval_X, eval_one, eval_comp, Polynomial.map_zero,
    eval_zero] at hev
  exact neg_ne_zero.mpr (mul_ne_zero (twDet_one_eval_ne_zero (2 * b + 2) h1 h2)
    (by norm_num)) hev

/-- The constant coefficients of the three blocks `L - 1`, `C_b`, `E` are not zero. -/
private theorem coeff_zero_blocks_ne_zero_twfNegIrred (b : ℕ) (hb : 1 ≤ b) :
    (X - 1 : ℤ[X][X]).coeff 0 ≠ 0 ∧ (twistPolyNeg b).coeff 0 ≠ 0 ∧ extraFactor.coeff 0 ≠ 0 := by
  refine ⟨by simp, ?_, ?_⟩
  · rw [coeff_zero_twistPolyNeg b hb]
    exact pow_ne_zero _ X_ne_zero
  · rw [extraFactor_coeff_zero]
    exact pow_ne_zero 4 X_ne_zero

/-- In the comparison ring `L - 1` does not divide `E`, and `C_b` does not divide `E`. -/
private theorem not_toComparison_dvd_extraFactor_twfNegIrred (b : ℕ) (hb : 1 ≤ b) :
    ¬ toComparison (X - 1) ∣ toComparison extraFactor ∧
      ¬ toComparison (twistPolyNeg b) ∣ toComparison extraFactor := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hev := eval_one_eq_zero_of_toComparison_X_sub_one_dvd h
    have h0 := congrArg (Polynomial.eval 1) hev
    simp [extraFactor] at h0
  · exact (not_toComparison_dvd_twistPolyNeg b hb).2
      (((prime_toComparison_twistPolyNeg b hb).dvd_prime_iff_associated
        prime_toComparison_extraFactor).mp h).dvd'

/-- For `b ≥ 1` the operator `P_(-b)` has no proper right factor over `ℚ(t, M)`: in every
pseudo-factorisation `β · P_(-b) = S ⋆ R` the right factor has degree `0` or `2b + 2`. -/
theorem natDegree_eq_zero_or_of_oreMul_eq_twTransferOp_neg (b : ℕ) (hb : 1 ≤ b) {β : Coeff}
    (hβ : β ≠ 0) {S R : RecOp} (h : C β * twTransferOp (-(b : ℤ)) = oreMul coeffShift S R) :
    R.natDegree = 0 ∨ R.natDegree = 2 * b + 2 := by
  obtain ⟨hκ₁, hκ₂⟩ := symbol_scalars_ne_zero_twfNegIrred b
  obtain ⟨hc₁, hc₂, hc₃⟩ := coeff_zero_blocks_ne_zero_twfNegIrred b hb
  obtain ⟨h13, h23⟩ := not_toComparison_dvd_extraFactor_twfNegIrred b hb
  have hP : (twTransferOp (-(b : ℤ))).natDegree = 2 * b + 2 := by
    rw [natDegree_twTransferOp, twWindow_neg_natCast b hb]
  have hsym : C ((X ^ 2 - 1) ^ (2 * b + 2) * (X ^ 4 - 1) ^ (2 * b + 2)) *
      specialize (twTransferOp (-(b : ℤ))) =
      C (-((twDet (2 * b + 2) (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1)))) *
        ((X - 1) * twistPolyNeg b * extraFactor) := by
    rw [specialize_twTransferOp_neg_mul_eq b hb]
    ring
  have hdeg : (specialize (twTransferOp (-(b : ℤ)))).natDegree =
      (twTransferOp (-(b : ℤ))).natDegree := by
    rw [natDegree_specialize_twTransferOp, natDegree_twTransferOp]
  rw [← hP]
  exact natDegree_eq_zero_or_of_linked_blocks hκ₁ hκ₂ hsym hdeg prime_toComparison_X_sub_one
    (prime_toComparison_twistPolyNeg b hb) prime_toComparison_extraFactor hc₁ hc₂ hc₃
    (not_toComparison_dvd_twistPolyNeg b hb).1 h13 h23
    (fun hβ' _ _ h' ↦ toComparison_X_sub_one_dvd_iff_twistPolyNeg_dvd b hb hβ' h')
    (fun hβ' _ _ h' ↦ (toComparison_extraFactor_dvd_iff_twistPolyNeg_dvd b hb hβ' h').symm)
    hβ h

end AJConjecture
