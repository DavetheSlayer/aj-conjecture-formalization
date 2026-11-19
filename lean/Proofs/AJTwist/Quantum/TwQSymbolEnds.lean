import Mathlib
import AJTwist.Quantum.TwQSymbolFacts
import AJFamily.Quantum.AbNodeNoSeparation

/-!
# The factor `E` and the endpoints of the symbol of `P_a` (Unit Q3)

Source: revision 5, Section 3.4 ("The factor `E` is present in each symbol") and Section 5.1
(`operators.tex`, "Retention of the shift endpoints": "both shift endpoints are units at all such
`x₀` in every case").

For every integer `a`:

* `extraFactor_dvd_specialize_twTransferOp`: `E` divides the symbol in `ℚ(M)[L, L⁻¹]`;
* `eval_coeff_specialize_twTransferOp_ne_zero`: the leading and the constant coefficient of the
  symbol do not vanish at `M = m₀` with `m₀ ≠ 0`, `m₀² ≠ ± 1`. With `x = M²` they are `κ₂/κ₁`
  times `x^(2a)`, `-x^(2a+2)` for `a ≥ 1`; `1`, `-x²` for `a = 0`; `1`, `-x^(4b+1)` for `a = -b`
  (checked at random points for `-6 ≤ a ≤ 6`, scratch `check_symbol_mod.py`).

For `a ≥ 1` these are the library's `extraFactor_dvd_specialize_famTransferOp`,
`eval_coeff_specialize_famTransferOp_ne_zero`; the cases `a ≤ 0` follow in the same way from
`specialize_twTransferOp_mul_eq`, `twDet_one_eval_ne_zero`, `monic_twistPolyNeg` and
`coeff_zero_twistPolyNeg`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The polynomial in `M` on the left of the symbol identity is not zero. -/
private theorem symbolLeft_ne_zero_twSymbolEnds (d : ℕ) :
    ((X ^ 2 - 1) ^ d * (X ^ 4 - 1) ^ d : ℤ[X]) ≠ 0 := by
  have h2 : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval 0) h
    simp at h0
  have h4 : (X ^ 4 - 1 : ℤ[X]) ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval 0) h
    simp at h0
  exact mul_ne_zero (pow_ne_zero d h2) (pow_ne_zero d h4)

/-- The extra factor divides the symbol of `P_a` in the comparison ring, for every `a`. -/
theorem extraFactor_dvd_specialize_twTransferOp (a : ℤ) :
    toComparison extraFactor ∣ toComparison (specialize (twTransferOp a)) := by
  refine (isUnit_toComparison_coeff_of_ne_zero
    (symbolLeft_ne_zero_twSymbolEnds (twWindow a))).dvd_mul_left.mp ?_
  rw [← map_mul, specialize_twTransferOp_mul_eq a]
  exact map_dvd toComparison (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _)

/-- The leading and the constant coefficient of the varying block are powers of `M`. -/
private theorem twBlock_ends_twSymbolEnds (a : ℤ) :
    ∃ j k : ℕ, (twBlock a).leadingCoeff = X ^ j ∧ (twBlock a).coeff 0 = X ^ k := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · obtain ⟨b, rfl⟩ : ∃ b : ℕ, a = -(b : ℤ) := ⟨(-a).toNat, by omega⟩
    have hb : 1 ≤ b := by omega
    have h1 : ¬ (1 : ℤ) ≤ -(b : ℤ) := by omega
    have h2 : ¬ -(b : ℤ) = 0 := by omega
    have h : twBlock (-(b : ℤ)) = twistPolyNeg b := by
      rw [twBlock, ite_eq_right h1, ite_eq_right h2, neg_neg, Int.toNat_natCast]
    exact ⟨0, 8 * b - 2, by rw [h, (monic_twistPolyNeg b hb).leadingCoeff, pow_zero],
      by rw [h, coeff_zero_twistPolyNeg b hb]⟩
  · have h : twBlock 0 = 1 := by simp [twBlock]
    exact ⟨0, 0, by rw [h, leadingCoeff_one, pow_zero], by simp [h]⟩
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = (m : ℤ) := ⟨a.toNat, by omega⟩
    have h1 : (1 : ℤ) ≤ (m : ℤ) := by omega
    have h : twBlock (m : ℤ) = twistPoly m := by
      rw [twBlock, ite_eq_left h1, Int.toNat_natCast]
    exact ⟨4 * m, 4 * m, by rw [h, leadingCoeff_twistPoly], by rw [h, coeff_zero_twistPoly]⟩

/-- The second polynomial in `M` of the symbol identity does not vanish away from
`M² = ±1`. -/
private theorem eval_symbolRight_ne_zero_twSymbolEnds (d : ℕ) {m₀ : ℂ} (h1 : m₀ ^ 2 ≠ 1)
    (h2 : m₀ ^ 2 ≠ -1) :
    ((((-1) ^ (d + 1) * ((twDet d (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1))) :
      ℤ[X])).map (Int.castRingHom ℂ)).eval m₀ ≠ 0 := by
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_neg, Polynomial.map_one, Polynomial.map_comp, map_X, eval_mul, eval_pow,
    eval_sub, eval_add, eval_neg, eval_X, eval_one, eval_comp]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (mul_ne_zero (twDet_one_eval_ne_zero d h1 h2) (mul_ne_zero (pow_ne_zero _
      (fun h ↦ h2 (eq_neg_of_add_eq_zero_left h))) (sub_ne_zero.mpr h1)))

/-- Both endpoint coefficients of the symbol of `P_a` are nonzero at every `M = m₀` with
`m₀ ≠ 0`, `m₀² ≠ ± 1`. -/
theorem eval_coeff_specialize_twTransferOp_ne_zero (a : ℤ) {m₀ : ℂ} (h0 : m₀ ≠ 0)
    (h1 : m₀ ^ 2 ≠ 1) (h2 : m₀ ^ 2 ≠ -1) :
    ((specialize (twTransferOp a)).leadingCoeff.map (Int.castRingHom ℂ)).eval m₀ ≠ 0 ∧
      (((specialize (twTransferOp a)).coeff 0).map (Int.castRingHom ℂ)).eval m₀ ≠ 0 := by
  obtain ⟨j, k, hj, hk⟩ := twBlock_ends_twSymbolEnds a
  have hκ₂ := eval_symbolRight_ne_zero_twSymbolEnds (twWindow a) h1 h2
  have hmonic : (X - 1 : ℤ[X][X]).Monic := by simpa using monic_X_sub_C (1 : ℤ[X])
  have hE : extraFactor.coeff 0 = X ^ 4 := by
    simp only [extraFactor, coeff_add, coeff_sub, coeff_C_zero, coeff_X_pow, mul_coeff_zero,
      coeff_X_zero]
    simp
  have hX : (X - 1 : ℤ[X][X]).coeff 0 = -1 := by
    simp
  have hlead := congrArg leadingCoeff (specialize_twTransferOp_mul_eq a)
  have hconst := congrArg (fun p : ℤ[X][X] ↦ p.coeff 0) (specialize_twTransferOp_mul_eq a)
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_mul,
    leadingCoeff_mul, hmonic.leadingCoeff, extraFactor_monic.leadingCoeff, hj, one_mul,
    one_mul] at hlead
  simp only [mul_coeff_zero, coeff_C_zero, hE, hX, hk] at hconst
  exact ⟨eval_ne_zero_of_mul_eq_mul hlead hκ₂ (by simp [h0]),
    eval_ne_zero_of_mul_eq_mul hconst hκ₂ (by simp [h0])⟩

end AJConjecture
