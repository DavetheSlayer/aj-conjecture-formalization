import Mathlib
import AJTwist.Quantum.TwQSymbolFacts
import AJTwist.Classical.TwCCoprime

/-!
# The whole symbol `(L - 1) E 𝒫_a` of the transfer operator (Unit PpS, node `PpS_Symbol`)

Source: Section 3.4 of the paper (`transfer.tex`, the table after eq. (B)) and Section 8.4
(`conclusion.tex`): "the Gauss specialization then gives `(L - 1) E 𝒫_a ∣ f_S`, by the symbol
calculation".

* `ppsSymbol a = (L - 1) E 𝒫_a` in `ℤ[M][L]`, with `𝒫_a = twP a` (`B_a`, `1`, `C_(-a)`).
* `twBlock_eq_twP`: the varying block of the library's symbol theorem is `𝒫_a`.
* `pps_specialize_twTransferOp_associated`: in `R = ℚ(M)[L, L⁻¹]` the specialization of the
  transfer operator `P_a` is associated to `(L - 1) E 𝒫_a` (the library's
  `specialize_twTransferOp_mul_eq` with its two polynomials in `M` made units).
* `pps_symbol_zero_dvd`: at index `0` the symbol is `(L - 1) E`; it divides whatever `L - 1` and
  `E` both divide (they are coprime in `R`). This is the glue for the case `a = 0`, where the
  factor `L - 1` comes from the package `AJPaper/Divisor`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The whole symbol `(L - 1) E 𝒫_a` of the transfer operator `P_a`, in `ℤ[M][L]`. -/
def ppsSymbol (a : ℤ) : ℤ[X][X] :=
  (X - 1) * extraFactor * twP a

/-- The varying block of `specialize_twTransferOp_mul_eq` is the filling polynomial `𝒫_a`. -/
theorem twBlock_eq_twP (a : ℤ) : twBlock a = twP a := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have h1 : ¬ (1 : ℤ) ≤ a := by omega
    have h2 : ¬ a = 0 := by omega
    have h3 : ¬ (0 : ℤ) ≤ a := by omega
    rw [twBlock, twP, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
  · rw [twP_zero]
    simp [twBlock]
  · have h1 : (1 : ℤ) ≤ a := by omega
    have h3 : (0 : ℤ) ≤ a := by omega
    rw [twBlock, twP, ite_eq_left h1, ite_eq_left h3]

/-- The symbol of `P_a` is `(L - 1) E 𝒫_a` up to a unit of `ℚ(M)[L, L⁻¹]`. -/
theorem pps_specialize_twTransferOp_associated (a : ℤ) :
    Associated (toComparison (specialize (twTransferOp a))) (toComparison (ppsSymbol a)) := by
  have h := specialize_twTransferOp_mul_eq a
  rw [twBlock_eq_twP, ← ppsSymbol] at h
  have h2 : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := fun h0 ↦ by
    simpa using congrArg (Polynomial.eval 0) h0
  have h4 : (X ^ 4 - 1 : ℤ[X]) ≠ 0 := fun h0 ↦ by
    simpa using congrArg (Polynomial.eval 0) h0
  have hl : ((X ^ 2 - 1) ^ twWindow a * (X ^ 4 - 1) ^ twWindow a : ℤ[X]) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h4)
  have hr : ((-1) ^ (twWindow a + 1) * ((twDet (twWindow a) (1 : ℤ)).comp (X ^ 2) *
      ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1))) : ℤ[X]) ≠ 0 := fun h0 ↦ by
    rw [h0, C_0, zero_mul] at h
    exact (mul_ne_zero (C_ne_zero.mpr hl) (specialize_twTransferOp_ne_zero a)) h
  rw [← associated_isUnit_mul_left_iff (isUnit_toComparison_coeff_of_ne_zero hl),
    ← associated_isUnit_mul_right_iff (isUnit_toComparison_coeff_of_ne_zero hr),
    ← map_mul, ← map_mul, h]
  exact Associated.refl _

/-- At index `0` the symbol `(L - 1) E` divides every element of `ℚ(M)[L, L⁻¹]` divisible by
`L - 1` and by `E`. -/
theorem pps_symbol_zero_dvd {F : ComparisonRing} (h1 : toComparison (X - 1) ∣ F)
    (hE : toComparison extraFactor ∣ F) : toComparison (ppsSymbol 0) ∣ F := by
  have hc := isCoprime_extraFactor_twBound 0 0
  rw [twBound, twP_zero, mul_one, mul_one] at hc
  rw [ppsSymbol, twP_zero, mul_one, map_mul]
  exact hc.symm.mul_dvd h1 hE

end AJConjecture
