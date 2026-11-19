import Mathlib
import AJConjecture.QAlgGaugeOpSpecialize
import AJConjecture.QAlgSpecializeDvdOfOreMul
import AJFamily.Quantum.TorusTailAnnihilatorFactor
import AJFamily.Quantum.TorusTailAnnihilatorGauge

/-!
# The extra factor divides every primitive annihilator

For `a ≥ 3`, `E` divides the `t = -1` specialisation of every primitive annihilator of
`torusWhiteheadFormula a`: after gauging, such an operator is a left multiple of
`famTransferOp (2a)` up to a scalar.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

theorem extraFactor_dvd_specialize_of_annihilates_torusWhiteheadFormula (a : ℕ) (ha : 3 ≤ a)
    {Q : RecOp} (hQ : Q.IsPrimitive)
    (hann : ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (torusWhiteheadFormula a) n = 0) :
    toComparison extraFactor ∣ toComparison (specialize Q) := by
  obtain ⟨n₁, hn₁⟩ := exists_tail_annihilator_gaugeOp_torus a hann
  obtain ⟨β, hβ, T, hT⟩ :=
    exists_C_mul_eq_oreMul_famTransferOp_of_tail_annihilator a (by omega) hn₁
  have hX : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
    intro h0
    have h1 := congrArg (Polynomial.eval 0) h0
    norm_num at h1
  have hm : 1 ≤ 2 * a := by omega
  have hspec : specialize (gaugeOp Q) ≠ 0 := by
    rw [specialize_gaugeOp]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hX) (specialize_ne_zero_of_isPrimitive hQ)
  have h1 : toComparison (specialize (famTransferOp (2 * a))) ∣
      toComparison (specialize (gaugeOp Q)) :=
    toComparison_specialize_dvd_of_oreMul hβ hT hspec (specialize_famTransferOp_ne_zero _ hm)
  have h2 := (extraFactor_dvd_specialize_famTransferOp _ hm).trans h1
  rw [specialize_gaugeOp, map_mul] at h2
  exact (isUnit_toComparison_coeff_of_ne_zero hX).dvd_mul_left.mp h2

end AJConjecture
