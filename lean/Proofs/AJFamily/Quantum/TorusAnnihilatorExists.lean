import Mathlib
import AJConjecture.QAlgGaugeToUnreduced
import AJConjecture.QAlgKillFiniteDefect
import AJConjecture.QAlgTwoSidedAnnihilator
import AJFamily.Quantum.TorusTailAnnihilatorExists

/-!
# The torus formula has a nonzero annihilator

For `a ≥ 3`, `torusWhiteheadFormula a` has a nonzero annihilator, obtained from a tail annihilator
of the even reduced formula and gauged by `[n]`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The torus closed formula `[n] F_|n|` is annihilated by a nonzero recurrence operator. -/
theorem exists_annihilator_torusWhiteheadFormula (a : ℕ) (ha : 3 ≤ a) :
    ∃ Q : RecOp, Q ≠ 0 ∧ ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (torusWhiteheadFormula a) n = 0 := by
  obtain ⟨G, hG, hGann⟩ := exists_tail_annihilator_torusReducedFormulaEven a (by omega)
  obtain ⟨Q₀, hQ₀, N, hN⟩ :=
    exists_annihilator_outside_finite_of_even (torusReducedFormulaEven_neg a) hG hGann
  obtain ⟨c, hc, hc0⟩ := exists_C_mul_annihilator_of_outside_finite hN
  obtain ⟨Q, hQ, hQann⟩ := exists_gauge_quantumInt_mul (Polynomial.C c * Q₀)
  have hne : Polynomial.C c * Q₀ ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hQ₀
  have hfun : torusWhiteheadFormula a = fun m ↦ quantumInt m * torusReducedFormulaEven a m :=
    funext (torusWhiteheadFormula_eq_quantumInt_mul a)
  refine ⟨Q, hQ hne, 1, one_ne_zero, fun n ↦ ?_⟩
  rw [Polynomial.C_1, one_mul, hfun]
  exact hQann (torusReducedFormulaEven a) n (hc0 n)

end AJConjecture
