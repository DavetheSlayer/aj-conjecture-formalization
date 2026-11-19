import Mathlib
import AJFamily.Quantum.TorusFormula

/-!
# Even form of the torus reduced formula

The even extension `F_|n|` of the reduced formula, and `torusWhiteheadFormula a n = [n] F_|n|`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The even extension `n ↦ F_|n|` of the family's reduced formula. -/
def torusReducedFormulaEven (a : ℕ) (n : ℤ) : RatFunc ℚ :=
  torusReducedFormula a n.natAbs

/-- The even extension is even. -/
theorem torusReducedFormulaEven_neg (a : ℕ) (n : ℤ) :
    torusReducedFormulaEven a (-n) = torusReducedFormulaEven a n := by
  rw [torusReducedFormulaEven, torusReducedFormulaEven, Int.natAbs_neg]

/-- `torusWhiteheadFormula a n = [n] F_|n|`. -/
theorem torusWhiteheadFormula_eq_quantumInt_mul (a : ℕ) (n : ℤ) :
    torusWhiteheadFormula a n = quantumInt n * torusReducedFormulaEven a n := by
  have hneg : quantumInt (-n) = -quantumInt n := by
    simp only [quantumInt, mul_neg, neg_neg]
    ring
  rcases lt_trichotomy 0 n with hn | hn | hn
  · have h1 : n.toNat = n.natAbs := by omega
    rw [torusWhiteheadFormula, ite_eq_left hn, torusReducedFormulaEven, h1]
  · subst hn
    have h0 : quantumInt 0 = 0 := by simp [quantumInt]
    rw [torusWhiteheadFormula, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), h0,
      zero_mul]
  · have h1 : (-n).toNat = n.natAbs := by omega
    rw [torusWhiteheadFormula, ite_eq_right (by omega), ite_eq_left hn, torusReducedFormulaEven,
      h1, hneg]
    ring

end AJConjecture
