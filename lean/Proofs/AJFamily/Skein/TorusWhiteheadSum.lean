import Mathlib
import AJConjecture.ClaspAlgClaspEigenCoeff
import AJFamily.Skein.TorusReducedFormulaSum

/-!
# The clasp-eigenvalue sum

`claspAlg_sum_claspEigen_mul_torusOddColor`: the sum over the channels of the clasp eigenvalues
times the odd colours of `T(2, a)`, with its framing factor, is `torusWhiteheadFormula a (c+1)`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The evaluation of the band-and-clasp diagram at the colour `c + 1`, in terms of the clasp
eigenvalues and the odd colours of the torus knot, is the unreduced formula. -/
theorem claspAlg_sum_claspEigen_mul_torusOddColor (a c : ℕ) :
    (-1) ^ c * (RatFunc.X : RatFunc ℚ) ^ (2 * (c : ℤ) * ((c : ℤ) + 2)) *
        ∑ n ∈ Finset.range (c + 1), claspAlgClaspEigen c n * torusOddColor a n =
      torusWhiteheadFormula a ((c : ℤ) + 1) := by
  have hpos : (0 : ℤ) < (c : ℤ) + 1 := by omega
  have htoNat : ((c : ℤ) + 1).toNat = c + 1 := by omega
  have hcast : (((c + 1 : ℕ) : ℤ)) = (c : ℤ) + 1 := by push_cast; ring
  rw [torusWhiteheadFormula, ite_eq_left hpos, htoNat, ← hcast,
    claspAlg_quantumInt_mul_torusReducedFormula, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [← claspAlgClaspEigen_eq_claspAlgCoeff c n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
  ring

end AJConjecture
