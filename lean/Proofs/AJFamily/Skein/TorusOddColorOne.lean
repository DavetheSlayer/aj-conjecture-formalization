import Mathlib
import AJConjecture.ClaspAlgBasic
import AJFamily.Quantum.TorusFormula

/-!
# The first odd colour of `T(2, a)`

`torusOddColor_one`: the closed form of the first odd colour `u_1` of `T(2, a)`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- `[1] = 1`. -/
theorem quantumInt_one : quantumInt 1 = 1 := by
  rw [quantumInt, mul_one]
  exact div_self claspAlg_ratFuncX_sq_sub_ne_zero

/-- The first odd colour of `T(2, a)`: `u_1 = q^(-4a) (1 - q^a [3] + q^(3a) [5])`. -/
theorem torusOddColor_one (a : ℕ) :
    torusOddColor a 1 =
      qParam ^ (-(4 * (a : ℤ))) *
        (1 - qParam ^ (a : ℤ) * quantumInt 3 + qParam ^ (3 * (a : ℤ)) * quantumInt 5) := by
  have hIcc : Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
  rw [torusOddColor, hIcc, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have h3 : (4 * (-1 : ℤ) + 1) = -3 := by norm_num
  rw [h3, claspAlg_quantumInt_neg]
  norm_num [quantumInt_one]
  ring_nf

end AJConjecture
