import Mathlib
import AJFamily.Quantum.FamTransferPoly

/-!
# Cramer coefficients of the family transfer operator

The coefficients of `famTransferOp m`, defined by Cramer's rule without division from the basis
polynomials and the target polynomial.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The coefficient matrix of the family basis polynomials in the monomial basis of `J`. -/
def famMatrix {R : Type*} [CommRing R] (m : ℕ) (q : R) :
    Matrix (Fin (2 * m + 4)) (Fin (2 * m + 4)) R[X] :=
  Matrix.of fun k i ↦ (famBasisPoly m q i).coeff k

/-- The determinant of `famMatrix`. -/
def famDet {R : Type*} [CommRing R] (m : ℕ) (q : R) : R[X] :=
  (famMatrix m q).det

/-- The Cramer numerators of `famMatrix` for the coefficients of `famTarget`. -/
def famCoeff {R : Type*} [CommRing R] (m : ℕ) (q : R) (i : Fin (2 * m + 4)) : R[X] :=
  Matrix.cramer (famMatrix m q) (fun k ↦ (famTarget m q).coeff k) i

end AJConjecture
