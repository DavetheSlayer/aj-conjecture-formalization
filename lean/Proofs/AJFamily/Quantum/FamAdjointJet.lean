import Mathlib
import AJConjecture.QAlgCompScaleNilpotent
import AJConjecture.QAlgTransferAdjointJet
import AJFamily.Quantum.FamJetData
import AJFamily.Quantum.FamTransferPoly

/-!
# The family adjoint to first order

If `(1 - q)² = 0`, `famAdjoint` is a first-order differential operator in `J`. This starts the jet
computations at `q = 1 - 4ε`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- If `(1 - q)² = 0`, then `famAdjoint m q n = ζ n + (1 - q) A ∂_J n`. -/
theorem famAdjoint_eq_of_sq_eq_zero {R : Type*} [CommRing R] {q : R} (hq : (1 - q) ^ 2 = 0)
    (m : ℕ) (n : R[X][X]) :
    famAdjoint m q n = famJetZeta m (C (C q)) (C X) X * n +
      C (C (1 - q)) * famJetCubic m (C (C q)) (C X) X * derivative n := by
  have hq' : ((1 : R[X]) - C q) ^ 2 = 0 := by
    rw [show (1 : R[X]) - C q = C (1 - q) by simp, ← C_pow, hq, C_0]
  have hinner : C (C (q ^ (2 * m + 2)) * X) * n -
      (1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ (2 * m + 2))) - C X * X) *
        n.comp (C (C q) * X) =
      X * ((famJetZeta m (C (C q)) (C X) X - C (C (q ^ (2 * m + 3)) * X) * X) * n +
        C (C (1 - q)) * famJetCubic m (C (C q)) (C X) X * derivative n) := by
    rw [comp_C_mul_X_of_sq_eq_zero hq', famJetZeta, famJetCubic]
    simp only [C_mul, C_pow, C_sub, C_1]
    ring
  rw [famAdjoint, hinner, divX_X_mul_jet]
  ring

end AJConjecture
