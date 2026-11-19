import Mathlib
import AJFamily.Quantum.FamTransferAtOne
import AJFamily.Quantum.TwistPoly

/-!
# The family target polynomial at `q = 1`

`famTarget_one_eq`: `famTarget m 1 = (1 - J)(ζ + 2x) · symbolTwist m`, by a homogenised Chebyshev
identity.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The Lucas-type sequence `L_0 = 2`, `L_1 = ζ`, `L_(k+2) = ζ L_(k+1) - x² L_k`. -/
private def lucasZetaAtOne : ℕ → ℤ[X][X]
  | 0 => 2
  | 1 => symbolZeta
  | k + 2 => symbolZeta * lucasZetaAtOne (k + 1) - C (X ^ 2) * lucasZetaAtOne k

/-- At `q = 1` the family Chebyshev operator `k` is multiplication by `L_k`. -/
private theorem famCheb_one_eq_lucasZetaAtOne (m : ℕ) :
    ∀ (k : ℕ) (n : ℤ[X][X]), famCheb m (1 : ℤ) k n = lucasZetaAtOne k * n
  | 0, n => by
    rw [famCheb, lucasZetaAtOne]
  | 1, n => by
    rw [famCheb, lucasZetaAtOne, famAdjoint_one_eq_mul]
  | k + 2, n => by
    rw [famCheb, lucasZetaAtOne, famAdjoint_one_eq_mul, famCheb_one_eq_lucasZetaAtOne m (k + 1),
      famCheb_one_eq_lucasZetaAtOne m k, one_pow, C_1, one_mul]
    ring

/-- The homogenised Chebyshev identity
`x² L_j + x (1 - J) L_(j+1) - J L_(j+2) = (1 - J)(ζ + 2x) T̂_(j+1)`. -/
private theorem lucasZetaAtOne_target_identity :
    ∀ j : ℕ, C (X ^ 2) * lucasZetaAtOne j + C X * ((1 - X) * lucasZetaAtOne (j + 1)) -
        X * lucasZetaAtOne (j + 2) =
      (1 - X) * (symbolZeta + C (2 * X)) * symbolTwist (j + 1)
  | 0 => by
    simp only [lucasZetaAtOne, symbolTwist, symbolZeta, C_add, C_pow, C_mul, C_ofNat]
    ring
  | 1 => by
    simp only [lucasZetaAtOne, symbolTwist, symbolZeta, C_add, C_pow, C_mul, C_ofNat]
    ring
  | j + 2 => by
    have h0 := lucasZetaAtOne_target_identity j
    have h1 := lucasZetaAtOne_target_identity (j + 1)
    rw [show symbolTwist (j + 2 + 1) =
        symbolZeta * symbolTwist (j + 1 + 1) - C (X ^ 2) * symbolTwist (j + 1) from rfl,
      show lucasZetaAtOne (j + 2 + 2) =
        symbolZeta * lucasZetaAtOne (j + 1 + 2) - C (X ^ 2) * lucasZetaAtOne (j + 2) from rfl,
      show lucasZetaAtOne (j + 2 + 1) =
        symbolZeta * lucasZetaAtOne (j + 1 + 1) - C (X ^ 2) * lucasZetaAtOne (j + 1) from rfl,
      show lucasZetaAtOne (j + 2) =
        symbolZeta * lucasZetaAtOne (j + 1) - C (X ^ 2) * lucasZetaAtOne j from rfl] at *
    linear_combination symbolZeta * h1 - C (X ^ 2) * h0

/-- At `q = 1` the family target polynomial is `(1 - J)(ζ + 2x) T̂_m`. -/
theorem famTarget_one_eq (m : ℕ) (hm : 1 ≤ m) :
    famTarget m (1 : ℤ) = (1 - X) * (symbolZeta + C (2 * X)) * symbolTwist m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [famTarget, famCheb_one_eq_lucasZetaAtOne, famCheb_one_eq_lucasZetaAtOne,
    famCheb_one_eq_lucasZetaAtOne, ← lucasZetaAtOne_target_identity j]
  simp only [one_pow, C_1, one_mul, mul_one, Nat.add_sub_cancel, C_pow]
  ring

end AJConjecture
