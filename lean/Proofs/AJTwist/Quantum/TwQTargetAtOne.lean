import Mathlib
import AJTwist.Quantum.TwQTarget
import AJTwist.Quantum.TwQTwistPolyNeg
import AJFamily.Quantum.FamTargetAtOne

/-!
# The cleared numerators at `q = 1` (Unit Q3)

Source: revision 5, Section 3.4, eq. (commonPi):
`Π_a = S_(a-1)(Z) + (1 - J) S_a(Z) - J S_(a+1)(Z) = (1 - J)(Z + 2) T_a` for every integer `a`
("Both sides obey the same invertible trace recurrence in `a`. At `a = 0, 1` equality follows
from `S_(-1) = Z` and `(J - 1) e = Z - 2`").

At `q = 1` the cleared adjoint `twAdjoint d 1` is multiplication by `ζ = x Z = symbolZeta` for
every window, and the trace polynomials are multiplication by the Lucas sequence
`twLucasZeta k = x^k S_k(Z)`. Hence, with `ζ + 2x = x (Z + 2)`:

* `twZeroTarget_one_eq`: `twTarget 0 1 = (1 - J)(ζ + 2x)`;
* `twNegTarget_one_eq`: `twTarget (-b) 1 = (1 - J)(ζ + 2x) T̂_(-b)`, `T̂_(-b) = symbolTwistNeg b`;
* for `a = m ≥ 1` the library has `famTarget_one_eq`: `famTarget m 1 = (1 - J)(ζ + 2x) T̂_m`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The Lucas sequence `L_0 = 2`, `L_1 = ζ`, `L_(k+2) = ζ L_(k+1) - x² L_k`: `L_k = x^k S_k(Z)` at
`q = 1`. -/
def twLucasZeta : ℕ → ℤ[X][X]
  | 0 => 2
  | 1 => symbolZeta
  | k + 2 => symbolZeta * twLucasZeta (k + 1) - C (X ^ 2) * twLucasZeta k

/-- Division by `X` undoes multiplication by `X` on the left. -/
private theorem divX_X_mul_targetAtOne {A : Type*} [Semiring A] (p : A[X]) :
    divX (X * p) = p := by
  ext k
  rw [coeff_divX, coeff_X_mul]

/-- At `q = 1` the cleared adjoint of every window is multiplication by `ζ`. -/
theorem twAdjoint_one_eq_mul (d : ℕ) (n : ℤ[X][X]) : twAdjoint d (1 : ℤ) n = symbolZeta * n := by
  have hinner : C (C ((1 : ℤ) ^ (d - 1)) * X) * n -
      (1 - C (C (1 : ℤ)) * X) * (C X - C (C (1 : ℤ)) * X) *
        (C (C ((1 : ℤ) ^ (d - 1))) - C X * X) * n.comp (C (C (1 : ℤ)) * X) =
      X * ((C (X ^ 2 + X + 1) - C (X ^ 2 + X + 1) * X + C X * X ^ 2) * n) := by
    simp only [one_pow, C_1, one_mul, comp_X, C_add, C_pow]
    ring
  rw [twAdjoint, hinner, divX_X_mul_targetAtOne, symbolZeta]
  simp only [one_pow, C_1, one_mul, C_add, C_pow]
  ring

/-- At `q = 1` the `k`-th adjoint trace polynomial is multiplication by `L_k`. -/
theorem twCheb_one_eq_mul (d k : ℕ) (n : ℤ[X][X]) :
    twCheb d (1 : ℤ) k n = twLucasZeta k * n := by
  induction k using Nat.twoStepInduction generalizing n with
  | zero => rw [twCheb, twLucasZeta]
  | one => rw [twCheb, twLucasZeta, twAdjoint_one_eq_mul]
  | more k ih0 ih1 =>
    rw [twCheb, twLucasZeta, twAdjoint_one_eq_mul, ih1, ih0, one_pow, C_1, one_mul]
    ring

/-- The homogenised trace identity of negative index:
`L_(b+1) + x (1 - J) L_b - x² J L_(b-1) = (1 - J)(ζ + 2x) T̂_(-b)` for `b ≥ 1`. -/
theorem twLucasZeta_neg_target_identity (b : ℕ) :
    twLucasZeta (b + 2) + C X * ((1 - X) * twLucasZeta (b + 1)) - C (X ^ 2) * (X * twLucasZeta b) =
      (1 - X) * (symbolZeta + C (2 * X)) * symbolTwistNeg (b + 1) := by
  induction b using Nat.twoStepInduction with
  | zero =>
    simp only [twLucasZeta, symbolTwistNeg, symbolZeta, C_add, C_pow, C_mul, C_ofNat, C_1]
    ring
  | one =>
    simp only [twLucasZeta, symbolTwistNeg, symbolZeta, C_add, C_pow, C_mul, C_ofNat, C_1]
    ring
  | more j h0 h1 =>
    rw [show symbolTwistNeg (j + 2 + 1) =
        symbolZeta * symbolTwistNeg (j + 1 + 1) - C (X ^ 2) * symbolTwistNeg (j + 1) from rfl,
      show twLucasZeta (j + 2 + 2) =
        symbolZeta * twLucasZeta (j + 1 + 2) - C (X ^ 2) * twLucasZeta (j + 2) from rfl,
      show twLucasZeta (j + 2 + 1) =
        symbolZeta * twLucasZeta (j + 1 + 1) - C (X ^ 2) * twLucasZeta (j + 1) from rfl,
      show twLucasZeta (j + 2) =
        symbolZeta * twLucasZeta (j + 1) - C (X ^ 2) * twLucasZeta j from rfl] at *
    linear_combination symbolZeta * h1 - C (X ^ 2) * h0

/-- At `q = 1` the cleared numerator of `a = 0` is `(1 - J)(ζ + 2x)`. -/
theorem twZeroTarget_one_eq : twZeroTarget (1 : ℤ) = (1 - X) * (symbolZeta + C (2 * X)) := by
  rw [twZeroTarget, twAdjoint_one_eq_mul]
  simp only [one_pow, C_1, one_mul, C_mul, C_ofNat]
  ring

/-- At `q = 1` the cleared numerator of `a = -b < 0` is `(1 - J)(ζ + 2x) T̂_(-b)`. -/
theorem twNegTarget_one_eq (b : ℕ) (hb : 1 ≤ b) :
    twNegTarget b (1 : ℤ) = (1 - X) * (symbolZeta + C (2 * X)) * symbolTwistNeg b := by
  obtain ⟨j, rfl⟩ : ∃ j, b = j + 1 := ⟨b - 1, by omega⟩
  rw [twNegTarget, twCheb_one_eq_mul, twCheb_one_eq_mul, twCheb_one_eq_mul,
    ← twLucasZeta_neg_target_identity j]
  simp only [one_pow, C_1, one_mul, mul_one, Nat.add_sub_cancel, C_pow]
  ring

end AJConjecture
