import Mathlib
import AJFamily.Quantum.TorusFormula

/-!
# Odd colours on the integers

The odd colours of `T(2, a)` extended to `ℤ` by `u_(-n-1) = -u_n`, and the forcing term `h_a` of
their recurrence.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The odd colours extended to all integers by `u_(-n-1) = -u_n`. -/
def torusOddColorInt (a : ℕ) (n : ℤ) : RatFunc ℚ :=
  if 0 ≤ n then torusOddColor a n.toNat else -torusOddColor a (-n - 1).toNat

/-- The forcing term `h_a(q^n)`: `(t² - t⁻²) h_a = t^((8-4a)n+10-4a) - t^(-(4a+8)n-4a-10)
- t^((8-12a)n+6-12a) + t^(-(12a+8)n-12a-6)`. -/
def torusForcing (a : ℕ) (n : ℤ) : RatFunc ℚ :=
  (RatFunc.X ^ ((8 - 4 * (a : ℤ)) * n + 10 - 4 * a)
      - RatFunc.X ^ (-(4 * (a : ℤ) + 8) * n - 4 * a - 10)
      - RatFunc.X ^ ((8 - 12 * (a : ℤ)) * n + 6 - 12 * a)
      + RatFunc.X ^ (-(12 * (a : ℤ) + 8) * n - 12 * a - 6))
    / (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))

end AJConjecture
