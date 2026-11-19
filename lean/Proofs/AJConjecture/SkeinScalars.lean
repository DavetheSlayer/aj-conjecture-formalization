import Mathlib
import AJConjecture.WhiteheadFormula

/-!
# The scalars of the Jones–Wenzl calculus

In `ℚ(t)`, with `[m] = quantumInt m`:

* `θ_k = (-1)^k t^(k(k+2))`, the positive kink on the Jones–Wenzl projector `f_k`;
* `Δ_k = (-1)^k [k+1]`, the closure of `f_k`.
-/

noncomputable section

namespace AJConjecture

/-- The kink scalar `θ_k = (-1)^k t^(k(k+2))`. -/
def kinkScalar (k : ℕ) : RatFunc ℚ :=
  (-1) ^ k * (RatFunc.X : RatFunc ℚ) ^ ((k : ℤ) * ((k : ℤ) + 2))

/-- The loop scalar `Δ_k = (-1)^k [k+1]`. -/
def loopScalar (k : ℕ) : RatFunc ℚ :=
  (-1) ^ k * quantumInt ((k : ℤ) + 1)

end AJConjecture
