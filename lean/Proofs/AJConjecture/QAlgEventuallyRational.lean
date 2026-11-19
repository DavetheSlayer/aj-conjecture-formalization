import Mathlib
import AJConjecture.WhiteheadFormula

/-!
# Sequences that are eventually rational functions of `M = t^(2n)`

A sequence `g : ℤ → ℚ(t)` is eventually rational if `g(n) = a(t, t^(2n)) / b(t, t^(2n))` for
all large `n`, with `a, b ∈ ℤ[t][M]` and `b ≠ 0`. These are the germs at `+∞` of the scalar line
of the module of sequences over `ℚ(t, M)[L; σ]`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `g` is eventually a rational function of `M = t^(2n)`: `b(t, t^(2n)) g(n) = a(t, t^(2n))`
for all large `n`, with `b ≠ 0`. -/
def EventuallyRational (g : ℤ → RatFunc ℚ) : Prop :=
  ∃ a b : Coeff, b ≠ 0 ∧ ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → evalAtField n b * g n = evalAtField n a

end AJConjecture
