import Mathlib
import AJFamily.VolumeDefs

/-!
# Evaluating the extra factor

`E(M, L) = L² - (M⁴ - 4M² + 1) L + M⁴` at a point of `ℂ²`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value of `E` at `(M, L)`. -/
theorem evalPoint_extraFactorℂ (p : ℂ × ℂ) :
    evalPoint extraFactorℂ p = p.2 ^ 2 - (p.1 ^ 4 - 4 * p.1 ^ 2 + 1) * p.2 + p.1 ^ 4 := by
  simp [extraFactorℂ, evalPoint, extraFactor, eval₂_pow]

end AJConjecture
