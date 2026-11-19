import Mathlib
import AJConjecture.SkeinBandClasp
import AJConjecture.SkeinLongKnot
import AJFamily.Skein.TorusKnot

/-!
# The satellite bracket

`torusSatelliteTrace k c`: the bracket at colour `c` of the band-and-clasp diagram of
`Wh⁻₀(T(2, 2k+1))`, written as a trace of the `2c`-cable of `T(2, 2k+1)`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The bracket of the band-and-clasp diagram of `Wh⁻₀(T(2, 2k+1))`: the `2c`-cable of
`σ_0^(2k+1)` with `(f ⊗ f) Σ_c^(-2(2k+1)) T_c (f ⊗ f)` on its first column. -/
def torusSatelliteTrace (k c : ℕ) : RatFunc ℚ :=
  knotTrace (torusKnot k) (2 * c)
    (twoBundleProj c * halfTwist c false ^ (2 * (2 * k + 1)) * bandClaspOp c * twoBundleProj c)

end AJConjecture
