import Mathlib
import AJFamily.Skein.TorusBridge
import AJFamily.Skein.TorusLongKnot
import AJFamily.Skein.TorusSatelliteEval

/-!
# The coloured bracket of the family knots

`knotTrace_whiteheadTorusKnot_jwAt`: the bracket of `whiteheadTorusKnot k` coloured by the
projector `f_c` is `(-1)^c θ_c^(4k) · torusWhiteheadFormula (2k+1) (c+1)`. It combines the isotopy
(`longKnotOp_whiteheadTorusKnot`) with the evaluation of the satellite diagram
(`torusSatelliteTrace_eq`).
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

theorem knotTrace_whiteheadTorusKnot_jwAt (k : ℕ) (hk : 1 ≤ k) (c : ℕ) :
    knotTrace (whiteheadTorusKnot k hk) c (jwAt c 0 c) =
      (-1) ^ c * kinkScalar c ^ (4 * k) * torusWhiteheadFormula (2 * k + 1) ((c : ℤ) + 1) := by
  rw [knotTrace_jwAt_of_longKnotOp_torus _ k c (longKnotOp_whiteheadTorusKnot k hk c),
    torusSatelliteTrace_eq]

end AJConjecture
