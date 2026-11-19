import Mathlib
import AJConjecture.SkeinChebyshevProjector
import AJConjecture.SkeinColorReduction
import AJFamily.Skein.TorusColorReduction
import AJFamily.Skein.TorusKnotTrace
import AJFamily.Skein.TorusWordWrithe

/-!
# The sequence identity

`laurentToField_coloredJones_whiteheadTorusKnot`: the coloured Jones function of
`whiteheadTorusKnot k` is `torusWhiteheadFormula (2k+1)` at every integer colour. At positive
colours the coloured bracket of `TorusKnotTrace` is corrected by the framing factor of writhe `4k`;
the other colours follow by `laurentToField_coloredJones_of_pos_torus`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

theorem laurentToField_coloredJones_whiteheadTorusKnot (k : ℕ) (hk : 1 ≤ k) (n : ℤ) :
    laurentToField (coloredJones (whiteheadTorusKnot k hk) n) = torusWhiteheadFormula (2 * k + 1) n := by
  refine laurentToField_coloredJones_of_pos_torus (whiteheadTorusKnot k hk) (2 * k + 1)
    (fun c ↦ ?_) n
  rw [laurentToField_coloredJonesPos, knotTrace_whiteheadTorusKnot_jwAt k hk c]
  have hw : writhe (whiteheadTorusKnot k hk).word = 4 * k := writhe_whiteheadTorusWord k hk
  rw [hw]
  have hθ : kinkScalar c ≠ 0 := kinkScalar_ne_zero c
  have h1 : ((-1 : RatFunc ℚ) ^ c) * (-1) ^ c = 1 := by
    rw [← mul_pow]
    norm_num
  have h2 : kinkScalar c ^ (-((4 * k : ℕ) : ℤ)) * kinkScalar c ^ (4 * k) = 1 := by
    rw [← zpow_natCast (kinkScalar c) (4 * k), ← zpow_add₀ hθ]
    norm_num
  push_cast at h2 ⊢
  calc (-1 : RatFunc ℚ) ^ c * kinkScalar c ^ (-(4 * (k : ℤ))) *
        ((-1) ^ c * kinkScalar c ^ (4 * k) * torusWhiteheadFormula (2 * k + 1) ((c : ℤ) + 1))
      = ((-1 : RatFunc ℚ) ^ c * (-1) ^ c) *
          (kinkScalar c ^ (-(4 * (k : ℤ))) * kinkScalar c ^ (4 * k)) *
          torusWhiteheadFormula (2 * k + 1) ((c : ℤ) + 1) := by ring
    _ = torusWhiteheadFormula (2 * k + 1) ((c : ℤ) + 1) := by rw [h1, h2, one_mul, one_mul]

end AJConjecture
