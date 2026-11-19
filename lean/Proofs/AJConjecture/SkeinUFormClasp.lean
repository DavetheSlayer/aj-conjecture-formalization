import Mathlib
import AJConjecture.SkeinMorseWord

/-!
# The clasp of two bundles

The clasp `T_c` is the positive cabled full twist `Σ_c²` turned by a quarter: a thick cup on the
right, the full twist on the two middle bundles, a thick cap on the left. It is an operator on
two bundles of `c` strands, without projectors; for `c = 1` it is `(1 - t⁻⁴) + t² e`.
-/

noncomputable section

namespace AJConjecture

/-- The clasp `T_c` on two bundles of `c` strands: `(1 ⊗ 1 ⊗ cup_c)`, then `(1 ⊗ Σ_c² ⊗ 1)`, then
`(cap_c ⊗ 1 ⊗ 1)`, in the order of the matrix product. -/
def claspOp (c : ℕ) : SkMat (2 * c) (2 * c) :=
  skPlace (2 * c) (4 * c) (2 * c) (cupThick c) *
    skPlace (4 * c) (4 * c) c (halfTwist c true * halfTwist c true) *
      skPlace (4 * c) (2 * c) 0 (capThick c)

/-- The clasp as a Morse word on two strands. -/
def claspWord : MorseWord :=
  [(.cup, 2), (.cross true, 1), (.cross true, 1), (.cap, 0)]

end AJConjecture
