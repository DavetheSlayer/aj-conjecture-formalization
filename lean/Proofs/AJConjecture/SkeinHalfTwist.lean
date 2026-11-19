import Mathlib
import AJConjecture.ColoredJones
import AJConjecture.SkeinJonesWenzl
import AJConjecture.SkeinPartialTrace

/-!
# The cabled half twist and the kink of a bundle

Two adjacent bundles of `c` strands in `V^{⊗ 2c}`: the projector `f_c ⊗ f_c`, the cabled half
twist `Σ_c^{±1}` (the matrix of `AJConjecture.cableGen c (0, s)`, the crossing of the two bundles),
and the kink of a bundle without projector, the partial trace of the half twist over the second
bundle.
-/

noncomputable section

namespace AJConjecture

/-- The projector `f_c ⊗ f_c` on two bundles of `c` strands. -/
def twoBundleProj (c : ℕ) : SkMat (2 * c) (2 * c) :=
  jwAt (2 * c) 0 c * jwAt (2 * c) c c

/-- The cabled half twist `Σ_c^{±1}` of two bundles of `c` strands. -/
def halfTwist (c : ℕ) (s : Bool) : SkMat (2 * c) (2 * c) :=
  braidMatrix (2 * c) (cableGen c (0, s))

/-- The kink of a bundle of `c` strands, without projector: the partial trace of the cabled
half twist over the second bundle. -/
def kinkOp (c : ℕ) (s : Bool) : SkMat c c :=
  ptrTail c (2 * c) (halfTwist c s)

end AJConjecture
