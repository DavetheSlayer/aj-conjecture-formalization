import Mathlib
import AJConjecture.SkeinHalfTwist
import AJConjecture.SkeinPlace

/-!
# The band-and-clasp form of the Whitehead double

The clasp of a Whitehead double as an operator on two bundles of `c` strands (the two edges of
the companion band).

* `bandRot c X` is the quarter-turn rotation of an operator `X` on two bundles: a nest of `c`
  cups creates two new bundles on the right, `X` acts on the second and the third bundle, and
  a nest of `c` caps closes the first and the second.
* `bandClaspOp c` is the clasp: the rotation of the positive full twist `Σ_c²`. The two bundles
  are turned back at the top and at the bottom, and the two turn-backs are hooked into each
  other. For `c = 1` it is `(1 - t⁻⁴) · 1 + t² · e`.
-/

noncomputable section

namespace AJConjecture

/-- The quarter-turn rotation of an operator on two bundles of `c` strands. -/
def bandRot (c : ℕ) (X : SkMat (2 * c) (2 * c)) : SkMat (2 * c) (2 * c) :=
  skPlace (2 * c) (4 * c) (2 * c) (cupThick c) * skPlace (4 * c) (4 * c) c X *
    skPlace (4 * c) (2 * c) 0 (capThick c)

/-- The clasp of two bundles of `c` strands: the rotation of the positive cabled full twist. -/
def bandClaspOp (c : ℕ) : SkMat (2 * c) (2 * c) :=
  bandRot c (halfTwist c true * halfTwist c true)

end AJConjecture
