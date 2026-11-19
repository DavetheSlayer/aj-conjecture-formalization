import Mathlib
import AJConjecture.SkeinBandClasp
import AJConjecture.SkeinUFormClasp

/-!
# The two definitions of the clasp agree

`AJConjecture.bandClaspOp` (the rotation `AJConjecture.bandRot` of the positive cabled full twist,
used in the evaluation of the band-and-clasp diagram) and `AJConjecture.claspOp` (the clasp of
the Morse-word calculus) are the same matrix by definition.
-/

namespace AJConjecture

/-- The clasp of the satellite evaluation is the clasp of the Morse-word calculus. -/
theorem bandClaspOp_eq_claspOp (c : ℕ) : bandClaspOp c = claspOp c :=
  rfl

end AJConjecture
