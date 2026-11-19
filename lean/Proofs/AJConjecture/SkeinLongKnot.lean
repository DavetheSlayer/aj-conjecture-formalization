import Mathlib
import AJConjecture.ColoredJones
import AJConjecture.SkeinPartialTrace
import AJConjecture.SkeinPlace

/-!
# The long knot and the knot trace

For a closed braid `K` and a thickness `k`, the blackboard `k`-cable of `K` cut open in the
first column is the operator `Λ_K(k) = ptr(ρ(cable k w))` on `V^{⊗ k}` (all bundles but the first
are closed), and `Tr_{K,k}(Y) = qtr(ρ(cable k w) (Y ⊗ 1))` inserts an operator `Y` on the first
bundle before closing. The knot trace is a trace on the Temperley–Lieb category
(`AJConjecture.capAt_mul_longKnotOp`), which is the content of "the skein of the solid torus
acts on the knot".
-/

noncomputable section

namespace AJConjecture

/-- The knot trace: the cabled closed braid with an operator `Y` inserted on the first bundle. -/
def knotTrace (K : BraidKnot) (k : ℕ) (Y : SkMat k k) : RatFunc ℚ :=
  qtr (k * K.strands)
    (braidMatrix (k * K.strands) (cable k K.word) * skPlace (k * K.strands) (k * K.strands) 0 Y)

/-- The long knot: the cabled braid with all bundles closed except the first. -/
def longKnotOp (K : BraidKnot) (k : ℕ) : SkMat k k :=
  ptrTail k (k * K.strands) (braidMatrix (k * K.strands) (cable k K.word))

end AJConjecture
