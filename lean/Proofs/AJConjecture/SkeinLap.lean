import Mathlib
import AJConjecture.SkeinPlace
import AJConjecture.SkeinThickCable

/-!
# The laps of a cap around a closed braid

Bookkeeping for the proof that a cap can be pushed once around a cabled knot. A strand of the
closed braid of `w` that is in the column `x` at the top is in the column `strandEnd w.reverse x`
at the bottom, where it re-enters the braid from the top after one more turn around the
closure. `lapCol w ℓ` is the column in which the cap sits at the top of the braid after `ℓ` laps,
starting from the column `0`. After `ℓ` laps the part of the strand already passed by the cap is
thinner by two: `lapProfile w k ℓ` has `k` strands in the columns `lapCol w 1, …, lapCol w ℓ` and
`k + 2` strands elsewhere. `lapTrace K k j G ℓ M` is the diagram after `ℓ` laps: the cable with
this profile at the bottom, the cap on the strands `j`, `j + 1` of the column `lapCol w ℓ` at the
top, followed by `G` on the column `0`, on `M + 2` strands in total.
-/

noncomputable section

namespace AJConjecture

/-- The column of the cap at the top of the braid after `ℓ` laps, starting from the column `0`. -/
def lapCol (w : BraidWord) (ℓ : ℕ) : ℕ :=
  (strandEnd w.reverse)^[ℓ] 0

/-- The thickness profile at the bottom of the braid after `ℓ` laps of a cap that removes two
strands from a bundle of `k + 2` strands. -/
def lapProfile (w : BraidWord) (k ℓ : ℕ) : ℕ → ℕ :=
  fun x ↦ if x ∈ (Finset.Icc 1 ℓ).image (lapCol w) then k else k + 2

/-- The quantum trace of the diagram after `ℓ` laps, on `M + 2` strands: the cable with the
profile `lapProfile K.word k ℓ`, the cap on the strands `j`, `j + 1` of the column
`lapCol K.word ℓ` at the top, and the matrix `G` on the column `0`. -/
def lapTrace (K : BraidKnot) (k j : ℕ) (G : SkMat k (k + 2)) (ℓ M : ℕ) : RatFunc ℚ :=
  qtr (M + 2) (braidMatrix (M + 2) (thickCable (lapProfile K.word k ℓ) K.word) *
    capAt M
      (profileOffset (profileEnd (lapProfile K.word k (ℓ + 1)) K.word) (lapCol K.word ℓ) + j) *
    skPlace M (M + 2) 0 G)

end AJConjecture
