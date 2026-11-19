import Mathlib
import AJConjecture.BraidKnot

/-!
# The family braid word

`whiteheadTorusWord k`: a braid word on `4k + 3` strands with `20k + 4` crossings, whose closure is
the untwisted negative-clasp Whitehead double `Wh⁻₀(T(2, 2k+1))`. It is the boundary of a braided
surface: an annulus around `T(2, 2k+1)` made of bands `surfaceBand i j`, plumbed with a negative
Hopf band on the top level.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The band `b(i, j) = σ_{j-1} ⋯ σ_{i+1} σ_i σ_{i+1}⁻¹ ⋯ σ_{j-1}⁻¹` (`i < j`) of a braided
surface: a positive half-twisted band between the levels `i` and `j`, passing in front of the
levels in between. -/
def surfaceBand (i j : ℕ) : BraidWord :=
  ((List.range (j - i - 1)).map fun x ↦ (j - 1 - x, true)) ++ [(i, true)] ++
    ((List.range (j - i - 1)).map fun x ↦ (i + 1 + x, false))

/-- The braid word of `Wh⁻₀(T(2, 2k+1))` on `4k + 3` strands (`a = 2k + 1`): the small climbs
`b(l, l+1)`, `l < a - 2`; the big climb `b(a-2, 2a-2)`; the first staircase step `b(2a-3, 2a-1)`
followed by the first Hopf band `σ_{2a-1}⁻¹`; the staircase steps `b(2a-4-s, 2a-2-s)`,
`s < a - 2`; the last crossing `b(0, a)`; the final climb `b(a-1, 2a-1)`; the second Hopf band. -/
def whiteheadTorusWord (k : ℕ) : BraidWord :=
  (List.range (2 * k - 1)).map (fun l ↦ (l, true)) ++
    surfaceBand (2 * k - 1) (4 * k) ++
    surfaceBand (4 * k - 1) (4 * k + 1) ++ [(4 * k + 1, false)] ++
    (List.range (2 * k - 1)).flatMap (fun s ↦ surfaceBand (4 * k - 2 - s) (4 * k - s)) ++
    surfaceBand 0 (2 * k + 1) ++ surfaceBand (2 * k) (4 * k + 1) ++ [(4 * k + 1, false)]

end AJConjecture
