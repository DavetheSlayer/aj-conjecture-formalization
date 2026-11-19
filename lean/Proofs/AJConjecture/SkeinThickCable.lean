import Mathlib
import AJConjecture.BraidKnot

/-!
# Crossings of bundles of arbitrary thickness, and cables with a thickness profile

`thickCross a b off s` is the braid word of the crossing of a bundle of `a` parallel strands,
starting at the position `off`, with the bundle of `b` strands on its right, all crossings of
sign `s`; for `a = b = c` it is `AJConjecture.cableGen`. A thickness profile `κ : ℕ → ℕ` gives
the number of strands of the bundle in each column, and `thickCable κ w` is the cable of the
braid word `w` in which the bundle that starts in the column `x` has `κ x` strands. Profiles
that are not constant are needed to push a cap along a strand of a cabled braid: the part of the
strand behind the cap is thinner by two.
-/

namespace AJConjecture

/-- The word `∏_x ∏_y σ_{off+x+y}^{±1}`: for `s = true`, the bundle of `a` strands at `off`
crosses the `b` strands on its right (positive crossings); for `s = false`, the inverse word. -/
def thickGen (a b off : ℕ) (s : Bool) : BraidWord :=
  if s then
    (List.range a).reverse.flatMap fun x ↦ (List.range b).map fun y ↦ (off + x + y, true)
  else
    (List.range a).flatMap fun x ↦ (List.range b).reverse.map fun y ↦ (off + x + y, false)

/-- The crossing of the bundle of `a` strands at `off` with the bundle of `b` strands on its
right, of sign `s`; afterwards the bundle of `b` strands is at `off` and the other at
`off + b`. The negative crossing is the inverse of the positive crossing of the bundles in the
other order. -/
def thickCross (a b off : ℕ) (s : Bool) : BraidWord :=
  if s then thickGen a b off true else thickGen b a off false

/-- The position of the first strand of the column `x` in the profile `κ`. -/
def profileOffset (κ : ℕ → ℕ) (x : ℕ) : ℕ :=
  ∑ y ∈ Finset.range x, κ y

/-- The profile after a crossing of the columns `i`, `i + 1`. -/
def profileSwap (κ : ℕ → ℕ) (i : ℕ) : ℕ → ℕ :=
  fun x ↦ κ (Equiv.swap i (i + 1) x)

/-- The cable of a braid word with the thickness profile `κ` at the bottom. -/
def thickCable : (ℕ → ℕ) → BraidWord → BraidWord
  | _, [] => []
  | κ, g :: w =>
    thickCross (κ g.1) (κ (g.1 + 1)) (profileOffset κ g.1) g.2 ++ thickCable (profileSwap κ g.1) w

/-- The thickness profile at the top of the word. -/
def profileEnd : (ℕ → ℕ) → BraidWord → ℕ → ℕ
  | κ, [] => κ
  | κ, g :: w => profileEnd (profileSwap κ g.1) w

/-- The column in which the strand that starts in the column `p` ends. -/
def strandEnd : BraidWord → ℕ → ℕ
  | [], p => p
  | g :: w, p => strandEnd w (Equiv.swap g.1 (g.1 + 1) p)

end AJConjecture
