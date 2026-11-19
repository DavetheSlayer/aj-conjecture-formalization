import Mathlib

/-!
# Knots as closed braids

By Alexander's theorem every knot in `S³` is the closure of a braid, and all the invariants
entering the AJ conjecture (the coloured Jones function, the knot group with its peripheral
pair) can be read off a braid word. The conjecture is therefore stated over closed braids
with one component.
-/

namespace AJConjecture

/-- A braid word: `(i, true)` is the positive Artin generator `σ_i` on the strands `i`, `i + 1`
(numbered from `0`), and `(i, false)` is its inverse. -/
abbrev BraidWord : Type := List (ℕ × Bool)

/-- Every generator of the word `w` exists on `m` strands. -/
def IsOnStrands (m : ℕ) (w : BraidWord) : Prop :=
  ∀ g ∈ w, g.1 + 1 < m

/-- The transposition of the strands `i`, `i + 1` (the identity when `i + 1` is not a strand). -/
def strandSwap (m i : ℕ) : Equiv.Perm (Fin m) :=
  if h : i + 1 < m then Equiv.swap ⟨i, by omega⟩ ⟨i + 1, h⟩ else 1

/-- The permutation of the `m` strands induced by a braid word. -/
def strandPerm (m : ℕ) (w : BraidWord) : Equiv.Perm (Fin m) :=
  (w.map fun g ↦ strandSwap m g.1).prod

/-- A knot diagram given as a closed braid: a braid word on a positive number of strands whose
closure has a single component. -/
structure BraidKnot where
  /-- The number of strands. -/
  strands : ℕ
  /-- The braid word. -/
  word : BraidWord
  /-- There is at least one strand. -/
  strands_pos : 0 < strands
  /-- The word only uses generators on these strands. -/
  isOnStrands : IsOnStrands strands word
  /-- The closure is connected: the strand permutation is transitive. -/
  connected : ∀ i j : Fin strands, ∃ k : ℕ, (strandPerm strands word ^ k) i = j

end AJConjecture
