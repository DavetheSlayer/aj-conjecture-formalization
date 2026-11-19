import Mathlib
import AJConjecture.BraidKnot

/-!
# Knot types of closed braids

Two braid words describe the same oriented knot exactly when their closures are related by
Markov moves (Markov's theorem): relations of the braid group, conjugation, and
stabilisation `β ↦ β σ_m^{±1}` from `m` to `m + 1` strands, together with the inverse moves.
`MarkovStep` lists the elementary moves on pairs (number of strands, word); every move relates
words on the given strands only, so a chain of moves starting at a braid knot never leaves the
words on its strands. `MarkovEquiv` is the generated equivalence relation; two braid knots that
are not `MarkovEquiv` have closures of different knot types.

Conventions of `AJConjecture.BraidKnot`: the letter `(i, true)` is `σ_{i+1}` and `(i, false)`
its inverse; a word on `m` strands uses letters with `i + 1 < m`.
-/

namespace AJConjecture

/-- A closed braid before the check that it is a knot: a number of strands and a word. -/
abbrev ClosedBraid : Type := ℕ × BraidWord

/-- The elementary moves between closed braids. `cancel`, `farComm` and `braidRel` are the
relations of the braid group (the inverse forms of the braid relation follow from these with
`cancel`), `rotate` is conjugation by a generator, and `stabilize` is the Markov
stabilisation by `σ_m^{±1}` (the letter `(m - 1, b)`). -/
inductive MarkovStep : ClosedBraid → ClosedBraid → Prop
  /-- `σ_i^{±1} σ_i^{∓1} = 1`. -/
  | cancel {m : ℕ} (u v : BraidWord) (i : ℕ) (b : Bool) (h : i + 1 < m) :
      MarkovStep (m, u ++ (i, b) :: (i, !b) :: v) (m, u ++ v)
  /-- Generators at distance at least two commute. -/
  | farComm {m : ℕ} (u v : BraidWord) (i j : ℕ) (b c : Bool) (hij : i + 2 ≤ j)
      (h : j + 1 < m) :
      MarkovStep (m, u ++ (i, b) :: (j, c) :: v) (m, u ++ (j, c) :: (i, b) :: v)
  /-- `σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1}`. -/
  | braidRel {m : ℕ} (u v : BraidWord) (i : ℕ) (h : i + 2 < m) :
      MarkovStep (m, u ++ (i, true) :: (i + 1, true) :: (i, true) :: v)
        (m, u ++ (i + 1, true) :: (i, true) :: (i + 1, true) :: v)
  /-- Conjugation: the closure of `g w` is the closure of `w g`. -/
  | rotate {m : ℕ} (w : BraidWord) (g : ℕ × Bool) :
      MarkovStep (m, g :: w) (m, w ++ [g])
  /-- Markov stabilisation: a new strand and one crossing `σ_m^{±1}` with the last strand. -/
  | stabilize {m : ℕ} (w : BraidWord) (b : Bool) (hm : 0 < m) (hw : IsOnStrands m w) :
      MarkovStep (m, w) (m + 1, w ++ [(m - 1, b)])

/-- Markov equivalence of braid knots: their closures are related by a finite chain of
elementary moves and inverse moves. By Markov's theorem this is ambient isotopy of the
oriented closures. -/
def MarkovEquiv (K K' : BraidKnot) : Prop :=
  Relation.EqvGen MarkovStep (K.strands, K.word) (K'.strands, K'.word)

end AJConjecture
