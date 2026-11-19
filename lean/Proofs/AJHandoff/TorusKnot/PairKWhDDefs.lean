import Mathlib
import AJHandoff.TorusKnot.PairKTargetWord

/-!
# The untwisted negative-clasp Whitehead double of a long-knot diagram

A long-knot diagram is a Morse word `D` from one strand to one strand (`AJConjecture.MorseWord`,
read from the bottom up). This file defines, independently of torus knots,

* the **orientations** of a Morse word: labellings of the strands at every level by a direction
  (`true` = upward) that are consistent with every letter (a cup or cap joins two strands of
  opposite directions, a crossing exchanges them). `orientStates w S` propagates a list of states
  (directions at the current level, oriented writhe so far) through `w`, one state per partial
  orientation; `orientWrithes D` lists the oriented writhes of the orientations of `D` whose two
  ends point upward, one entry per orientation;
* `IsLongKnotDiagram D`: `D` fits on one strand and has exactly one such orientation (that is,
  no closed components); `morseWrithe D`, its oriented writhe, the blackboard framing;
* `whDouble D = [cup 1] ++ morseDouble D ++ bandUntwist (morseWrithe D) ++ claspWord ++ [cap 1]`:
  the blackboard double of `D` (a band along `D`), `morseWrithe D` negative full twists of the
  two edges of the band (they cancel the blackboard framing, so the band is untwisted), and the
  clasp; the input strand is the left edge of the band and the closing strand runs up on the
  right. The closure of `whDouble D` is the untwisted negative-clasp Whitehead double of the
  closure of `D` (orientation and sign conventions: `formalization/WHITEHEAD_BRIDGE.md` of the audit repository);
* the **linking number** of the two strings of a two-string tangle by crossing signs
  (`bandLinkings`), used to state that the band of `whDouble D` is untwisted.

For the long closure of `(σ_0 ⋯ σ_(r-2))^s` the word `whDouble` is literally the library's
target word `pairTargetWord r s` (`AJHandoff.TorusKnot.PairKWhDIdent`).
-/

namespace AJConjecture

/-- The oriented sign of a crossing of sign `s` whose two strands point in the directions `a`
and `b` (`true` = upward): `±1` with the sign `s` when the strands are parallel, the opposite sign
when they are antiparallel. -/
def orientSign (s a b : Bool) : ℤ :=
  (if s then 1 else -1) * (if a = b then 1 else -1)

/-- One letter acting on an oriented state `(a, x)`: `a` the directions of the strands at the
current level, `x` the oriented writhe so far. A cup at `i` inserts two strands of opposite
directions, in both possible ways; a cap at `i` requires opposite directions; a crossing
exchanges the two directions and adds its oriented sign. A letter that does not fit gives no
state. -/
def orientLetter : MorseLetter → List Bool × ℤ → List (List Bool × ℤ)
  | (.cup, i), (a, x) =>
    if i ≤ a.length then
      [(a.take i ++ true :: false :: a.drop i, x), (a.take i ++ false :: true :: a.drop i, x)]
    else []
  | (.cap, i), (a, x) =>
    match a.drop i with
    | p :: q :: b => if p = q then [] else [(a.take i ++ b, x)]
    | _ => []
  | (.cross s, i), (a, x) =>
    match a.drop i with
    | p :: q :: b => [(a.take i ++ q :: p :: b, x + orientSign s p q)]
    | _ => []

/-- The oriented states of a word: every state of `S` propagated through the letters of `w`, one
output state for every way of orienting the cups of `w`. -/
def orientStates : MorseWord → List (List Bool × ℤ) → List (List Bool × ℤ)
  | [], S => S
  | l :: w, S => orientStates w (S.flatMap (orientLetter l))

/-- The oriented writhes of the orientations of the long-knot diagram `D` in which both ends
point upward, one entry per orientation. -/
def orientWrithes (D : MorseWord) : List ℤ :=
  ((orientStates D [([true], 0)]).filter fun st ↦ st.1 = [true]).map Prod.snd

/-- `D` is a long-knot diagram: a Morse word on one strand with exactly one orientation whose
two ends point upward. (Each closed component would contribute two orientations, so this says
that `D` is a single arc from the bottom to the top.) -/
def IsLongKnotDiagram (D : MorseWord) : Prop :=
  morseFits 1 D = true ∧ (orientWrithes D).length = 1

/-- The oriented writhe (blackboard framing) of a long-knot diagram: the sum of the oriented
signs of its crossings, for its unique orientation. -/
def morseWrithe (D : MorseWord) : ℤ :=
  (orientWrithes D).sum

/-- The `-w` full twists of the two edges of a band (both edges oriented upward) that cancel the
blackboard framing `w`: `2w` negative crossings of the strands `0, 1` if `w ≥ 0`, `-2w` positive
ones if `w < 0`. -/
def bandUntwist (w : ℤ) : MorseWord :=
  if 0 ≤ w then List.replicate (2 * w.toNat) (.cross false, 0)
  else List.replicate (2 * (-w).toNat) (.cross true, 0)

/-- The untwisted band along the long-knot diagram `D`: its blackboard double followed by the
full twists that cancel the blackboard framing. A two-string tangle on two strands. -/
def whBand (D : MorseWord) : MorseWord :=
  morseDouble D ++ bandUntwist (morseWrithe D)

/-- **The untwisted negative-clasp Whitehead double** of the long-knot diagram `D`: a cup opening
the band and the closing strand, the untwisted band along `D`, the clasp, and the cap joining the
clasp to the closing strand. -/
def whDouble (D : MorseWord) : MorseWord :=
  [(.cup, 1)] ++ whBand D ++ claspWord ++ [(.cap, 1)]

/-- The diagram of a closed braid cut open in its first column (a long-knot diagram). -/
def braidLongDiagram (K : BraidKnot) : MorseWord :=
  morseLongClosure K.strands K.word

/-! ### Linking number of a two-string tangle -/

/-- One letter acting on a labelled state `(a, x)`: every strand carries a direction and a
component label; a cup or cap joins strands of opposite directions and equal components; a
crossing exchanges the labels and adds its oriented sign if the two strands belong to different
components. -/
def lkLetter : MorseLetter → List (Bool × Bool) × ℤ → List (List (Bool × Bool) × ℤ)
  | (.cup, i), (a, x) =>
    if i ≤ a.length then
      [true, false].flatMap fun d ↦ [false, true].map fun c ↦
        (a.take i ++ (d, c) :: (!d, c) :: a.drop i, x)
    else []
  | (.cap, i), (a, x) =>
    match a.drop i with
    | p :: q :: b => if p.1 ≠ q.1 ∧ p.2 = q.2 then [(a.take i ++ b, x)] else []
    | _ => []
  | (.cross s, i), (a, x) =>
    match a.drop i with
    | p :: q :: b =>
      [(a.take i ++ q :: p :: b, x + if p.2 = q.2 then 0 else orientSign s p.1 q.1)]
    | _ => []

/-- The labelled states of a word. -/
def lkStates : MorseWord → List (List (Bool × Bool) × ℤ) → List (List (Bool × Bool) × ℤ)
  | [], S => S
  | l :: w, S => lkStates w (S.flatMap (lkLetter l))

/-- The ends of a band: two upward strands, the left one of component `false`, the right one of
component `true`. -/
def bandEnd : List (Bool × Bool) :=
  [(true, false), (true, true)]

/-- The linking numbers of the two strings of a two-string tangle diagram `T`, one entry for
every labelling in which the left string and the right string both run upward from the bottom to
the top: half the sum of the oriented signs of the crossings between the two strings. -/
def bandLinkings (T : MorseWord) : List ℤ :=
  ((lkStates T [(bandEnd, 0)]).filter fun st ↦ st.1 = bandEnd).map fun st ↦ st.2 / 2

end AJConjecture
