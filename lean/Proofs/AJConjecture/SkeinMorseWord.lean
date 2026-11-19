import Mathlib
import AJConjecture.SkeinHalfTwist
import AJConjecture.SkeinPlace

/-!
# Morse words and their thick operators

A sliced diagram of a tangle is a word in four kinds of letters, each at a position `i`: a cup
(two new strands at the positions `i`, `i + 1`), a cap (on the strands `i`, `i + 1`), and a
positive or negative crossing of the strands `i`, `i + 1`. The word is read in the order of the
matrix product of `AJConjecture.SkMat`: the first letter acts first.

For a thickness `c`, every strand is replaced by a bundle of `c` parallel strands and the letter
at the position `i` becomes the operator placed at the offset `c * i`: the thick cup
`cupThick c`, the thick cap `capThick c`, or the cabled half twist `halfTwist c s`. The operator
`morseOp c w N N'` of a word is the product of the operators of its letters, from `N` to `N'`
tensor factors; as everywhere in the skein layer the sizes are free parameters, and an operator
that does not fit is `0`. For a braid word this is the matrix of its `c`-cable, and for the word
"cups, braid, caps" it is the long knot operator (`AJConjecture.SkeinMorseBraid`).

This is the language of the isotopy lemmas: an isotopy of diagrams is a list of
elementary moves of Morse words (`AJConjecture.MorseRule`), each of which preserves the thick
operator for every thickness.
-/

namespace AJConjecture

/-- The kinds of letters of a Morse word: cup, cap, and a crossing with its sign. -/
inductive MorseKind
  | cup
  | cap
  | cross (s : Bool)
  deriving DecidableEq, Repr

/-- A letter of a Morse word: a kind and the position of its first strand. -/
abbrev MorseLetter : Type := MorseKind × ℕ

/-- A Morse word: a sliced diagram, read in the order of the matrix product. -/
abbrev MorseWord : Type := List MorseLetter

/-- The number of strands a letter of this kind consumes. -/
def morseKindIn : MorseKind → ℕ
  | .cup => 0
  | .cap => 2
  | .cross _ => 2

/-- The number of strands a letter of this kind produces. -/
def morseKindOut : MorseKind → ℕ
  | .cup => 2
  | .cap => 0
  | .cross _ => 2

/-- The number of strands after a letter, when there are `n` strands in front of it. -/
def morseLetterOut (n : ℕ) (l : MorseLetter) : ℕ :=
  n + morseKindOut l.1 - morseKindIn l.1

/-- The number of strands at the end of a word that starts on `n` strands. -/
def morseOut : ℕ → MorseWord → ℕ
  | n, [] => n
  | n, l :: w => morseOut (morseLetterOut n l) w

/-- Every letter of the word fits on the strands present when it is reached. -/
def morseFits : ℕ → MorseWord → Bool
  | _, [] => true
  | n, l :: w => decide (l.2 + morseKindIn l.1 ≤ n) && morseFits (morseLetterOut n l) w

/-- The number of tensor factors at the end of a word of thickness `c` that starts on `N` tensor
factors. -/
def morseThickOut (c : ℕ) : ℕ → MorseWord → ℕ
  | N, [] => N
  | N, l :: w => morseThickOut c (N + c * morseKindOut l.1 - c * morseKindIn l.1) w

/-- The operator of one letter for the thickness `c`: the thick cup, the thick cap or the cabled
half twist, placed at the offset `c * i`. -/
noncomputable def morseLetterOp (c : ℕ) (l : MorseLetter) (N N' : ℕ) : SkMat N N' :=
  match l.1 with
  | .cup => skPlace N N' (c * l.2) (cupThick c)
  | .cap => skPlace N N' (c * l.2) (capThick c)
  | .cross s => skPlace N N' (c * l.2) (halfTwist c s)

/-- The thick operator of a Morse word for the thickness `c`, from `N` to `N'` tensor factors. -/
noncomputable def morseOp (c : ℕ) : MorseWord → (N N' : ℕ) → SkMat N N'
  | [], N, N' => skPlace N N' 0 (1 : SkMat 0 0)
  | l :: w, N, N' =>
    morseLetterOp c l N (N + c * morseKindOut l.1 - c * morseKindIn l.1) *
      morseOp c w (N + c * morseKindOut l.1 - c * morseKindIn l.1) N'

end AJConjecture
