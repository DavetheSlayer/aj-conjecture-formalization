import Mathlib
import AJConjecture.SkeinMorseWord
import AJConjecture.SkeinPlaceBasic

/-!
# The thick operator of a Morse word: composition

The operator of the empty word is the identity, the operator of a concatenation is the product
through the number of tensor factors at the end of the first word, and for a word that fits on
`n` strands that number is `c` times the number of strands at its end.

Proofs: `morseOp_nil` is `AJConjecture.skPlace_one` with `k = 0`; `morseOp_append` is an
induction on the first word (the two definitions recurse in the same way); `morseThickOut_eq`
is an induction on the word with `Nat.mul_add` and `Nat.mul_sub`.
-/

namespace AJConjecture

/-- The operator of the empty word is the identity. -/
theorem morseOp_nil (c N : ℕ) : morseOp c [] N N = 1 :=
  skPlace_one N 0 0 (Nat.zero_le N)

/-- The operator of a concatenation is the product of the operators. -/
theorem morseOp_append (c : ℕ) (u v : MorseWord) (N N' : ℕ) :
    morseOp c (u ++ v) N N' =
      morseOp c u N (morseThickOut c N u) * morseOp c v (morseThickOut c N u) N' := by
  induction u generalizing N with
  | nil =>
    change morseOp c v N N' = morseOp c [] N N * morseOp c v N N'
    rw [morseOp_nil, Matrix.one_mul]
  | cons l u ih =>
    change morseLetterOp c l N _ * morseOp c (u ++ v) _ N' =
      morseLetterOp c l N _ * morseOp c u _ _ * morseOp c v _ N'
    rw [ih, Matrix.mul_assoc]
    rfl

set_option linter.unusedVariables false in
/-- A word that fits on `n` strands ends, for the thickness `c`, on `c` times the number of
strands at its end. -/
theorem morseThickOut_eq (c n : ℕ) (w : MorseWord) (h : morseFits n w = true) :
    morseThickOut c (c * n) w = c * morseOut n w := by
  clear h
  induction w generalizing n with
  | nil => rfl
  | cons l w ih =>
    change morseThickOut c (c * n + c * morseKindOut l.1 - c * morseKindIn l.1) w =
      c * morseOut (n + morseKindOut l.1 - morseKindIn l.1) w
    rw [← ih, Nat.mul_sub, Nat.mul_add]

end AJConjecture
