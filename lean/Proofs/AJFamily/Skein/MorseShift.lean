import Mathlib
import AJConjecture.SkeinMorseRule

/-!
# Shifting Morse words

Shifting a letter, a word or a checker rule by `d` strands to the right, that is, adding `d` idle
strands on the left.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- Shift a letter by `d` strands to the right (add `d` idle strands on the left). -/
def shiftLetter (d : ℕ) (l : MorseLetter) : MorseLetter := (l.1, l.2 + d)

/-- Shift a word by `d` strands. -/
def morseShiftWord (d : ℕ) (w : MorseWord) : MorseWord := w.map (shiftLetter d)

/-- Shift a rule by `d` strands. -/
def shiftRule (d : ℕ) : MorseRule → MorseRule
  | .zig i r => .zig (i + d) r
  | .r2 i s => .r2 (i + d) s
  | .r3 i s => .r3 (i + d) s
  | .cupSlide i s r => .cupSlide (i + d) s r
  | .capSlide i s r => .capSlide (i + d) s r
  | .kink i s => .kink (i + d) s
  | .exch a b => .exch (shiftLetter d a) (shiftLetter d b)

end AJConjecture
