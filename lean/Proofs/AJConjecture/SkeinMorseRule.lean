import Mathlib
import AJConjecture.SkeinMorseWord

/-!
# The elementary moves of Morse words

The rules of regular isotopy of sliced diagrams (Turaev's moves for framed tangles), each with
two sides:

* `zig`: a cup followed by a cap that shares one strand with it is a straight strand;
* `r2`, `r3`: the second and third Reidemeister moves;
* `cupSlide`, `capSlide`: a strand that crosses both legs of a cup (of a cap), with crossings of
  one sign, passes to the other side of it;
* `kink`: a positive and a negative curl on the same side of a strand cancel (the framed first
  Reidemeister move; in the plane this changes the rotation number by two, so it is the move
  "through infinity");
* `exch`: two letters with disjoint supports exchange their heights.

A rule is sound when its two sides have the same thick operator for every thickness
(`AJConjecture.MorseRuleSound`). A single curl is not a rule: on a bundle without projector it is
not a scalar.
-/

namespace AJConjecture

/-- The elementary moves of Morse words. -/
inductive MorseRule
  | zig (i : ℕ) (r : Bool)
  | r2 (i : ℕ) (s : Bool)
  | r3 (i : ℕ) (s : Bool)
  | cupSlide (i : ℕ) (s r : Bool)
  | capSlide (i : ℕ) (s r : Bool)
  | kink (i : ℕ) (s : Bool)
  | exch (a b : MorseLetter)
  deriving DecidableEq, Repr

/-- The left side of a rule. -/
def morseRuleLhs : MorseRule → MorseWord
  | .zig i r => if r then [(.cup, i), (.cap, i + 1)] else [(.cup, i + 1), (.cap, i)]
  | .r2 i s => [(.cross s, i), (.cross (!s), i)]
  | .r3 i s => [(.cross s, i), (.cross s, i + 1), (.cross s, i)]
  | .cupSlide i s r =>
    if r then [(.cup, i + 1), (.cross s, i), (.cross s, i + 1)]
    else [(.cup, i), (.cross s, i + 1), (.cross s, i)]
  | .capSlide i s r =>
    if r then [(.cross s, i), (.cross s, i + 1), (.cap, i)]
    else [(.cross s, i + 1), (.cross s, i), (.cap, i + 1)]
  | .kink i s =>
    [(.cup, i + 1), (.cross s, i), (.cap, i + 1), (.cup, i + 1), (.cross (!s), i), (.cap, i + 1)]
  | .exch a b => [a, (b.1, b.2 + morseKindOut a.1 - morseKindIn a.1)]

/-- The right side of a rule. -/
def morseRuleRhs : MorseRule → MorseWord
  | .zig _ _ => []
  | .r2 _ _ => []
  | .r3 i s => [(.cross s, i + 1), (.cross s, i), (.cross s, i + 1)]
  | .cupSlide i _ r => if r then [(.cup, i)] else [(.cup, i + 1)]
  | .capSlide i _ r => if r then [(.cap, i + 1)] else [(.cap, i)]
  | .kink _ _ => []
  | .exch a b => [b, a]

/-- The side condition of a rule: in an exchange the letter `a` lies to the left of the letter
`b`. -/
def morseRuleOk : MorseRule → Bool
  | .exch a b => decide (a.2 + morseKindIn a.1 ≤ b.2)
  | _ => true

/-- A rule is sound: whenever both sides fit on `n` strands, they have the same thick operator
for every thickness. -/
def MorseRuleSound (r : MorseRule) : Prop :=
  ∀ c n N N' : ℕ, N = c * n → morseRuleOk r = true → morseFits n (morseRuleLhs r) = true →
    morseFits n (morseRuleRhs r) = true →
      morseOp c (morseRuleLhs r) N N' = morseOp c (morseRuleRhs r) N N'

end AJConjecture
