import Mathlib
import AJConjecture.SkeinMorseRule

/-!
# The checker of move lists

A move is a position in a word, a rule and a direction. `morseApply` replaces one side of the
rule, found at that position, by the other side, after checking the side condition of the rule
and that both sides fit on the strands present at that position. An isotopy of diagrams is then
a list of moves, checked by evaluating `morseApplyAll` in the kernel; the thickness does not
occur in it.
-/

namespace AJConjecture

/-- A move: the position in the word, the rule, and `true` to apply the rule from right to
left. -/
abbrev MorseMove : Type := ℕ × MorseRule × Bool

/-- Apply one move to a word that starts on `n₀` strands; `none` when the move does not apply. -/
def morseApply (n₀ : ℕ) (w : MorseWord) (mv : MorseMove) : Option MorseWord :=
  let src := if mv.2.2 then morseRuleRhs mv.2.1 else morseRuleLhs mv.2.1
  let dst := if mv.2.2 then morseRuleLhs mv.2.1 else morseRuleRhs mv.2.1
  let n := morseOut n₀ (w.take mv.1)
  if decide (mv.1 ≤ w.length) && morseRuleOk mv.2.1 && src.isPrefixOf (w.drop mv.1) &&
      morseFits n src && morseFits n dst then
    some (w.take mv.1 ++ dst ++ (w.drop mv.1).drop src.length)
  else none

/-- Apply a list of moves. -/
def morseApplyAll (n₀ : ℕ) : MorseWord → List MorseMove → Option MorseWord
  | w, [] => some w
  | w, mv :: mvs => (morseApply n₀ w mv).bind fun w' ↦ morseApplyAll n₀ w' mvs

end AJConjecture
