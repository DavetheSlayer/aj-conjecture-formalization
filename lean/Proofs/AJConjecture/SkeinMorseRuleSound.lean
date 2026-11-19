import Mathlib
import AJConjecture.SkeinMorseRuleCapSlide
import AJConjecture.SkeinMorseRuleCupSlide
import AJConjecture.SkeinMorseRuleExch
import AJConjecture.SkeinMorseRuleKink
import AJConjecture.SkeinMorseRuleR2
import AJConjecture.SkeinMorseRuleR3
import AJConjecture.SkeinMorseRuleZig

/-!
# Every rule is sound

The seven families of elementary moves preserve the thick operator of a Morse word, for every
thickness.
-/

namespace AJConjecture

/-- Every elementary move of Morse words is sound. -/
theorem morseRuleSound (r : MorseRule) : MorseRuleSound r := by
  cases r with
  | zig i r => exact morseRuleSound_zig i r
  | r2 i s => exact morseRuleSound_r2 i s
  | r3 i s => exact morseRuleSound_r3 i s
  | cupSlide i s r => exact morseRuleSound_cupSlide i s r
  | capSlide i s r => exact morseRuleSound_capSlide i s r
  | kink i s => exact morseRuleSound_kink i s
  | exch a b => exact morseRuleSound_exch a b

end AJConjecture
