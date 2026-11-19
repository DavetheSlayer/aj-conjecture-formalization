import Mathlib
import AJHandoff.TorusKnot.PairKIsoNormalDefs

/-!
# The fixed macros of stage N

Five fixed certificates (to be proved by an explicit move list checked with `decide`, as the
macros of `AJFamily.Skein.TorusPhaseTwoMacros`; the moves can be found by a breadth-first search
over the rules on these small words). The increasing-run block is the library macro `A`
(`morseReach_phaseTwoMacroA`), shifted. Both sides of each macro have equal Kauffman-bracket
operators at thickness one and two and the same arcs with the same rotation numbers
(`SCR/ISO/tools/c2checks.py`); none needs `kink`.
-/

namespace AJConjecture

/-- Macro `LC`: two discs joined by a band become a doubled cup and a positive left curl. -/
theorem morseReach_isoMacroLC :
    MorseReach 1 (isoStLC 1) [isoU 1, isoU 2, isoU 2, isoX true 3, isoN 2] := by
  exact ⟨[(0, .exch (.cup, 1) (.cup, 1), false), (1, .cupSlide 1 true false, false),
      (2, .zig 2 false, true), (3, .exch (.cap, 2) (.cross false, 4), false),
      (4, .r2 3 false, true), (2, .cupSlide 3 false false, false),
      (1, .exch (.cup, 2) (.cup, 2), false)], by decide⟩

/-- Macro `DEC`: a block of the decreasing run becomes a positive left curl. -/
theorem morseReach_isoMacroDEC : MorseReach 3 (isoStDec 1) [isoU 2, isoX true 3, isoN 2] := by
  exact ⟨[(4, .capSlide 2 true true, true), (3, .r2 2 false, false),
      (0, .cupSlide 1 true false, false)], by decide⟩

/-- Macro `TRC`: the top-right climb becomes a negative full twist, a negative curl and an inner
cap. -/
theorem morseReach_isoMacroTRC :
    MorseReach 5 (isoBand 1 3 true ++ [isoN 1]) (phaseTwoMacroA_rhs ++ [isoN 2]) := by
  exact ⟨[(3, .capSlide 1 false false, true), (5, .zig 2 true, true),
      (6, .capSlide 3 false false, true), (8, .exch (.cap, 2) (.cap, 4), true),
      (5, .exch (.cup, 2) (.cross false, 2), false), (3, .r3 1 false, true),
      (2, .r3 1 false, true), (1, .r2 1 true, false), (0, .r2 2 true, false)], by decide⟩

/-- Macro `RD`: a right descent becomes a negative full twist, a negative curl and a doubled
cap. -/
theorem morseReach_isoMacroRD :
    MorseReach 5 (isoBand 1 3 true ++ [isoN 3, isoN 1])
      (phaseTwoMacroA_rhs ++ [isoN 2, isoN 1]) := by
  exact ⟨[(3, .exch (.cap, 1) (.cap, 3), true), (3, .capSlide 1 false false, true),
      (5, .zig 2 true, true), (6, .capSlide 3 false false, true),
      (8, .exch (.cap, 2) (.cap, 4), true), (5, .exch (.cup, 2) (.cross false, 2), false),
      (3, .r3 1 false, true), (2, .r3 1 false, true), (1, .r2 1 true, false),
      (0, .r2 2 true, false)], by decide⟩

/-- Macro `FINAL`: the second Hopf letter becomes a negative curl and two caps. -/
theorem morseReach_isoMacroFINAL : MorseReach 5 isoStFinal isoFinalNF := by
  exact ⟨[(0, .zig 3 true, true), (0, .cupSlide 2 false false, true),
      (2, .exch (.cross false, 2) (.cap, 4), false), (3, .r2 2 false, false),
      (5, .exch (.cap, 1) (.cap, 3), true), (3, .capSlide 1 false true, false),
      (2, .exch (.cap, 2) (.cap, 4), true)], by decide⟩

end AJConjecture
