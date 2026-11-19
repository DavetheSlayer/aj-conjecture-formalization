import Mathlib
import AJTwist.TwDefs
import AJHandoff.TorusKnot.PairKIsoPlumbDefs

/-!
# The fixed macros of the positive clasp

The positive clasp differs from the negative one in the two Hopf letters of the fence word. Both
differences are local.

* **The tip.** `morseReach_twkTipFlip`: the last Hopf crossing with the positive sign, followed
  by the cap of the Hopf disc, is the negative one preceded by one negative full twist of the thin
  pair of the Hopf disc. After it the library macro `FINAL` applies unchanged.
* **The clasp.** In band coordinates the first Hopf block (the *hook* `twkHook σ`) followed by
  the tip (`isoXTip`, moved down to the hook) is a tangle from two strands to two strands,
  `twkKRaw σ`, and it *is* the clasp of sign `σ` (`morseReach_twkKRaw`): for the negative clasp
  without the twist, for the positive clasp with the one twist left by the tip flip.

All four certificates are explicit move lists checked by `decide` (found with
`SCR/KP/tools/msearch.py`; both sides were first compared as Kauffman-bracket operators at
thickness one and two).
-/

namespace AJConjecture

/-- `m` negative full twists of two strands. -/
def twkTw (m : ℕ) : MorseWord := List.replicate (2 * m) (isoX false 0)

/-- The number of negative full twists of the Hopf pair left in front of the tip: none for the
negative clasp (`σ = true`), one for the positive clasp. -/
def twkTipTw (σ : Bool) : ℕ := if σ then 0 else 1

/-- The hook of sign `σ` in band coordinates: the Hopf disc opens on the right of the band
`0, 1`, its left edge passes over the strand `1` and crosses the strand `0` (`σ = true`: the
library's negative hook of `isoBHopf`). -/
def twkHook (σ : Bool) : MorseWord := [isoU 2, isoX true 1, isoX (!σ) 0, isoX false 1]

/-- The raw clasp bead: the hook of sign `σ`, the twists of the Hopf pair left by the tip flip,
and the tip. A tangle from two strands to two strands. -/
def twkKRaw (σ : Bool) : MorseWord :=
  twkHook σ ++ morseShiftWord 2 (twkTw (twkTipTw σ)) ++ morseShiftWord 1 isoXTip

/-- The tip flip: a positive Hopf crossing in front of the cap of the Hopf disc is a negative
full twist of the Hopf pair followed by the negative Hopf crossing. -/
theorem morseReach_twkTipFlip :
    MorseReach 5 (isoBand 1 3 true ++ [isoN 3])
      (morseShiftWord 3 (twkTw 1) ++ isoBand 1 3 false ++ [isoN 3]) := by
  exact ⟨[(0, .r2 1 false, true), (0, .r2 3 false, true),
      (1, .exch (.cross false, 1) (.cross true, 3), true), (3, .r3 1 true, false),
      (5, .r2 2 true, false), (4, .exch (.cross true, 1) (.cap, 3), false),
      (2, .capSlide 2 true false, false), (2, .capSlide 2 false false, true),
      (4, .exch (.cross true, 1) (.cap, 3), true),
      (1, .exch (.cross false, 1) (.cross false, 3), false), (2, .r2 2 true, true),
      (3, .r3 1 false, true), (5, .r2 1 false, false)], by decide⟩

/-- The raw clasp bead of the negative clasp is the clasp. -/
theorem morseReach_twkKRaw_true : MorseReach 2 (twkKRaw true) (claspSWord true) := by
  exact ⟨[(2, .r2 1 true, true), (5, .exch (.cup, 1) (.cross false, 1), true),
      (8, .exch (.cap, 1) (.cap, 3), false), (6, .capSlide 2 false false, false),
      (5, .zig 1 true, false), (3, .capSlide 0 false false, false)], by decide⟩

/-- The raw clasp bead of the positive clasp (positive hook, one negative full twist of the Hopf
pair, the tip) is the positive clasp. -/
theorem morseReach_twkKRaw_false : MorseReach 2 (twkKRaw false) (claspSWord false) := by
  exact ⟨[(6, .r2 1 true, true), (7, .exch (.cup, 1) (.cross false, 1), true),
      (10, .exch (.cap, 1) (.cap, 3), false), (8, .capSlide 2 false false, false),
      (7, .zig 1 true, false), (3, .r2 2 true, true), (4, .r3 1 false, true),
      (4, .r2 2 true, true), (7, .r3 1 false, true), (9, .r2 1 false, false),
      (7, .capSlide 1 false true, false), (5, .capSlide 1 false false, false),
      (2, .exch (.cross true, 0) (.cross true, 2), false), (0, .cupSlide 1 true true, false),
      (1, .exch (.cross true, 0) (.cross true, 2), false), (2, .r2 1 true, true),
      (5, .capSlide 0 false true, true), (4, .r2 0 true, false),
      (0, .cupSlide 1 true false, false)], by decide⟩

/-- The raw clasp bead is the clasp of its sign. -/
theorem morseReach_twkKRaw (σ : Bool) : MorseReach 2 (twkKRaw σ) (claspSWord σ) := by
  cases σ
  · exact morseReach_twkKRaw_false
  · exact morseReach_twkKRaw_true

/-- The raw clasp bead is a tangle from two strands to two strands. -/
theorem morseFits_twkKRaw (σ : Bool) :
    morseFits 2 (twkKRaw σ) = true ∧ morseOut 2 (twkKRaw σ) = 2 := by
  cases σ <;> decide

end AJConjecture
