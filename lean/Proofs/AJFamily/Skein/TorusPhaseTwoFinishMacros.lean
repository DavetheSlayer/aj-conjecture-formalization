import Mathlib
import AJFamily.Skein.MorseReach

/-!
# The fixed macros of stage E

Three fixed checker certificates of stage E, with acceptance proved by `decide`: `E1` turns the
conjugated clasp into the clasp with two opposite curls, and `CU13`, `CU31` move a curl through a
doubled crossing from the strand `1` to the strand `3` and back.
-/

namespace AJConjecture

/-- Macro `E1`, left side: the conjugated clasp at the end of `phaseTwoWG k` (window: the last two
twist letters, `+0 claspWord −0`, the final cap) → clasp, a negative curl on the input side
(`u1 −2 n1`, in front of the last twist letter) and a positive curl on the left leg of the X-cup
(`u2 +3 n2`). -/
def phaseTwoMacroE1_lhs : MorseWord :=
  [(.cross false, 0), (.cross false, 0), (.cross true, 0), (.cup, 2), (.cross true, 1),
    (.cross true, 1), (.cap, 0), (.cross false, 0), (.cap, 1)]

/-- Macro `E1`, right side. -/
def phaseTwoMacroE1_rhs : MorseWord :=
  [(.cross false, 0), (.cup, 1), (.cross false, 2), (.cap, 1), (.cross false, 0), (.cup, 2),
    (.cup, 2), (.cross true, 3), (.cap, 2), (.cross true, 1), (.cross true, 1), (.cap, 0),
    (.cap, 1)]

/-- Macro `E1`, the moves (61). -/
def phaseTwoMacroE1_moves : List MorseMove :=
  [(2, .exch (.cross true, 0) (.cup, 2), false), (3, .r2 1 false, true), (4, .r3 0 true, true),
    (5, .r3 0 true, true), (7, .zig 1 true, true), (8, .exch (.cross true, 0) (.cap, 2), true),
    (9, .exch (.cap, 0) (.cap, 2), true), (7, .cupSlide 0 false false, true),
    (9, .r2 0 false, false), (6, .exch (.cup, 0) (.cross true, 1), true),
    (7, .exch (.cross false, 1) (.cross true, 3), true),
    (8, .exch (.cap, 0) (.cross true, 3), true), (9, .r2 0 false, true),
    (10, .capSlide 0 true true, false), (8, .r2 0 false, true),
    (6, .cupSlide 0 false false, false), (6, .cupSlide 1 true true, true),
    (8, .exch (.cross true, 0) (.cross true, 2), true),
    (9, .exch (.cap, 0) (.cross true, 2), true), (5, .exch (.cross true, 0) (.cup, 2), false),
    (6, .r3 0 true, false), (7, .capSlide 0 true true, false),
    (5, .cupSlide 1 false false, true), (7, .r2 1 false, false),
    (5, .cupSlide 0 true false, true), (4, .exch (.cup, 0) (.cross true, 0), true),
    (8, .r2 1 true, true), (9, .capSlide 1 false true, false), (6, .r3 0 true, true),
    (8, .exch (.cross true, 0) (.cap, 2), false),
    (5, .exch (.cross true, 0) (.cross true, 2), true), (6, .capSlide 1 true false, false),
    (6, .capSlide 0 false true, true), (5, .r2 0 true, false),
    (3, .exch (.cup, 0) (.cross false, 1), true),
    (4, .exch (.cross false, 1) (.cross false, 3), true),
    (5, .exch (.cap, 0) (.cross false, 3), true), (2, .exch (.cup, 0) (.cup, 2), true),
    (3, .exch (.cross false, 1) (.cup, 4), true), (4, .exch (.cap, 0) (.cup, 4), true),
    (1, .exch (.cup, 0) (.cross false, 0), true), (1, .cupSlide 0 false true, true),
    (3, .r3 1 false, false), (5, .exch (.cap, 0) (.cross false, 2), true),
    (2, .exch (.cross false, 0) (.cross false, 2), false), (3, .capSlide 0 false true, false),
    (8, .r2 0 true, false), (8, .capSlide 0 false true, true), (7, .r2 0 true, false),
    (8, .exch (.cap, 0) (.cross false, 2), false), (9, .r2 1 false, true),
    (7, .r3 1 false, false), (5, .cupSlide 1 false true, false), (8, .r2 1 false, true),
    (6, .r3 1 false, false), (8, .zig 2 false, true),
    (9, .exch (.cap, 2) (.cross false, 4), false), (10, .r2 3 false, true),
    (8, .cupSlide 3 false false, false), (5, .cupSlide 1 false false, false),
    (5, .exch (.cup, 2) (.cup, 2), false)]

/-- The left side of macro `E1` fits on 3 strands. -/
theorem phaseTwoMacroE1_fits : morseFits 3 phaseTwoMacroE1_lhs = true := by decide

/-- The checker accepts macro `E1`. -/
theorem phaseTwoMacroE1_ok :
    morseApplyAll 3 phaseTwoMacroE1_lhs phaseTwoMacroE1_moves = some phaseTwoMacroE1_rhs := by
  decide

/-- Macro `E1` as a reachability statement. -/
theorem morseReach_phaseTwoMacroE1 : MorseReach 3 phaseTwoMacroE1_lhs phaseTwoMacroE1_rhs :=
  ⟨_, phaseTwoMacroE1_ok⟩

/-- Macro `CU13`, left side: a positive right curl on the strand `1` passes a doubled crossing `D`
and ends on the strand `3`. -/
def phaseTwoMacroCU13_lhs : MorseWord :=
  [(.cup, 2), (.cross true, 1), (.cap, 2), (.cross true, 1), (.cross true, 2), (.cross true, 0),
    (.cross true, 1)]

/-- Macro `CU13`, right side. -/
def phaseTwoMacroCU13_rhs : MorseWord :=
  [(.cross true, 1), (.cross true, 2), (.cross true, 0), (.cross true, 1), (.cup, 4),
    (.cross true, 3), (.cap, 4)]

/-- Macro `CU13`, the moves (18). -/
def phaseTwoMacroCU13_moves : List MorseMove :=
  [(2, .capSlide 2 true false, true), (1, .exch (.cross true, 1) (.cross true, 3), false),
    (4, .exch (.cross true, 1) (.cap, 3), true), (2, .r3 1 true, false),
    (0, .cupSlide 2 true false, false), (0, .exch (.cross true, 1) (.cup, 3), true),
    (3, .capSlide 3 true false, true), (2, .exch (.cross true, 2) (.cross true, 4), false),
    (5, .exch (.cross true, 2) (.cap, 4), true), (3, .r3 2 true, false),
    (1, .cupSlide 3 true false, false), (1, .exch (.cross true, 2) (.cup, 4), true),
    (4, .exch (.cross true, 0) (.cap, 4), true),
    (3, .exch (.cross true, 0) (.cross true, 3), true),
    (2, .exch (.cross true, 0) (.cup, 4), true), (5, .exch (.cross true, 1) (.cap, 4), true),
    (4, .exch (.cross true, 1) (.cross true, 3), true),
    (3, .exch (.cross true, 1) (.cup, 4), true)]

/-- The left side of macro `CU13` fits on 7 strands. -/
theorem phaseTwoMacroCU13_fits : morseFits 7 phaseTwoMacroCU13_lhs = true := by decide

/-- The checker accepts macro `CU13`. -/
theorem phaseTwoMacroCU13_ok :
    morseApplyAll 7 phaseTwoMacroCU13_lhs phaseTwoMacroCU13_moves = some phaseTwoMacroCU13_rhs := by
  decide

/-- Macro `CU13` as a reachability statement. -/
theorem morseReach_phaseTwoMacroCU13 : MorseReach 7 phaseTwoMacroCU13_lhs phaseTwoMacroCU13_rhs :=
  ⟨_, phaseTwoMacroCU13_ok⟩

/-- Macro `CU31`, left side: a positive right curl on the strand `3` passes a doubled crossing `D`
and ends on the strand `1`. -/
def phaseTwoMacroCU31_lhs : MorseWord :=
  [(.cup, 4), (.cross true, 3), (.cap, 4), (.cross true, 1), (.cross true, 2), (.cross true, 0),
    (.cross true, 1)]

/-- Macro `CU31`, right side. -/
def phaseTwoMacroCU31_rhs : MorseWord :=
  [(.cross true, 1), (.cross true, 2), (.cross true, 0), (.cross true, 1), (.cup, 2),
    (.cross true, 1), (.cap, 2)]

/-- Macro `CU31`, the moves (18). -/
def phaseTwoMacroCU31_moves : List MorseMove :=
  [(2, .exch (.cross true, 1) (.cap, 4), true),
    (1, .exch (.cross true, 1) (.cross true, 3), true),
    (0, .exch (.cross true, 1) (.cup, 4), true), (3, .exch (.cross true, 2) (.cap, 4), true),
    (4, .capSlide 3 true true, true), (2, .r3 2 true, true),
    (4, .exch (.cross true, 2) (.cross true, 4), false),
    (1, .exch (.cross true, 2) (.cup, 4), true), (2, .cupSlide 3 true true, false),
    (4, .exch (.cross true, 0) (.cap, 3), true),
    (3, .exch (.cross true, 0) (.cross true, 2), true),
    (2, .exch (.cross true, 0) (.cup, 3), true), (5, .exch (.cross true, 1) (.cap, 3), true),
    (6, .capSlide 2 true true, true), (4, .r3 1 true, true),
    (6, .exch (.cross true, 1) (.cross true, 3), false),
    (3, .exch (.cross true, 1) (.cup, 3), true), (4, .cupSlide 2 true true, false)]

/-- The left side of macro `CU31` fits on 7 strands. -/
theorem phaseTwoMacroCU31_fits : morseFits 7 phaseTwoMacroCU31_lhs = true := by decide

/-- The checker accepts macro `CU31`. -/
theorem phaseTwoMacroCU31_ok :
    morseApplyAll 7 phaseTwoMacroCU31_lhs phaseTwoMacroCU31_moves = some phaseTwoMacroCU31_rhs := by
  decide

/-- Macro `CU31` as a reachability statement. -/
theorem morseReach_phaseTwoMacroCU31 : MorseReach 7 phaseTwoMacroCU31_lhs phaseTwoMacroCU31_rhs :=
  ⟨_, phaseTwoMacroCU31_ok⟩

end AJConjecture
