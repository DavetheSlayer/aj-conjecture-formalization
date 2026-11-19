import Mathlib
import AJHandoff.TorusKnot.PairKIsoEndDefs

/-!
# Stage E: fixed macros

The macros of stage E for the clasp `isoClaspU` arriving at the top end, all checked by `decide`.
`ToR1`, `PastPair`, `PastOdd`, `Cancel` are copies of the private macros of the library's stage E
(`AJFamily.Skein.TorusPhaseTwoFinishTurns`, `…FinishEnd`; same move lists); macro `E1` itself is
the public `morseReach_phaseTwoMacroE1`. `CUPL` (a left curl on the return strand turns around the
first cup onto the right edge as a right curl) was found by search (`SCR/ISO2/tools/msearch.py`).
All sides have equal Kauffman-bracket operators at thickness one and two
(`SCR/ISO2/tools/endgame.py`).
-/

namespace AJConjecture

/-- Macro `ToR1`: the curl `c₂` inside the clasp moves to the return strand. -/
theorem morseReach_isoPark_toR1 :
    MorseReach 3 (isoCurlL false 1 ++ [isoX false 0, isoU 2] ++ isoCurlL true 2 ++
        [isoX true 1, isoX true 1, isoN 0, isoN 1])
      (isoCurlL true 2 ++ isoCurlL false 1 ++ [isoX false 0] ++ claspWord ++ [isoN 1]) :=
  ⟨[(8, .zig 2 true, true), (9, .capSlide 3 true false, true),
    (8, .exch (.cup, 2) (.cross true, 2), false), (7, .exch (.cap, 2) (.cross true, 4), false),
    (4, .exch (.cup, 2) (.cup, 2), true), (5, .cupSlide 3 true true, false),
    (5, .zig 2 false, false), (4, .exch (.cup, 2) (.cup, 2), true),
    (7, .exch (.cross true, 1) (.cap, 4), true),
    (6, .exch (.cross true, 1) (.cross true, 3), true),
    (5, .exch (.cross true, 1) (.cup, 4), true), (8, .exch (.cross true, 1) (.cap, 4), true),
    (7, .exch (.cross true, 1) (.cross true, 3), true),
    (6, .exch (.cross true, 1) (.cup, 4), true), (9, .exch (.cap, 0) (.cap, 4), true),
    (8, .exch (.cap, 0) (.cross true, 3), true), (7, .exch (.cap, 0) (.cup, 4), true),
    (10, .capSlide 1 false true, true), (9, .r2 1 true, false),
    (10, .exch (.cap, 1) (.cap, 3), false), (10, .capSlide 2 true true, true),
    (9, .r2 2 false, false), (7, .exch (.cap, 0) (.cup, 4), false),
    (8, .exch (.cap, 0) (.cross true, 5), false), (9, .exch (.cap, 0) (.cap, 4), false),
    (6, .exch (.cross true, 1) (.cup, 4), false),
    (7, .exch (.cross true, 1) (.cross true, 5), false),
    (8, .exch (.cross true, 1) (.cap, 4), false), (5, .exch (.cross true, 1) (.cup, 4), false),
    (6, .exch (.cross true, 1) (.cross true, 5), false),
    (7, .exch (.cross true, 1) (.cap, 4), false), (4, .exch (.cup, 2) (.cup, 2), false),
    (5, .exch (.cup, 2) (.cross true, 3), false), (6, .exch (.cup, 2) (.cap, 2), false),
    (3, .exch (.cross false, 0) (.cup, 2), false),
    (4, .exch (.cross false, 0) (.cross true, 3), false),
    (5, .exch (.cross false, 0) (.cap, 2), false), (2, .exch (.cap, 1) (.cup, 4), false),
    (3, .exch (.cap, 1) (.cross true, 5), false), (4, .exch (.cap, 1) (.cap, 4), false),
    (1, .exch (.cross false, 2) (.cup, 4), false),
    (2, .exch (.cross false, 2) (.cross true, 5), false),
    (3, .exch (.cross false, 2) (.cap, 4), false), (0, .exch (.cup, 1) (.cup, 2), false),
    (1, .exch (.cup, 1) (.cross true, 3), false), (2, .exch (.cup, 1) (.cap, 2), false)
    ], by decide⟩

/-- Macro `CUPL`: a left curl on the return strand turns around the first cup. -/
theorem morseReach_isoPark_cupL :
    MorseReach 1 ([isoU 1] ++ isoCurlL true 2)
      ([isoU 1] ++ isoCurlR true 1) :=
  ⟨[(3, .r2 1 false, true), (3, .r2 2 true, true), (1, .cupSlide 2 true false, false),
    (0, .exch (.cup, 1) (.cup, 1), false), (1, .cupSlide 1 false false, false)], by decide⟩

/-- Macro `PastPair`: the travelling curl passes a negative full twist. -/
theorem morseReach_isoPark_pastPair :
    MorseReach 3 (isoCurlR true 1 ++ [isoX false 0, isoX false 0])
      ([isoX false 0, isoX false 0] ++ isoCurlR true 1) :=
  ⟨[(0, .cupSlide 1 false false, true), (2, .r2 1 false, false),
    (2, .exch (.cross false, 0) (.cap, 2), true),
    (1, .exch (.cross false, 0) (.cross false, 2), true), (3, .capSlide 1 false true, true),
    (2, .r3 1 false, true), (0, .cupSlide 0 false true, false),
    (0, .exch (.cup, 0) (.cross false, 0), false), (3, .r2 0 false, true),
    (1, .cupSlide 0 false false, false), (1, .cupSlide 0 false false, true),
    (3, .r2 0 false, false), (3, .capSlide 1 false false, true), (2, .r3 1 false, false),
    (1, .exch (.cup, 0) (.cross false, 0), false), (5, .exch (.cross false, 0) (.cap, 2), true),
    (4, .exch (.cross false, 0) (.cross false, 2), true), (2, .cupSlide 0 false false, false),
    (4, .r2 1 false, true), (2, .cupSlide 1 false false, false)], by decide⟩

/-- Macro `PastOdd`: the travelling curl passes a half twist and changes strands. -/
theorem morseReach_isoPark_pastOdd :
    MorseReach 3 (isoCurlR true 1 ++ [isoX false 0])
      ([isoX false 0] ++ isoCurlR true 0) :=
  ⟨[(0, .cupSlide 1 false false, true), (2, .r2 1 false, false),
    (2, .exch (.cross false, 0) (.cap, 2), true),
    (1, .exch (.cross false, 0) (.cross false, 2), true), (3, .capSlide 1 false true, true),
    (2, .r3 1 false, true), (0, .cupSlide 0 false true, false),
    (0, .exch (.cup, 0) (.cross false, 0), false), (3, .r2 0 false, true),
    (1, .cupSlide 0 false false, false)], by decide⟩

/-- Macro `Cancel`: the two curls cancel at the clasp (one `kink`). -/
theorem morseReach_isoPark_cancel :
    MorseReach 3 (isoCurlR true 0 ++ isoCurlL false 1 ++ [isoX false 0] ++ claspWord)
      ([isoX false 0] ++ claspWord) :=
  ⟨[(2, .exch (.cap, 1) (.cup, 3), false), (1, .exch (.cross true, 0) (.cup, 3), false),
    (0, .exch (.cup, 1) (.cup, 1), false), (3, .exch (.cap, 1) (.cross false, 4), false),
    (2, .exch (.cross true, 0) (.cross false, 4), false),
    (1, .exch (.cup, 1) (.cross false, 2), false), (4, .exch (.cap, 1) (.cap, 3), false),
    (3, .exch (.cross true, 0) (.cap, 3), false), (2, .exch (.cup, 1) (.cap, 1), false),
    (3, .cupSlide 0 false false, true), (5, .r2 0 false, false),
    (5, .capSlide 1 false false, true), (4, .r3 1 false, false),
    (3, .exch (.cup, 0) (.cross false, 0), false), (7, .exch (.cross false, 0) (.cap, 2), true),
    (6, .exch (.cross false, 0) (.cross false, 2), true), (4, .cupSlide 0 false false, false),
    (6, .r2 1 false, true), (4, .cupSlide 1 false false, false),
    (6, .exch (.cap, 2) (.cup, 4), false), (5, .exch (.cross true, 1) (.cup, 4), false),
    (4, .exch (.cup, 2) (.cup, 2), false), (7, .capSlide 2 true false, true),
    (6, .exch (.cross true, 1) (.cross true, 3), false),
    (9, .exch (.cross true, 1) (.cap, 3), true), (7, .r3 1 true, false),
    (5, .cupSlide 2 true false, false), (5, .exch (.cross true, 1) (.cup, 3), true),
    (8, .exch (.cross true, 1) (.cap, 3), true), (9, .capSlide 2 true true, true),
    (7, .r3 1 true, true), (9, .exch (.cross true, 1) (.cross true, 3), false),
    (6, .exch (.cross true, 1) (.cup, 3), true), (7, .cupSlide 2 true true, false),
    (7, .zig 1 true, true), (7, .cupSlide 0 true false, true),
    (9, .exch (.cross true, 0) (.cap, 2), false), (10, .exch (.cross true, 0) (.cup, 2), false),
    (13, .exch (.cap, 0) (.cap, 2), true), (11, .capSlide 0 true true, false),
    (10, .zig 1 false, false), (9, .exch (.cap, 0) (.cap, 2), true),
    (6, .exch (.cup, 0) (.cross true, 1), true),
    (7, .exch (.cross true, 1) (.cross true, 3), true),
    (8, .exch (.cap, 0) (.cross true, 3), true), (5, .exch (.cup, 0) (.cross true, 1), true),
    (6, .exch (.cross true, 1) (.cross true, 3), true),
    (7, .exch (.cap, 0) (.cross true, 3), true), (4, .exch (.cup, 0) (.cup, 2), true),
    (5, .exch (.cross true, 1) (.cup, 4), true), (6, .exch (.cap, 0) (.cup, 4), true),
    (6, .r2 0 true, true), (4, .cupSlide 0 true false, false), (4, .cupSlide 1 false true, true),
    (6, .exch (.cross false, 0) (.cross false, 2), true),
    (7, .exch (.cap, 0) (.cross false, 2), true), (3, .exch (.cross false, 0) (.cup, 2), false),
    (4, .r3 0 false, false), (5, .capSlide 0 false true, false), (3, .cupSlide 1 true false, true),
    (5, .r2 1 true, false), (3, .kink 1 true, true), (1, .r2 1 true, true),
    (2, .capSlide 1 false true, false), (2, .exch (.cup, 2) (.cap, 2), true),
    (2, .cupSlide 2 true true, true), (1, .exch (.cross true, 1) (.cup, 3), false),
    (0, .exch (.cup, 1) (.cup, 1), false), (5, .exch (.cross true, 1) (.cap, 4), true),
    (4, .exch (.cross true, 1) (.cross true, 3), true), (2, .r3 1 true, false),
    (6, .exch (.cap, 2) (.cap, 4), true), (4, .capSlide 2 true true, false),
    (1, .cupSlide 1 true false, false), (1, .zig 2 true, false), (0, .zig 1 true, false),
    (2, .capSlide 1 true true, true), (1, .r2 1 false, false),
    (2, .exch (.cap, 1) (.cup, 3), false), (2, .cupSlide 2 true false, true),
    (1, .exch (.cup, 2) (.cross true, 2), true), (0, .exch (.cup, 2) (.cup, 2), true),
    (5, .exch (.cap, 1) (.cross true, 4), false),
    (4, .exch (.cross true, 2) (.cross true, 4), false), (2, .r3 3 true, true),
    (6, .exch (.cap, 1) (.cap, 3), false), (4, .capSlide 2 true false, false),
    (1, .cupSlide 3 true true, false), (1, .zig 2 false, false), (0, .zig 1 false, false)
    ], by decide⟩

end AJConjecture
