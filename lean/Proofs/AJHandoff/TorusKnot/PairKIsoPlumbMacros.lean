import Mathlib
import AJHandoff.TorusKnot.PairKIsoPlumbDefs

/-!
# The macros `CAPM` and `WIN` (copies of the library's private macros)

`AJFamily.Skein.TorusPhaseTwoCurls` proves these two certificates as private theorems
(`morseReach_curlsCAPM`, 8 moves; `morseReach_curlsWIN`, 161 moves, two `kink`s). They are restated
here with the same words; the proofs copy the move lists of the library and run `decide`.
-/

namespace AJConjecture

/-- Macro `CAPM`: a negative left curl goes around the following cap. -/
theorem morseReach_isoCAPM :
    MorseReach 2 isoXTip [isoU 2, isoX false 1, isoN 2, isoN 0] :=
  ⟨[(2, .exch (.cap, 0) (.cap, 2), false), (3, .zig 1 false, true),
    (4, .capSlide 0 false true, true), (6, .exch (.cap, 0) (.cap, 2), false),
    (3, .exch (.cross false, 0) (.cup, 2), true), (2, .exch (.cross false, 0) (.cap, 2), true),
    (0, .cupSlide 0 false false, false), (0, .zig 1 true, false)], by decide⟩

/-- Macro `WIN`: the X-tip curl cancels the curl after the doubled crossing and the clasp absorbs
the fold curl. -/
theorem morseReach_isoWIN : MorseReach 3 isoWinL isoWinR :=
  ⟨[(18, .exch (.cap, 5) (.cap, 7), false), (19, .zig 6 false, true),
    (20, .capSlide 5 false true, true), (22, .exch (.cap, 5) (.cap, 7), false),
    (19, .exch (.cross false, 5) (.cup, 7), true),
    (18, .exch (.cross false, 5) (.cap, 7), true), (16, .cupSlide 5 false false, false),
    (16, .zig 6 true, false), (15, .exch (.cross false, 5) (.cup, 7), false),
    (15, .cupSlide 6 false false, true), (17, .r3 5 false, true),
    (19, .exch (.cross false, 5) (.cap, 7), false),
    (16, .exch (.cross false, 5) (.cross false, 7), true),
    (17, .capSlide 6 false false, false), (14, .exch (.cap, 5) (.cup, 8), false),
    (15, .exch (.cap, 5) (.cross false, 7), false), (16, .exch (.cap, 5) (.cap, 8), false),
    (13, .exch (.cross false, 4) (.cup, 8), false),
    (14, .exch (.cross false, 4) (.cross false, 7), false),
    (15, .exch (.cross false, 4) (.cap, 8), false), (12, .exch (.cup, 5) (.cup, 6), false),
    (13, .exch (.cup, 5) (.cross false, 5), false), (14, .exch (.cup, 5) (.cap, 6), false),
    (11, .exch (.cross false, 4) (.cup, 6), false), (11, .cupSlide 5 false false, true),
    (13, .r3 4 false, true), (15, .exch (.cross false, 4) (.cap, 6), false),
    (12, .exch (.cross false, 4) (.cross false, 6), true),
    (13, .capSlide 5 false false, false), (10, .exch (.cup, 5) (.cross true, 5), true),
    (11, .exch (.cross false, 4) (.cross true, 7), true),
    (12, .exch (.cap, 5) (.cross true, 7), true), (9, .exch (.cup, 5) (.cup, 6), true),
    (10, .exch (.cross false, 4) (.cup, 8), true), (11, .exch (.cap, 5) (.cup, 8), true),
    (8, .exch (.cap, 1) (.cup, 7), false), (9, .exch (.cap, 1) (.cross false, 6), false),
    (10, .exch (.cap, 1) (.cap, 7), false), (7, .exch (.cross true, 2) (.cup, 7), false),
    (8, .exch (.cross true, 2) (.cross false, 6), false),
    (9, .exch (.cross true, 2) (.cap, 7), false), (6, .exch (.cup, 1) (.cup, 5), false),
    (7, .exch (.cup, 1) (.cross false, 4), false), (8, .exch (.cup, 1) (.cap, 5), false),
    (5, .exch (.cross true, 1) (.cup, 5), false),
    (6, .exch (.cross true, 1) (.cross false, 4), false),
    (7, .exch (.cross true, 1) (.cap, 5), false), (4, .exch (.cross true, 0) (.cup, 5), false),
    (5, .exch (.cross true, 0) (.cross false, 4), false),
    (6, .exch (.cross true, 0) (.cap, 5), false), (3, .exch (.cross true, 2) (.cup, 5), false),
    (4, .exch (.cross true, 2) (.cross false, 4), false),
    (5, .exch (.cross true, 2) (.cap, 5), false), (2, .exch (.cross true, 1) (.cup, 5), false),
    (3, .exch (.cross true, 1) (.cross false, 4), false),
    (4, .exch (.cross true, 1) (.cap, 5), false), (1, .exch (.cup, 3) (.cup, 3), false),
    (2, .zig 3 false, true), (2, .cupSlide 4 false true, true),
    (1, .exch (.cup, 3) (.cup, 3), false), (4, .exch (.cap, 3) (.cross false, 5), true),
    (5, .exch (.cup, 3) (.cross false, 3), true), (6, .capSlide 4 false false, false),
    (5, .zig 3 true, false), (4, .exch (.cross true, 1) (.cap, 3), true),
    (3, .exch (.cross true, 1) (.cross false, 4), true),
    (2, .exch (.cross true, 1) (.cup, 3), true), (5, .r2 3 false, true),
    (3, .cupSlide 3 false false, false), (5, .capSlide 2 true true, true),
    (4, .r3 2 true, true), (3, .exch (.cross true, 2) (.cup, 4), true),
    (7, .exch (.cap, 2) (.cross true, 4), false),
    (6, .exch (.cross true, 2) (.cross true, 4), false), (4, .cupSlide 3 true true, false),
    (4, .cupSlide 2 false false, true), (6, .r2 2 false, false),
    (6, .exch (.cross true, 0) (.cap, 2), true),
    (5, .exch (.cross true, 0) (.cross false, 3), true),
    (4, .exch (.cross true, 0) (.cup, 2), true), (7, .r2 2 false, true),
    (5, .cupSlide 2 false false, false), (7, .capSlide 1 true true, true),
    (6, .r3 1 true, true), (5, .exch (.cross true, 1) (.cup, 3), true),
    (9, .exch (.cap, 1) (.cross true, 3), false),
    (8, .exch (.cross true, 1) (.cross true, 3), false), (6, .cupSlide 2 true true, false),
    (6, .cupSlide 1 false false, true), (8, .r2 1 false, false), (9, .kink 1 true, true),
    (7, .r2 1 true, true), (8, .capSlide 1 false true, false),
    (8, .exch (.cup, 2) (.cap, 2), true), (8, .cupSlide 2 true true, true),
    (7, .exch (.cross true, 1) (.cup, 3), false), (6, .exch (.cup, 1) (.cup, 1), false),
    (11, .exch (.cross true, 1) (.cap, 4), true),
    (10, .exch (.cross true, 1) (.cross true, 3), true), (8, .r3 1 true, false),
    (12, .exch (.cap, 2) (.cap, 4), true), (10, .capSlide 2 true true, false),
    (7, .cupSlide 1 true false, false), (7, .zig 2 true, false), (6, .zig 1 true, false),
    (8, .capSlide 1 true true, true), (7, .r2 1 false, false),
    (8, .exch (.cap, 1) (.cup, 3), false), (8, .cupSlide 2 true false, true),
    (7, .exch (.cup, 2) (.cross true, 2), true), (6, .exch (.cup, 2) (.cup, 2), true),
    (11, .exch (.cap, 1) (.cross true, 4), false),
    (10, .exch (.cross true, 2) (.cross true, 4), false), (8, .r3 3 true, true),
    (12, .exch (.cap, 1) (.cap, 3), false), (10, .capSlide 2 true false, false),
    (7, .cupSlide 3 true true, false), (7, .zig 2 false, false), (6, .zig 1 false, false),
    (6, .cupSlide 5 false false, true), (8, .r2 5 false, false),
    (7, .exch (.cross false, 4) (.cross false, 6), true),
    (8, .exch (.cup, 5) (.cross false, 6), true),
    (9, .exch (.cross false, 4) (.cross false, 8), true),
    (10, .exch (.cap, 5) (.cross false, 8), true), (8, .zig 4 true, true),
    (9, .zig 5 true, true), (9, .cupSlide 4 true false, true),
    (12, .capSlide 5 true true, true), (14, .exch (.cap, 5) (.cap, 7), false),
    (10, .r3 4 true, true), (12, .exch (.cross true, 4) (.cross true, 6), false),
    (13, .exch (.cross true, 4) (.cap, 7), false), (8, .exch (.cup, 4) (.cup, 4), true),
    (9, .exch (.cross true, 4) (.cup, 6), true), (10, .cupSlide 5 true true, false),
    (10, .exch (.cup, 5) (.cap, 5), false), (10, .capSlide 4 false true, true),
    (9, .r2 4 true, false), (11, .kink 4 true, false),
    (7, .exch (.cup, 4) (.cross false, 4), true), (6, .exch (.cup, 4) (.cup, 5), true),
    (9, .r2 4 true, true), (10, .capSlide 4 false true, false),
    (8, .exch (.cross true, 4) (.cross false, 6), true),
    (7, .exch (.cross true, 4) (.cup, 7), true), (13, .r2 6 false, true),
    (11, .r3 5 false, true), (10, .exch (.cap, 5) (.cross false, 7), false),
    (8, .cupSlide 6 false true, false), (8, .zig 5 false, false),
    (7, .exch (.cross true, 4) (.cross false, 6), false),
    (6, .exch (.cup, 4) (.cross false, 4), false), (7, .cupSlide 4 true true, true),
    (8, .r3 4 true, false), (10, .r2 5 true, false),
    (9, .exch (.cross true, 4) (.cross true, 6), false), (7, .cupSlide 5 true true, true),
    (9, .r3 5 true, true), (11, .capSlide 4 true false, false),
    (10, .exch (.cap, 4) (.cross true, 6), true)], by decide⟩

/-- The left side of `WIN` fits on three strands. -/
theorem morseFits_isoWinL : morseFits 3 isoWinL = true := by
  decide

end AJConjecture
