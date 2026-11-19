import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkDefs

/-!
# Stage C by ports: fixed macros for the curls on the right edge

Checked by `decide` (move lists found by search, `SCR/ISO2/tools/msearch.py`, or copied from the
library: `CANPM`, `CANMP`, `TW` of `AJFamily.Skein.TorusPhaseTwoCurls`, valid on two strands).
Both sides have equal Kauffman-bracket operators at thickness one and two
(`SCR/ISO2/tools/macros.py`).
-/

namespace AJConjecture

/-- A positive and a negative right-edge curl cancel (library `CANPM`, one `kink`). -/
theorem morseReach_isoPark_PN :
    MorseReach 2 (isoBeadsWord [.p, .n]) [] :=
  ⟨[(3, .kink 1 false, true), (1, .r2 1 false, true), (2, .capSlide 1 true true, false),
    (2, .exch (.cup, 2) (.cap, 2), true), (2, .cupSlide 2 false true, true),
    (1, .exch (.cross false, 1) (.cup, 3), false), (0, .exch (.cup, 1) (.cup, 1), false),
    (5, .exch (.cross false, 1) (.cap, 4), true),
    (4, .exch (.cross false, 1) (.cross false, 3), true), (2, .r3 1 false, false),
    (6, .exch (.cap, 2) (.cap, 4), true), (4, .capSlide 2 false true, false),
    (1, .cupSlide 1 false false, false), (1, .zig 2 true, false), (0, .zig 1 true, false),
    (2, .capSlide 1 false true, true), (1, .r2 1 true, false),
    (2, .exch (.cap, 1) (.cup, 3), false), (2, .cupSlide 2 false false, true),
    (1, .exch (.cup, 2) (.cross false, 2), true), (0, .exch (.cup, 2) (.cup, 2), true),
    (5, .exch (.cap, 1) (.cross false, 4), false),
    (4, .exch (.cross false, 2) (.cross false, 4), false), (2, .r3 3 false, true),
    (6, .exch (.cap, 1) (.cap, 3), false), (4, .capSlide 2 false false, false),
    (1, .cupSlide 3 false true, false), (1, .zig 2 false, false), (0, .zig 1 false, false)
    ], by decide⟩

/-- A negative and a positive right-edge curl cancel (library `CANMP`, one `kink`). -/
theorem morseReach_isoPark_NP :
    MorseReach 2 (isoBeadsWord [.n, .p]) [] :=
  ⟨[(3, .kink 1 true, true), (1, .r2 1 true, true), (2, .capSlide 1 false true, false),
    (2, .exch (.cup, 2) (.cap, 2), true), (2, .cupSlide 2 true true, true),
    (1, .exch (.cross true, 1) (.cup, 3), false), (0, .exch (.cup, 1) (.cup, 1), false),
    (5, .exch (.cross true, 1) (.cap, 4), true),
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

/-- A positive right-edge curl passes a twist (library `TW`). -/
theorem morseReach_isoPark_TP :
    MorseReach 2 (isoBeadsWord [.t, .p]) (isoBeadsWord [.p, .t]) :=
  ⟨[(2, .cupSlide 0 false false, true), (1, .exch (.cup, 0) (.cross false, 0), true),
    (5, .r2 1 false, true), (6, .capSlide 1 true true, false), (3, .r3 0 false, true),
    (5, .exch (.cross false, 0) (.cap, 2), false),
    (2, .exch (.cross false, 0) (.cross false, 2), true), (3, .capSlide 1 false false, false),
    (3, .capSlide 0 true true, true), (2, .r2 0 false, false), (3, .r2 0 true, true),
    (1, .cupSlide 0 true false, false), (1, .cupSlide 1 false true, true),
    (3, .exch (.cross false, 0) (.cross false, 2), true),
    (4, .exch (.cap, 0) (.cross false, 2), true), (0, .exch (.cross false, 0) (.cup, 2), false),
    (1, .r3 0 false, false), (2, .capSlide 0 false true, false), (0, .cupSlide 1 true false, true),
    (2, .r2 1 true, false)], by decide⟩

/-- A negative right-edge curl passes a twist. -/
theorem morseReach_isoPark_NT :
    MorseReach 2 (isoBeadsWord [.n, .t]) (isoBeadsWord [.t, .n]) :=
  ⟨[(2, .capSlide 0 false true, true), (1, .exch (.cross false, 0) (.cross false, 2), true),
    (4, .exch (.cap, 0) (.cross false, 2), false), (2, .r3 1 false, true),
    (0, .cupSlide 0 false true, false), (0, .exch (.cup, 0) (.cross false, 0), false),
    (3, .exch (.cap, 0) (.cross false, 2), false), (4, .capSlide 0 false false, true),
    (2, .r3 1 false, false), (4, .exch (.cross false, 0) (.cross false, 2), true),
    (1, .exch (.cup, 0) (.cross false, 0), false), (2, .cupSlide 0 false false, false)], by decide⟩

end AJConjecture
