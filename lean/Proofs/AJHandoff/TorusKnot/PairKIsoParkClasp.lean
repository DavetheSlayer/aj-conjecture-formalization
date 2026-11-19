import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkDefs

/-!
# Stage C by ports: a left-edge curl crosses to the right edge through the clasp

At the clasp `isoClaspU = +0 · claspWord · −0` (band frame) the two edges of the band are joined:
below it by the cap of the clasp, above it by its cup. A left-edge curl next to the clasp
travels along that arc onto the right edge, on either side (`morseReach_isoPark_CSLP`,
`morseReach_isoPark_LPCS`, `morseReach_isoPark_LNCS`). Each move list was found by a chained
search through the waypoints "curl passes a crossing / turns around the cup or cap of the clasp"
(`SCR/ISO2/tools/chains.py`); regular isotopies.
-/

namespace AJConjecture

/-- After the clasp, a positive left-edge curl moves to the right edge. -/
theorem morseReach_isoPark_CSLP :
    MorseReach 2 (isoBeadsWord [.cs, .lp]) (isoBeadsWord [.cs, .p]) :=
  ⟨[(8, .capSlide 1 true false, true), (7, .exch (.cross true, 0) (.cross true, 2), false),
    (10, .r2 0 true, true), (11, .exch (.cross false, 0) (.cap, 2), false), (8, .r3 0 true, false),
    (6, .cupSlide 1 true false, false), (6, .exch (.cross true, 0) (.cup, 2), true),
    (5, .r2 0 false, false), (4, .exch (.cap, 0) (.cup, 4), false),
    (5, .exch (.cap, 0) (.cross true, 3), false), (6, .exch (.cap, 0) (.cap, 4), false),
    (3, .exch (.cross true, 1) (.cup, 4), false),
    (4, .exch (.cross true, 1) (.cross true, 3), false),
    (5, .exch (.cross true, 1) (.cap, 4), false), (2, .exch (.cross true, 1) (.cup, 4), false),
    (3, .exch (.cross true, 1) (.cross true, 3), false),
    (4, .exch (.cross true, 1) (.cap, 4), false), (1, .exch (.cup, 2) (.cup, 2), false),
    (5, .zig 3 false, true), (6, .capSlide 2 true true, true),
    (5, .exch (.cross true, 2) (.cup, 4), true), (4, .exch (.cross true, 2) (.cap, 4), true),
    (2, .cupSlide 2 true false, false), (2, .zig 3 true, false),
    (1, .exch (.cup, 2) (.cup, 2), false), (2, .cupSlide 1 false false, true),
    (6, .capSlide 1 true true, true), (5, .exch (.cross true, 1) (.cross true, 3), true),
    (8, .exch (.cap, 1) (.cross true, 3), false), (4, .r2 1 false, false), (4, .r3 2 true, true),
    (3, .r2 2 false, false), (2, .exch (.cup, 1) (.cross true, 1), false),
    (5, .exch (.cap, 1) (.cross true, 3), false), (6, .capSlide 1 true false, true),
    (4, .r3 2 true, false), (6, .exch (.cross true, 1) (.cross true, 3), true),
    (3, .exch (.cup, 1) (.cross true, 1), false), (4, .cupSlide 1 true false, false),
    (6, .exch (.cap, 0) (.cap, 2), true), (5, .exch (.cap, 0) (.cross true, 3), true),
    (4, .exch (.cap, 0) (.cup, 2), true), (7, .exch (.cap, 0) (.cross false, 2), false),
    (8, .capSlide 0 false false, true), (9, .r2 2 false, true), (7, .r3 1 false, true),
    (10, .exch (.cross false, 0) (.cross true, 2), true), (6, .r2 1 true, false),
    (5, .exch (.cup, 0) (.cross false, 0), false), (6, .cupSlide 0 false false, false)], by decide⟩

/-- Before the clasp, a positive left-edge curl moves to the right edge. -/
theorem morseReach_isoPark_LPCS :
    MorseReach 2 (isoBeadsWord [.lp, .cs]) (isoBeadsWord [.p, .cs]) :=
  ⟨[(2, .capSlide 1 true false, true), (1, .exch (.cross true, 0) (.cross true, 2), false),
    (4, .exch (.cross true, 0) (.cap, 2), true), (2, .r3 0 true, false),
    (0, .cupSlide 1 true false, false), (0, .exch (.cross true, 0) (.cup, 2), true),
    (3, .exch (.cap, 2) (.cup, 4), false), (2, .exch (.cross true, 1) (.cup, 4), false),
    (1, .exch (.cup, 2) (.cup, 2), false), (4, .capSlide 2 true false, true),
    (3, .exch (.cross true, 1) (.cross true, 3), false),
    (6, .exch (.cross true, 1) (.cap, 3), true), (4, .r3 1 true, false),
    (2, .cupSlide 2 true false, false), (2, .exch (.cross true, 1) (.cup, 3), true),
    (5, .exch (.cross true, 1) (.cap, 3), true), (6, .capSlide 2 true true, true),
    (4, .r3 1 true, true), (3, .exch (.cross true, 1) (.cup, 3), true),
    (4, .cupSlide 2 false false, true), (6, .r2 2 false, false),
    (6, .exch (.cross true, 1) (.cross true, 3), false), (5, .r2 3 false, false),
    (4, .zig 1 true, true), (4, .cupSlide 0 true false, true),
    (6, .exch (.cross true, 0) (.cap, 2), false), (10, .exch (.cap, 0) (.cap, 2), true),
    (7, .exch (.cross true, 0) (.cup, 2), false), (8, .capSlide 0 true true, false),
    (7, .zig 1 false, false), (6, .exch (.cap, 0) (.cap, 2), true),
    (3, .exch (.cup, 0) (.cross true, 1), true), (2, .exch (.cup, 0) (.cross true, 1), true),
    (4, .exch (.cross true, 1) (.cross true, 3), true),
    (5, .exch (.cap, 0) (.cross true, 3), true),
    (3, .exch (.cross true, 1) (.cross true, 3), true),
    (4, .exch (.cap, 0) (.cross true, 3), true), (1, .exch (.cup, 0) (.cup, 2), true),
    (2, .exch (.cross true, 1) (.cup, 4), true), (3, .exch (.cap, 0) (.cup, 4), true),
    (0, .exch (.cup, 0) (.cross true, 0), true), (1, .r2 1 false, true), (2, .r3 1 true, false),
    (2, .r2 0 false, true), (6, .exch (.cap, 0) (.cross true, 2), true),
    (3, .exch (.cross true, 0) (.cross true, 2), false), (4, .capSlide 0 true true, false),
    (0, .cupSlide 0 false false, false)], by decide⟩

/-- Before the clasp, a negative left-edge curl moves to the right edge. -/
theorem morseReach_isoPark_LNCS :
    MorseReach 2 (isoBeadsWord [.ln, .cs]) (isoBeadsWord [.n, .cs]) :=
  ⟨[(2, .capSlide 1 true false, true), (4, .exch (.cross true, 0) (.cap, 2), true),
    (5, .r2 1 true, true), (3, .r3 0 true, true),
    (2, .exch (.cross true, 0) (.cross true, 2), true), (1, .r2 0 false, false),
    (0, .cupSlide 1 true false, false), (0, .exch (.cross true, 0) (.cup, 2), true),
    (3, .exch (.cap, 2) (.cup, 4), false), (2, .exch (.cross false, 1) (.cup, 4), false),
    (1, .exch (.cup, 2) (.cup, 2), false), (4, .capSlide 2 true false, true),
    (6, .exch (.cross true, 1) (.cap, 3), true), (7, .r2 2 true, true), (5, .r3 1 true, true),
    (4, .exch (.cross true, 1) (.cross true, 3), true), (3, .r2 1 false, false),
    (2, .cupSlide 2 true false, false), (2, .exch (.cross true, 1) (.cup, 3), true),
    (3, .r2 1 true, true), (4, .exch (.cross false, 1) (.cup, 3), false),
    (4, .cupSlide 2 false false, true), (6, .r3 1 false, true),
    (9, .exch (.cross true, 1) (.cap, 3), true), (8, .r2 1 false, false),
    (5, .exch (.cross false, 1) (.cross false, 3), true), (6, .capSlide 2 false false, false),
    (4, .zig 1 true, true), (4, .cupSlide 0 false false, true),
    (6, .exch (.cross false, 0) (.cap, 2), false), (10, .exch (.cap, 0) (.cap, 2), true),
    (7, .exch (.cross false, 0) (.cup, 2), false), (8, .capSlide 0 false true, false),
    (7, .zig 1 false, false), (6, .exch (.cap, 0) (.cap, 2), true),
    (3, .exch (.cup, 0) (.cross true, 1), true), (2, .exch (.cup, 0) (.cross true, 1), true),
    (4, .exch (.cross false, 1) (.cross true, 3), true),
    (5, .exch (.cap, 0) (.cross true, 3), true),
    (3, .exch (.cross false, 1) (.cross true, 3), true),
    (4, .exch (.cap, 0) (.cross true, 3), true), (1, .exch (.cup, 0) (.cup, 2), true),
    (2, .exch (.cross false, 1) (.cup, 4), true), (3, .exch (.cap, 0) (.cup, 4), true),
    (0, .exch (.cup, 0) (.cross true, 0), true), (3, .r2 2 false, true),
    (4, .exch (.cap, 0) (.cross true, 2), true), (4, .capSlide 0 false false, true),
    (2, .r3 1 false, false), (4, .exch (.cross false, 0) (.cross false, 2), true),
    (1, .r2 2 true, false), (0, .cupSlide 0 false false, false)], by decide⟩

end AJConjecture
