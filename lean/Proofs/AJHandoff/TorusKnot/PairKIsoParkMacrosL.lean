import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkDefs

/-!
# Stage C by ports: fixed macros for the curls on the left edge

The left-edge curls `lp`, `ln` (right curls on the strand `0`) pass a twist, commute with the
right-edge curls, and cancel by one `kink`. Checked by `decide`; move lists found by search
(`SCR/ISO2/tools/msearch.py`); regular isotopies (equal operators at thickness one and two,
equal arcs and rotation numbers).
-/

namespace AJConjecture

/-- A positive left-edge curl passes a twist. -/
theorem morseReach_isoPark_LPT :
    MorseReach 2 (isoBeadsWord [.lp, .t]) (isoBeadsWord [.t, .lp]) :=
  ⟨[(2, .capSlide 1 false false, true), (1, .exch (.cross true, 0) (.cross false, 2), false),
    (4, .exch (.cross false, 0) (.cap, 2), true), (5, .exch (.cross false, 0) (.cap, 2), true),
    (5, .r2 1 false, true), (3, .r3 0 false, true), (2, .r2 0 true, false),
    (0, .cupSlide 1 false false, false), (2, .r2 0 false, true),
    (0, .exch (.cross false, 0) (.cup, 2), true), (1, .exch (.cross false, 0) (.cup, 2), true),
    (2, .cupSlide 1 true false, true), (4, .r3 0 true, true), (6, .r2 0 true, false),
    (3, .exch (.cross true, 0) (.cross true, 2), true), (4, .capSlide 1 true false, false)
    ], by decide⟩

/-- A negative left-edge curl passes a twist. -/
theorem morseReach_isoPark_LNT :
    MorseReach 2 (isoBeadsWord [.ln, .t]) (isoBeadsWord [.t, .ln]) :=
  ⟨[(2, .capSlide 1 false false, true), (1, .exch (.cross false, 0) (.cross false, 2), false),
    (4, .exch (.cross false, 0) (.cap, 2), true), (2, .r3 0 false, false),
    (0, .cupSlide 1 false false, false), (0, .exch (.cross false, 0) (.cup, 2), true),
    (3, .exch (.cross false, 0) (.cap, 2), true), (4, .capSlide 1 false true, true),
    (2, .r3 0 false, true), (1, .exch (.cross false, 0) (.cup, 2), true),
    (2, .cupSlide 1 true false, true), (4, .r2 1 true, false),
    (4, .exch (.cross false, 0) (.cross false, 2), false), (3, .r2 2 true, false)], by decide⟩

/-- A positive left-edge curl passes a positive right-edge curl. -/
theorem morseReach_isoPark_LPP :
    MorseReach 2 (isoBeadsWord [.lp, .p]) (isoBeadsWord [.p, .lp]) :=
  ⟨[(2, .exch (.cap, 1) (.cup, 3), false), (1, .exch (.cross true, 0) (.cup, 3), false),
    (0, .exch (.cup, 1) (.cup, 1), false), (3, .exch (.cap, 1) (.cross true, 4), false),
    (2, .exch (.cross true, 0) (.cross true, 4), false), (4, .exch (.cap, 1) (.cap, 3), false),
    (3, .exch (.cross true, 0) (.cap, 3), false), (1, .exch (.cup, 1) (.cross true, 2), false),
    (2, .exch (.cup, 1) (.cap, 1), false)], by decide⟩

/-- A positive left-edge curl passes a negative right-edge curl. -/
theorem morseReach_isoPark_LPN :
    MorseReach 2 (isoBeadsWord [.lp, .n]) (isoBeadsWord [.n, .lp]) :=
  ⟨[(2, .exch (.cap, 1) (.cup, 3), false), (1, .exch (.cross true, 0) (.cup, 3), false),
    (0, .exch (.cup, 1) (.cup, 1), false), (3, .exch (.cap, 1) (.cross false, 4), false),
    (2, .exch (.cross true, 0) (.cross false, 4), false), (4, .exch (.cap, 1) (.cap, 3), false),
    (3, .exch (.cross true, 0) (.cap, 3), false), (1, .exch (.cup, 1) (.cross false, 2), false),
    (2, .exch (.cup, 1) (.cap, 1), false)], by decide⟩

/-- A negative and a positive left-edge curl cancel (`kink`). -/
theorem morseReach_isoPark_LNLP :
    MorseReach 2 (isoBeadsWord [.ln, .lp]) [] :=
  ⟨[(0, .kink 0 false, false)], by decide⟩

end AJConjecture
