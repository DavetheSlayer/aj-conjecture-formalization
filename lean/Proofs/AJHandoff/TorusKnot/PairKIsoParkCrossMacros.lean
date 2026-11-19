import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkDefs

/-!
# Stage C by ports: small macros for the twist crossing the clasp

Right curls on the right edge (`isoCurlR s 1`) appear when a twist is written as a doubled curl
and two edge curls (`PairKIsoParkCross`). They commute with right curls on the left edge
(`morseReach_isoPark_swapP`, `morseReach_isoPark_swapN`: exchanges only) and turn into the
right-edge curls `p`, `n` with one `kink` (`morseReach_isoPark_RP`, `morseReach_isoPark_RN`:
the library macro `CANMP` (resp. `CANPM`) read backwards inserts `n p` (resp. `p n`), and the
second half of `CANPM` (resp. `CANMP`), a planar Whitney cancellation, removes the right curl
with the inserted curl of opposite sign). Checked by `decide`.
-/

namespace AJConjecture

/-- Positive right curls on the two edges commute. -/
theorem morseReach_isoPark_swapP :
    MorseReach 2 (isoCurlR true 1 ++ isoCurlR true 0)
      (isoCurlR true 0 ++ isoCurlR true 1) :=
  ⟨[(2, .exch (.cup, 1) (.cap, 2), true), (1, .exch (.cup, 1) (.cross true, 1), true),
    (0, .exch (.cup, 1) (.cup, 2), true), (3, .exch (.cross true, 0) (.cap, 4), true),
    (2, .exch (.cross true, 0) (.cross true, 3), true), (4, .exch (.cap, 1) (.cap, 4), true),
    (3, .exch (.cap, 1) (.cross true, 3), true), (1, .exch (.cross true, 0) (.cup, 4), true),
    (2, .exch (.cap, 1) (.cup, 4), true)], by decide⟩

/-- Negative right curls on the two edges commute. -/
theorem morseReach_isoPark_swapN :
    MorseReach 2 (isoCurlR false 0 ++ isoCurlR false 1)
      (isoCurlR false 1 ++ isoCurlR false 0) :=
  ⟨[(2, .exch (.cap, 1) (.cup, 4), false), (1, .exch (.cross false, 0) (.cup, 4), false),
    (3, .exch (.cap, 1) (.cross false, 3), false), (4, .exch (.cap, 1) (.cap, 4), false),
    (2, .exch (.cross false, 0) (.cross false, 3), false),
    (3, .exch (.cross false, 0) (.cap, 4), false), (0, .exch (.cup, 1) (.cup, 2), false),
    (1, .exch (.cup, 1) (.cross false, 1), false), (2, .exch (.cup, 1) (.cap, 2), false)
    ], by decide⟩

/-- A positive right curl on the right edge becomes `p` (one `kink`). -/
theorem morseReach_isoPark_RP :
    MorseReach 2 (isoCurlR true 1)
      (isoBeadsWord [.p]) :=
  ⟨[(3, .zig 1 false, true), (4, .zig 2 false, true), (4, .cupSlide 3 true true, true),
    (7, .capSlide 2 true false, true), (9, .exch (.cap, 1) (.cap, 3), true),
    (5, .r3 3 true, false), (7, .exch (.cross true, 2) (.cross true, 4), true),
    (8, .exch (.cap, 1) (.cross true, 4), true), (3, .exch (.cup, 2) (.cup, 2), false),
    (4, .exch (.cup, 2) (.cross true, 2), false), (5, .cupSlide 2 true false, false),
    (5, .exch (.cap, 1) (.cup, 3), true), (4, .r2 1 false, true),
    (5, .capSlide 1 true true, false), (3, .zig 1 true, true), (4, .zig 2 true, true),
    (4, .cupSlide 1 true false, true), (7, .capSlide 2 true true, true),
    (9, .exch (.cap, 2) (.cap, 4), false), (5, .r3 1 true, true),
    (7, .exch (.cross true, 1) (.cross true, 3), false),
    (8, .exch (.cross true, 1) (.cap, 4), false), (3, .exch (.cup, 1) (.cup, 1), true),
    (4, .exch (.cross true, 1) (.cup, 3), true), (5, .cupSlide 2 true true, false),
    (5, .exch (.cup, 2) (.cap, 2), false), (5, .capSlide 1 false true, true),
    (4, .r2 1 true, false), (6, .kink 1 true, false), (2, .capSlide 1 false true, true),
    (1, .r2 1 true, false), (2, .exch (.cap, 1) (.cup, 3), false),
    (2, .cupSlide 2 false false, true), (1, .exch (.cup, 2) (.cross false, 2), true),
    (0, .exch (.cup, 2) (.cup, 2), true), (5, .exch (.cap, 1) (.cross false, 4), false),
    (4, .exch (.cross false, 2) (.cross false, 4), false), (2, .r3 3 false, true),
    (6, .exch (.cap, 1) (.cap, 3), false), (4, .capSlide 2 false false, false),
    (1, .cupSlide 3 false true, false), (1, .zig 2 false, false), (0, .zig 1 false, false)
    ], by decide⟩

/-- A negative right curl on the right edge becomes `n` (one `kink`). -/
theorem morseReach_isoPark_RN :
    MorseReach 2 (isoCurlR false 1)
      (isoBeadsWord [.n]) :=
  ⟨[(3, .zig 1 false, true), (4, .zig 2 false, true), (4, .cupSlide 3 false true, true),
    (7, .capSlide 2 false false, true), (9, .exch (.cap, 1) (.cap, 3), true),
    (5, .r3 3 false, false), (7, .exch (.cross false, 2) (.cross false, 4), true),
    (8, .exch (.cap, 1) (.cross false, 4), true), (3, .exch (.cup, 2) (.cup, 2), false),
    (4, .exch (.cup, 2) (.cross false, 2), false), (5, .cupSlide 2 false false, false),
    (5, .exch (.cap, 1) (.cup, 3), true), (4, .r2 1 true, true),
    (5, .capSlide 1 false true, false), (3, .zig 1 true, true), (4, .zig 2 true, true),
    (4, .cupSlide 1 false false, true), (7, .capSlide 2 false true, true),
    (9, .exch (.cap, 2) (.cap, 4), false), (5, .r3 1 false, true),
    (7, .exch (.cross false, 1) (.cross false, 3), false),
    (8, .exch (.cross false, 1) (.cap, 4), false), (3, .exch (.cup, 1) (.cup, 1), true),
    (4, .exch (.cross false, 1) (.cup, 3), true), (5, .cupSlide 2 false true, false),
    (5, .exch (.cup, 2) (.cap, 2), false), (5, .capSlide 1 true true, true),
    (4, .r2 1 false, false), (6, .kink 1 false, false), (2, .capSlide 1 true true, true),
    (1, .r2 1 false, false), (2, .exch (.cap, 1) (.cup, 3), false),
    (2, .cupSlide 2 true false, true), (1, .exch (.cup, 2) (.cross true, 2), true),
    (0, .exch (.cup, 2) (.cup, 2), true), (5, .exch (.cap, 1) (.cross true, 4), false),
    (4, .exch (.cross true, 2) (.cross true, 4), false), (2, .r3 3 true, true),
    (6, .exch (.cap, 1) (.cap, 3), false), (4, .capSlide 2 true false, false),
    (1, .cupSlide 3 true true, false), (1, .zig 2 false, false), (0, .zig 1 false, false)
    ], by decide⟩

end AJConjecture
