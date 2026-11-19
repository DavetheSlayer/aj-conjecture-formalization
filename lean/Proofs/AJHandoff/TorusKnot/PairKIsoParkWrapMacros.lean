import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkDefs

/-!
# Stage C by ports: a right-edge curl turns at the ends of the return strand

The last cap `n1` joins the right edge of the band with the return strand, the first cup `u1`
joins them at the bottom. A right-edge curl `p`/`n` at the top end turns around `n1` onto the
return strand (`CAPP`, `CAPN`, as a right curl on the strand `2`), and a right curl on the return
strand turns around `u1` onto the right edge (`CUPP`, `CUPN`). `CAPP`, `CUPP` are the library
macros of `AJFamily.Skein.TorusPhaseTwoCurls`; `CAPN`, `CUPN` were found by search.
-/

namespace AJConjecture

/-- A positive right-edge curl turns around the last cap. -/
theorem morseReach_isoPark_capP :
    MorseReach 3 (isoBeadsWord [.p] ++ [isoN 1]) ([isoU 3, isoX true 2, isoN 3] ++ [isoN 1]) :=
  ⟨[(2, .exch (.cap, 1) (.cap, 3), false), (3, .zig 2 false, true),
    (4, .capSlide 1 true true, true), (6, .exch (.cap, 1) (.cap, 3), false),
    (3, .exch (.cross true, 1) (.cup, 3), true), (2, .exch (.cross true, 1) (.cap, 3), true),
    (0, .cupSlide 1 true false, false), (0, .zig 2 true, false)], by decide⟩

/-- A negative right-edge curl turns around the last cap. -/
theorem morseReach_isoPark_capN :
    MorseReach 3 (isoBeadsWord [.n] ++ [isoN 1]) ([isoU 3, isoX false 2, isoN 3] ++ [isoN 1]) :=
  ⟨[(2, .exch (.cap, 1) (.cap, 3), false), (3, .zig 2 false, true),
    (4, .capSlide 1 false true, true), (3, .exch (.cross false, 1) (.cup, 3), true),
    (6, .exch (.cap, 1) (.cap, 3), false), (2, .exch (.cross false, 1) (.cap, 3), true),
    (0, .cupSlide 1 false false, false), (0, .zig 2 true, false)], by decide⟩

/-- A positive right curl on the return strand turns around the first cup. -/
theorem morseReach_isoPark_cupP :
    MorseReach 1 ([isoU 1] ++ [isoU 3, isoX true 2, isoN 3]) ([isoU 1] ++ isoBeadsWord [.p]) :=
  ⟨[(0, .exch (.cup, 1) (.cup, 1), false), (1, .zig 1 false, true),
    (1, .cupSlide 2 true true, true), (0, .exch (.cup, 1) (.cup, 1), false),
    (3, .exch (.cap, 1) (.cross true, 3), true), (4, .exch (.cup, 1) (.cross true, 1), true),
    (5, .capSlide 2 true false, false), (4, .zig 1 true, false)], by decide⟩

/-- A negative right curl on the return strand turns around the first cup. -/
theorem morseReach_isoPark_cupN :
    MorseReach 1 ([isoU 1] ++ [isoU 3, isoX false 2, isoN 3]) ([isoU 1] ++ isoBeadsWord [.n]) :=
  ⟨[(4, .zig 2 false, true), (5, .capSlide 1 false true, true),
    (4, .exch (.cross false, 1) (.cup, 3), true), (3, .exch (.cross false, 1) (.cap, 3), true),
    (0, .exch (.cup, 1) (.cup, 1), false), (1, .cupSlide 1 false false, false),
    (1, .zig 2 true, false), (0, .exch (.cup, 1) (.cup, 1), false)], by decide⟩

end AJConjecture
