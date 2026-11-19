import Mathlib
import AJFamily.Skein.MorseReach

/-!
# The fixed macros of phase II

Nine fixed checker certificates of phase II, each turning a small word `lhs` on `n` strands into
`rhs`; they are applied with the frame lemma `morseReach_frame`, and their acceptance is proved by
`decide`. Macros `A`, `M`, `B`, `Q` put the strip blocks in normal form (stage N); `RC`, `SB`, `TC`
move the return strand and clean up after its swing (stage S); `TWCAP` and `HCUPM` move a full twist
past a doubled cap and a half twist past a doubled cup (stages T and G).
-/

namespace AJConjecture

/-- Macro `A`, left side: the stabilisation block `A` → negative full twist of the band `(1,2)` and
a negative left curl on its right edge (fold normal form, then a zig-zag). -/
def phaseTwoMacroA_lhs : MorseWord :=
  [(.cup, 3), (.cross true, 2), (.cross true, 1), (.cross false, 2), (.cap, 1)]

/-- Macro `A`, right side. -/
def phaseTwoMacroA_rhs : MorseWord :=
  [(.cross false, 1), (.cross false, 1), (.cup, 2), (.cross false, 3), (.cap, 2)]

/-- Macro `A`, the moves (25). -/
def phaseTwoMacroA_moves : List MorseMove :=
  [(1, .r2 1 false, true), (2, .r3 1 true, false), (4, .r2 2 true, false),
    (3, .zig 2 true, true), (4, .exch (.cross true, 1) (.cap, 3), true),
    (5, .exch (.cap, 1) (.cap, 3), true), (3, .cupSlide 1 false false, true),
    (5, .r2 1 false, false), (2, .exch (.cup, 1) (.cross true, 2), true),
    (3, .exch (.cross false, 2) (.cross true, 4), true),
    (4, .exch (.cap, 1) (.cross true, 4), true), (5, .r2 1 false, true),
    (6, .capSlide 1 true true, false), (4, .exch (.cap, 1) (.cross false, 3), false),
    (5, .capSlide 1 false false, true), (3, .r3 2 false, false),
    (5, .exch (.cross false, 1) (.cross false, 3), true),
    (2, .exch (.cup, 1) (.cross false, 1), false), (3, .cupSlide 1 false false, false),
    (0, .exch (.cross false, 1) (.cup, 3), true), (1, .exch (.cross false, 1) (.cup, 3), true),
    (2, .exch (.cup, 2) (.cup, 3), true), (3, .exch (.cross false, 3) (.cup, 5), true),
    (4, .exch (.cap, 2) (.cup, 5), true), (5, .zig 2 false, false)]

/-- The left side of macro `A` fits on 3 strands. -/
theorem phaseTwoMacroA_fits : morseFits 3 phaseTwoMacroA_lhs = true := by decide

/-- The checker accepts macro `A`. -/
theorem phaseTwoMacroA_ok :
    morseApplyAll 3 phaseTwoMacroA_lhs phaseTwoMacroA_moves = some phaseTwoMacroA_rhs := by
  decide

/-- Macro `A` as a reachability statement. -/
theorem morseReach_phaseTwoMacroA : MorseReach 3 phaseTwoMacroA_lhs phaseTwoMacroA_rhs :=
  ⟨_, phaseTwoMacroA_ok⟩

/-- Macro `M`, left side: the middle block (without its last two letters) → doubled cup, doubled
crossing `D` (shifted by one), positive left curl, clasp letters. -/
def phaseTwoMacroM_lhs : MorseWord :=
  [(.cup, 3), (.cross true, 2), (.cross true, 1), (.cup, 2), (.cross false, 2),
    (.cross false, 3), (.cross false, 4), (.cup, 7), (.cross true, 6), (.cross false, 5),
    (.cross false, 6)]

/-- Macro `M`, right side. -/
def phaseTwoMacroM_rhs : MorseWord :=
  [(.cup, 3), (.cup, 4), (.cross true, 2), (.cross true, 3), (.cross true, 1), (.cross true, 2),
    (.cup, 2), (.cross true, 3), (.cap, 2), (.cup, 7), (.cross true, 6), (.cross false, 5),
    (.cross false, 6)]

/-- Macro `M`, the moves (19). -/
def phaseTwoMacroM_moves : List MorseMove :=
  [(4, .zig 2 false, true), (5, .exch (.cap, 2) (.cross false, 4), false),
    (6, .r2 3 false, true), (4, .cupSlide 3 false false, false),
    (3, .exch (.cup, 2) (.cup, 2), false), (6, .exch (.cap, 2) (.cross false, 5), false),
    (5, .exch (.cross true, 3) (.cross false, 5), false),
    (4, .exch (.cup, 2) (.cross false, 3), false),
    (7, .exch (.cap, 2) (.cross false, 6), false),
    (6, .exch (.cross true, 3) (.cross false, 6), false),
    (5, .exch (.cup, 2) (.cross false, 4), false), (5, .r2 2 false, true),
    (3, .cupSlide 2 false false, false), (4, .exch (.cross true, 2) (.cross false, 4), false),
    (5, .r2 3 false, true), (3, .cupSlide 3 false false, false),
    (2, .exch (.cross true, 1) (.cup, 4), false), (1, .exch (.cross true, 2) (.cup, 4), false),
    (3, .exch (.cross true, 1) (.cross true, 3), false)]

/-- The left side of macro `M` fits on 3 strands. -/
theorem phaseTwoMacroM_fits : morseFits 3 phaseTwoMacroM_lhs = true := by decide

/-- The checker accepts macro `M`. -/
theorem phaseTwoMacroM_ok :
    morseApplyAll 3 phaseTwoMacroM_lhs phaseTwoMacroM_moves = some phaseTwoMacroM_rhs := by
  decide

/-- Macro `M` as a reachability statement. -/
theorem morseReach_phaseTwoMacroM : MorseReach 3 phaseTwoMacroM_lhs phaseTwoMacroM_rhs :=
  ⟨_, phaseTwoMacroM_ok⟩

/-- Macro `B`, left side: the staircase block `B'` (= `+2 +1` of the previous block and `B` without
them) → doubled crossing `D` (shifted by one) and a positive left curl. -/
def phaseTwoMacroB_lhs : MorseWord :=
  [(.cross true, 2), (.cross true, 1), (.cup, 2), (.cross false, 2), (.cross false, 3),
    (.cross false, 4), (.cap, 5)]

/-- Macro `B`, right side. -/
def phaseTwoMacroB_rhs : MorseWord :=
  [(.cross true, 2), (.cross true, 3), (.cross true, 1), (.cross true, 2), (.cup, 2),
    (.cross true, 3), (.cap, 2)]

/-- Macro `B`, the moves (23). -/
def phaseTwoMacroB_moves : List MorseMove :=
  [(3, .zig 2 false, true), (4, .exch (.cap, 2) (.cross false, 4), false),
    (5, .r2 3 false, true), (3, .cupSlide 3 false false, false),
    (2, .exch (.cup, 2) (.cup, 2), false), (5, .exch (.cap, 2) (.cross false, 5), false),
    (4, .exch (.cross true, 3) (.cross false, 5), false),
    (3, .exch (.cup, 2) (.cross false, 3), false),
    (6, .exch (.cap, 2) (.cross false, 6), false),
    (5, .exch (.cross true, 3) (.cross false, 6), false),
    (4, .exch (.cup, 2) (.cross false, 4), false), (7, .exch (.cap, 2) (.cap, 7), false),
    (6, .exch (.cross true, 3) (.cap, 7), false), (5, .exch (.cup, 2) (.cap, 5), false),
    (4, .r2 2 false, true), (2, .cupSlide 2 false false, false),
    (3, .exch (.cross true, 2) (.cross false, 4), false), (4, .r2 3 false, true),
    (2, .cupSlide 3 false false, false), (4, .exch (.cross true, 2) (.cap, 5), false),
    (3, .exch (.cross true, 3) (.cap, 5), false), (2, .zig 4 true, false),
    (1, .exch (.cross true, 1) (.cross true, 3), false)]

/-- The left side of macro `B` fits on 9 strands. -/
theorem phaseTwoMacroB_fits : morseFits 9 phaseTwoMacroB_lhs = true := by decide

/-- The checker accepts macro `B`. -/
theorem phaseTwoMacroB_ok :
    morseApplyAll 9 phaseTwoMacroB_lhs phaseTwoMacroB_moves = some phaseTwoMacroB_rhs := by
  decide

/-- Macro `B` as a reachability statement. -/
theorem morseReach_phaseTwoMacroB : MorseReach 9 phaseTwoMacroB_lhs phaseTwoMacroB_rhs :=
  ⟨_, phaseTwoMacroB_ok⟩

/-- Macro `Q`, left side: the tail block `Q'` → doubled crossing, the cap of the return strand, fold
normal form (negative full twist, curl, caps), twisted cap as cap plus curl. -/
def phaseTwoMacroQ_lhs : MorseWord :=
  [(.cross true, 2), (.cross true, 1), (.cross true, 0), (.cross false, 1), (.cross false, 2),
    (.cap, 3), (.cross true, 2), (.cross true, 1), (.cross false, 2), (.cap, 1),
    (.cross true, 2), (.cap, 2), (.cap, 1)]

/-- Macro `Q`, right side. -/
def phaseTwoMacroQ_rhs : MorseWord :=
  [(.cross true, 2), (.cross true, 3), (.cross true, 1), (.cross true, 2), (.cross true, 0),
    (.cap, 1), (.cross false, 1), (.cross false, 1), (.cup, 2), (.cross false, 3), (.cap, 2),
    (.cap, 2), (.cup, 2), (.cross false, 3), (.cap, 2), (.cap, 2), (.cap, 1)]

/-- Macro `Q`, the moves (32). -/
def phaseTwoMacroQ_moves : List MorseMove :=
  [(5, .capSlide 2 true true, true), (4, .r2 2 false, false),
    (3, .exch (.cross false, 1) (.cross true, 3), false), (5, .capSlide 1 true true, true),
    (4, .r2 1 false, false), (2, .exch (.cross true, 0) (.cross true, 3), false),
    (3, .exch (.cross true, 0) (.cross true, 2), false),
    (1, .exch (.cross true, 1) (.cross true, 3), false), (6, .r2 1 false, true),
    (7, .r3 1 true, false), (9, .r2 2 true, false), (8, .zig 2 true, true),
    (9, .exch (.cross true, 1) (.cap, 3), true), (10, .exch (.cap, 1) (.cap, 3), true),
    (8, .cupSlide 1 false false, true), (10, .r2 1 false, false),
    (7, .exch (.cup, 1) (.cross true, 2), true),
    (8, .exch (.cross false, 2) (.cross true, 4), true),
    (9, .exch (.cap, 1) (.cross true, 4), true), (10, .r2 1 false, true),
    (11, .capSlide 1 true true, false), (9, .exch (.cap, 1) (.cross false, 3), false),
    (10, .capSlide 1 false false, true), (8, .r3 2 false, false),
    (10, .exch (.cross false, 1) (.cross false, 3), true),
    (7, .exch (.cup, 1) (.cross false, 1), false), (8, .cupSlide 1 false false, false),
    (12, .zig 3 true, true), (13, .exch (.cross true, 2) (.cap, 4), true),
    (14, .exch (.cap, 2) (.cap, 4), true), (12, .cupSlide 2 false false, true),
    (14, .r2 2 false, false)]

/-- The left side of macro `Q` fits on 9 strands. -/
theorem phaseTwoMacroQ_fits : morseFits 9 phaseTwoMacroQ_lhs = true := by decide

/-- The checker accepts macro `Q`. -/
theorem phaseTwoMacroQ_ok :
    morseApplyAll 9 phaseTwoMacroQ_lhs phaseTwoMacroQ_moves = some phaseTwoMacroQ_rhs := by
  decide

/-- Macro `Q` as a reachability statement. -/
theorem morseReach_phaseTwoMacroQ : MorseReach 9 phaseTwoMacroQ_lhs phaseTwoMacroQ_rhs :=
  ⟨_, phaseTwoMacroQ_ok⟩

/-- Macro `RC`, left side: the cap of the return strand `+0 n1` moves to the end of the tail
(exchanges). -/
def phaseTwoMacroRC_lhs : MorseWord :=
  [(.cross true, 2), (.cross true, 3), (.cross true, 1), (.cross true, 2), (.cross true, 0),
    (.cap, 1), (.cross false, 1), (.cross false, 1), (.cup, 2), (.cross false, 3), (.cap, 2),
    (.cap, 2), (.cup, 2), (.cross false, 3), (.cap, 2), (.cap, 2), (.cap, 1)]

/-- Macro `RC`, right side. -/
def phaseTwoMacroRC_rhs : MorseWord :=
  [(.cross true, 2), (.cross true, 3), (.cross true, 1), (.cross true, 2), (.cross false, 3),
    (.cross false, 3), (.cup, 4), (.cross false, 5), (.cap, 4), (.cap, 4), (.cup, 4),
    (.cross false, 5), (.cap, 4), (.cap, 4), (.cap, 3), (.cross true, 0), (.cap, 1)]

/-- Macro `RC`, the moves (22). -/
def phaseTwoMacroRC_moves : List MorseMove :=
  [(5, .exch (.cap, 1) (.cross false, 3), false), (6, .exch (.cap, 1) (.cross false, 3), false),
    (7, .exch (.cap, 1) (.cup, 4), false), (8, .exch (.cap, 1) (.cross false, 5), false),
    (9, .exch (.cap, 1) (.cap, 4), false), (10, .exch (.cap, 1) (.cap, 4), false),
    (11, .exch (.cap, 1) (.cup, 4), false), (12, .exch (.cap, 1) (.cross false, 5), false),
    (13, .exch (.cap, 1) (.cap, 4), false), (14, .exch (.cap, 1) (.cap, 4), false),
    (15, .exch (.cap, 1) (.cap, 3), false),
    (4, .exch (.cross true, 0) (.cross false, 3), false),
    (5, .exch (.cross true, 0) (.cross false, 3), false),
    (6, .exch (.cross true, 0) (.cup, 4), false),
    (7, .exch (.cross true, 0) (.cross false, 5), false),
    (8, .exch (.cross true, 0) (.cap, 4), false), (9, .exch (.cross true, 0) (.cap, 4), false),
    (10, .exch (.cross true, 0) (.cup, 4), false),
    (11, .exch (.cross true, 0) (.cross false, 5), false),
    (12, .exch (.cross true, 0) (.cap, 4), false),
    (13, .exch (.cross true, 0) (.cap, 4), false),
    (14, .exch (.cross true, 0) (.cap, 3), false)]

/-- The left side of macro `RC` fits on 9 strands. -/
theorem phaseTwoMacroRC_fits : morseFits 9 phaseTwoMacroRC_lhs = true := by decide

/-- The checker accepts macro `RC`. -/
theorem phaseTwoMacroRC_ok :
    morseApplyAll 9 phaseTwoMacroRC_lhs phaseTwoMacroRC_moves = some phaseTwoMacroRC_rhs := by
  decide

/-- Macro `RC` as a reachability statement. -/
theorem morseReach_phaseTwoMacroRC : MorseReach 9 phaseTwoMacroRC_lhs phaseTwoMacroRC_rhs :=
  ⟨_, phaseTwoMacroRC_ok⟩

/-- Macro `SB`, left side: debris of the swing of the return strand at the bottom: `u1 +0 +0 +1` →
negative full twist and negative left curl. -/
def phaseTwoMacroSB_lhs : MorseWord :=
  [(.cup, 1), (.cross true, 0), (.cross true, 0), (.cross true, 1)]

/-- Macro `SB`, right side. -/
def phaseTwoMacroSB_rhs : MorseWord :=
  [(.cup, 1), (.cross false, 0), (.cross false, 0), (.cup, 1), (.cross false, 2), (.cap, 1)]

/-- Macro `SB`, the moves (19). -/
def phaseTwoMacroSB_moves : List MorseMove :=
  [(2, .zig 0 false, true), (3, .exch (.cap, 0) (.cross true, 2), false),
    (4, .exch (.cap, 0) (.cross true, 3), false), (5, .capSlide 0 false false, true),
    (4, .r2 1 true, true), (2, .cupSlide 1 true false, false),
    (3, .exch (.cross false, 1) (.cross true, 3), false), (4, .r2 2 true, true),
    (2, .cupSlide 2 true false, false), (0, .cupSlide 0 false false, true),
    (2, .r2 0 false, false), (1, .exch (.cross false, 1) (.cup, 3), false),
    (2, .r3 1 false, false), (3, .r3 1 false, false),
    (5, .exch (.cross false, 0) (.cross false, 2), true),
    (0, .exch (.cup, 0) (.cup, 1), false), (1, .exch (.cup, 0) (.cross false, 0), false),
    (2, .exch (.cup, 0) (.cross false, 0), false), (3, .cupSlide 0 false false, false)]

/-- The left side of macro `SB` fits on 1 strand. -/
theorem phaseTwoMacroSB_fits : morseFits 1 phaseTwoMacroSB_lhs = true := by decide

/-- The checker accepts macro `SB`. -/
theorem phaseTwoMacroSB_ok :
    morseApplyAll 1 phaseTwoMacroSB_lhs phaseTwoMacroSB_moves = some phaseTwoMacroSB_rhs := by
  decide

/-- Macro `SB` as a reachability statement. -/
theorem morseReach_phaseTwoMacroSB : MorseReach 1 phaseTwoMacroSB_lhs phaseTwoMacroSB_rhs :=
  ⟨_, phaseTwoMacroSB_ok⟩

/-- Macro `TC`, left side: debris at the top: twisted cap `-1 n1` → positive left curl and cap. -/
def phaseTwoMacroTC_lhs : MorseWord :=
  [(.cross false, 1), (.cap, 1)]

/-- Macro `TC`, right side. -/
def phaseTwoMacroTC_rhs : MorseWord :=
  [(.cup, 1), (.cross true, 2), (.cap, 1), (.cap, 1)]

/-- Macro `TC`, the moves (5). -/
def phaseTwoMacroTC_moves : List MorseMove :=
  [(0, .zig 2 true, true), (1, .exch (.cross false, 1) (.cap, 3), true),
    (2, .exch (.cap, 1) (.cap, 3), true), (0, .cupSlide 1 true false, true),
    (2, .r2 1 true, false)]

/-- The left side of macro `TC` fits on 3 strands. -/
theorem phaseTwoMacroTC_fits : morseFits 3 phaseTwoMacroTC_lhs = true := by decide

/-- The checker accepts macro `TC`. -/
theorem phaseTwoMacroTC_ok :
    morseApplyAll 3 phaseTwoMacroTC_lhs phaseTwoMacroTC_moves = some phaseTwoMacroTC_rhs := by
  decide

/-- Macro `TC` as a reachability statement. -/
theorem morseReach_phaseTwoMacroTC : MorseReach 3 phaseTwoMacroTC_lhs phaseTwoMacroTC_rhs :=
  ⟨_, phaseTwoMacroTC_ok⟩

/-- Macro `TWCAP`, left side: a negative full twist passes a doubled cap. -/
def phaseTwoMacroTWCAP_lhs : MorseWord :=
  [(.cross false, 0), (.cross false, 0), (.cap, 1), (.cap, 0)]

/-- Macro `TWCAP`, right side. -/
def phaseTwoMacroTWCAP_rhs : MorseWord :=
  [(.cross false, 2), (.cross false, 2), (.cap, 1), (.cap, 0)]

/-- Macro `TWCAP`, the moves (9). -/
def phaseTwoMacroTWCAP_moves : List MorseMove :=
  [(2, .capSlide 1 false false, true), (1, .exch (.cross false, 0) (.cross false, 2), false),
    (0, .exch (.cross false, 0) (.cross false, 2), false),
    (4, .exch (.cap, 0) (.cap, 2), true), (2, .capSlide 0 false true, false),
    (2, .capSlide 1 false false, true), (4, .exch (.cap, 0) (.cap, 2), true),
    (1, .exch (.cross false, 0) (.cross false, 2), false), (2, .capSlide 0 false true, false)]

/-- The left side of macro `TWCAP` fits on 4 strands. -/
theorem phaseTwoMacroTWCAP_fits : morseFits 4 phaseTwoMacroTWCAP_lhs = true := by decide

/-- The checker accepts macro `TWCAP`. -/
theorem phaseTwoMacroTWCAP_ok :
    morseApplyAll 4 phaseTwoMacroTWCAP_lhs phaseTwoMacroTWCAP_moves = some phaseTwoMacroTWCAP_rhs := by
  decide

/-- Macro `TWCAP` as a reachability statement. -/
theorem morseReach_phaseTwoMacroTWCAP : MorseReach 4 phaseTwoMacroTWCAP_lhs phaseTwoMacroTWCAP_rhs :=
  ⟨_, phaseTwoMacroTWCAP_ok⟩

/-- Macro `HCUPM`, left side: a negative half twist passes a doubled cup (right band → left
band). -/
def phaseTwoMacroHCUPM_lhs : MorseWord :=
  [(.cup, 0), (.cup, 1), (.cross false, 2)]

/-- Macro `HCUPM`, right side. -/
def phaseTwoMacroHCUPM_rhs : MorseWord :=
  [(.cup, 0), (.cup, 1), (.cross false, 0)]

/-- Macro `HCUPM`, the moves (4). -/
def phaseTwoMacroHCUPM_moves : List MorseMove :=
  [(1, .cupSlide 0 false false, true), (3, .exch (.cross false, 0) (.cross false, 2), false),
    (0, .exch (.cup, 0) (.cup, 0), true), (1, .cupSlide 1 false true, false)]

/-- The left side of macro `HCUPM` fits on 0 strands. -/
theorem phaseTwoMacroHCUPM_fits : morseFits 0 phaseTwoMacroHCUPM_lhs = true := by decide

/-- The checker accepts macro `HCUPM`. -/
theorem phaseTwoMacroHCUPM_ok :
    morseApplyAll 0 phaseTwoMacroHCUPM_lhs phaseTwoMacroHCUPM_moves = some phaseTwoMacroHCUPM_rhs := by
  decide

/-- Macro `HCUPM` as a reachability statement. -/
theorem morseReach_phaseTwoMacroHCUPM : MorseReach 0 phaseTwoMacroHCUPM_lhs phaseTwoMacroHCUPM_rhs :=
  ⟨_, phaseTwoMacroHCUPM_ok⟩

end AJConjecture
