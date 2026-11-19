import Mathlib
import AJFamily.Skein.MorseReach

/-!
# The fixed macros of phase I

Six fixed checker certificates used by the level steps of phase I (`HC`, `S0a`, `S0b`, `S1a`, `S2a`,
`S2c`). Each turns a small word `lhs` on `n` strands into `rhs`; the frame lemma `morseReach_frame`
transports it, shifted, into the large words. Acceptance is proved by `decide`.
-/

namespace AJConjecture

/-- Macro `HC` (flip head), left side: the closing arc passes the cup `u (l+1)` of the head:
`u0 → u1 +0 +1` (one cupSlide), used with shift `l + 1`. -/
def phaseOneMacroHC_lhs : MorseWord :=
  [(.cup, 0)]

/-- Macro `HC`, right side. -/
def phaseOneMacroHC_rhs : MorseWord :=
  [(.cup, 1), (.cross true, 0), (.cross true, 1)]

/-- Macro `HC`, the moves (1). -/
def phaseOneMacroHC_moves : List MorseMove :=
  [(0, .cupSlide 0 true true, true)]

/-- The left side of macro `HC` fits on 1 strand. -/
theorem phaseOneMacroHC_fits : morseFits 1 phaseOneMacroHC_lhs = true := by decide

/-- The checker accepts macro `HC`. -/
theorem phaseOneMacroHC_ok :
    morseApplyAll 1 phaseOneMacroHC_lhs phaseOneMacroHC_moves = some phaseOneMacroHC_rhs := by
  decide

/-- Macro `HC` as a reachability statement. -/
theorem morseReach_phaseOneMacroHC : MorseReach 1 phaseOneMacroHC_lhs phaseOneMacroHC_rhs :=
  ⟨_, phaseOneMacroHC_ok⟩

/-- Macro `S0a` (top step, Hopf crossing), left side: the walk passes the first staircase step and
the first Hopf letter, shift `4k - 1`. -/
def phaseOneMacroS0a_lhs : MorseWord :=
  [(.cross true, 3), (.cross true, 4), (.cross true, 1), (.cross true, 0), (.cross false, 1),
   (.cross false, 2)]

/-- Macro `S0a`, right side. -/
def phaseOneMacroS0a_rhs : MorseWord :=
  [(.cross true, 1), (.cross true, 0), (.cross false, 1), (.cross true, 3), (.cross false, 2),
   (.cross false, 3), (.cross true, 3), (.cross true, 4)]

/-- Macro `S0a`, the moves (8). -/
def phaseOneMacroS0a_moves : List MorseMove :=
  [(1, .exch (.cross true, 1) (.cross true, 4), true),
   (0, .exch (.cross true, 1) (.cross true, 3), true),
   (2, .exch (.cross true, 0) (.cross true, 4), true),
   (1, .exch (.cross true, 0) (.cross true, 3), true),
   (3, .exch (.cross false, 1) (.cross true, 4), true),
   (2, .exch (.cross false, 1) (.cross true, 3), true),
   (4, .exch (.cross false, 2) (.cross true, 4), true), (5, .r2 3 false, true)]

/-- The left side of macro `S0a` fits on 6 strands. -/
theorem phaseOneMacroS0a_fits : morseFits 6 phaseOneMacroS0a_lhs = true := by decide

/-- The checker accepts macro `S0a`. -/
theorem phaseOneMacroS0a_ok :
    morseApplyAll 6 phaseOneMacroS0a_lhs phaseOneMacroS0a_moves = some phaseOneMacroS0a_rhs := by
  decide

/-- Macro `S0a` as a reachability statement. -/
theorem morseReach_phaseOneMacroS0a : MorseReach 6 phaseOneMacroS0a_lhs phaseOneMacroS0a_rhs :=
  ⟨_, phaseOneMacroS0a_ok⟩

/-- Macro `S0b` (top step, tail), left side: the walk ends at the closing caps, shift `4k + 1`. -/
def phaseOneMacroS0b_lhs : MorseWord :=
  [(.cross true, 2), (.cross false, 0), (.cap, 1), (.cap, 0)]

/-- Macro `S0b`, right side. -/
def phaseOneMacroS0b_rhs : MorseWord :=
  [(.cap, 1), (.cap, 0)]

/-- Macro `S0b`, the moves (5). -/
def phaseOneMacroS0b_moves : List MorseMove :=
  [(0, .exch (.cross false, 0) (.cross true, 2), true), (1, .r2 1 false, true),
   (2, .capSlide 1 true true, false), (2, .exch (.cap, 0) (.cap, 2), true),
   (0, .capSlide 0 false true, false)]

/-- The left side of macro `S0b` fits on 4 strands. -/
theorem phaseOneMacroS0b_fits : morseFits 4 phaseOneMacroS0b_lhs = true := by decide

/-- The checker accepts macro `S0b`. -/
theorem phaseOneMacroS0b_ok :
    morseApplyAll 4 phaseOneMacroS0b_lhs phaseOneMacroS0b_moves = some phaseOneMacroS0b_rhs := by
  decide

/-- Macro `S0b` as a reachability statement. -/
theorem morseReach_phaseOneMacroS0b : MorseReach 4 phaseOneMacroS0b_lhs phaseOneMacroS0b_rhs :=
  ⟨_, phaseOneMacroS0b_ok⟩

/-- Macro `S1a` (level 4k, middle), left side: the closing arc of the level `4k` passes the two
middle groups, shift `4k - 1`. -/
def phaseOneMacroS1a_lhs : MorseWord :=
  [(.cup, 2), (.cross true, 1), (.cross true, 0), (.cross false, 1), (.cup, 4),
   (.cross true, 3), (.cross false, 2), (.cross false, 3)]

/-- Macro `S1a`, right side. -/
def phaseOneMacroS1a_rhs : MorseWord :=
  [(.cup, 3), (.cross true, 2), (.cross true, 1), (.cross true, 0), (.cross false, 1),
   (.cross false, 2), (.cup, 5), (.cross true, 4), (.cross false, 3), (.cross false, 4),
   (.cross true, 2), (.cross true, 3), (.cross true, 4), (.cross true, 5)]

/-- Macro `S1a`, the moves (21). -/
def phaseOneMacroS1a_moves : List MorseMove :=
  [(0, .cupSlide 2 true true, true), (2, .exch (.cross true, 1) (.cross true, 3), true),
   (3, .exch (.cross true, 0) (.cross true, 3), true),
   (4, .exch (.cross false, 1) (.cross true, 3), true), (5, .r2 2 false, true),
   (8, .cupSlide 4 true true, true), (7, .exch (.cross true, 3) (.cup, 5), false),
   (6, .exch (.cross true, 2) (.cup, 5), false),
   (10, .exch (.cross true, 3) (.cross true, 5), true), (8, .r3 3 true, false),
   (7, .exch (.cross true, 2) (.cross true, 4), false),
   (11, .exch (.cross false, 2) (.cross true, 5), true),
   (10, .exch (.cross false, 2) (.cross true, 4), true), (8, .r2 3 false, true),
   (9, .r3 2 true, true), (11, .r2 2 true, false),
   (12, .exch (.cross false, 3) (.cross true, 5), true), (10, .r2 4 false, true),
   (11, .r3 3 true, true), (13, .r2 3 true, false),
   (9, .exch (.cross true, 2) (.cross false, 4), false)]

/-- The left side of macro `S1a` fits on 3 strands. -/
theorem phaseOneMacroS1a_fits : morseFits 3 phaseOneMacroS1a_lhs = true := by decide

/-- The checker accepts macro `S1a`. -/
theorem phaseOneMacroS1a_ok :
    morseApplyAll 3 phaseOneMacroS1a_lhs phaseOneMacroS1a_moves = some phaseOneMacroS1a_rhs := by
  decide

/-- Macro `S1a` as a reachability statement. -/
theorem morseReach_phaseOneMacroS1a : MorseReach 3 phaseOneMacroS1a_lhs phaseOneMacroS1a_rhs :=
  ⟨_, phaseOneMacroS1a_ok⟩

/-- Macro `S2a` (level 4k-1, middle), left side: the walk passes the middle groups and the first
staircase band, shift `4k - 2`. -/
def phaseOneMacroS2a_lhs : MorseWord :=
  [(.cross true, 3), (.cup, 4), (.cross true, 3), (.cross true, 2), (.cross true, 1),
   (.cross false, 2), (.cross false, 3), (.cup, 6), (.cross true, 5), (.cross false, 4),
   (.cross false, 5), (.cross true, 1), (.cross true, 0), (.cross false, 1), (.cap, 2)]

/-- Macro `S2a`, right side. -/
def phaseOneMacroS2a_rhs : MorseWord :=
  [(.cross false, 2), (.cup, 5), (.cross true, 4), (.cross true, 3), (.cross true, 2),
   (.cross true, 1), (.cross false, 2), (.cross false, 3), (.cross false, 4), (.cup, 7),
   (.cross true, 6), (.cross false, 5), (.cross false, 6), (.cross true, 2),
   (.cross true, 1), (.cross true, 0), (.cross false, 1), (.cross false, 2), (.cap, 3),
   (.cross true, 2), (.cross true, 3), (.cross true, 4), (.cross true, 5)]

/-- Macro `S2a`, the moves (69). -/
def phaseOneMacroS2a_moves : List MorseMove :=
  [(0, .r2 2 false, true), (3, .cupSlide 4 true true, true),
   (2, .exch (.cross true, 3) (.cup, 5), false),
   (1, .exch (.cross true, 2) (.cup, 5), false),
   (5, .exch (.cross true, 3) (.cross true, 5), true), (3, .r3 3 true, false),
   (2, .exch (.cross true, 2) (.cross true, 4), false),
   (6, .exch (.cross true, 2) (.cross true, 5), true),
   (5, .exch (.cross true, 2) (.cross true, 4), true), (3, .r3 2 true, false),
   (7, .exch (.cross true, 1) (.cross true, 5), true),
   (6, .exch (.cross true, 1) (.cross true, 4), true),
   (5, .exch (.cross true, 1) (.cross true, 3), true), (6, .r2 2 false, true),
   (10, .exch (.cross false, 2) (.cross true, 5), true),
   (9, .exch (.cross false, 2) (.cross true, 4), true), (7, .r2 3 false, true),
   (8, .r3 2 true, true), (10, .r2 2 true, false),
   (11, .exch (.cross false, 3) (.cross true, 5), true), (9, .r2 4 false, true),
   (10, .r3 3 true, true), (12, .r2 3 true, false),
   (8, .exch (.cross true, 2) (.cross false, 4), false), (13, .cupSlide 6 true true, true),
   (12, .exch (.cross true, 5) (.cup, 7), false),
   (11, .exch (.cross true, 4) (.cup, 7), false),
   (10, .exch (.cross true, 3) (.cup, 7), false),
   (9, .exch (.cross true, 2) (.cup, 7), false),
   (15, .exch (.cross true, 5) (.cross true, 7), true), (13, .r3 5 true, false),
   (12, .exch (.cross true, 4) (.cross true, 6), false),
   (11, .exch (.cross true, 3) (.cross true, 6), false),
   (10, .exch (.cross true, 2) (.cross true, 6), false),
   (16, .exch (.cross false, 4) (.cross true, 7), true),
   (15, .exch (.cross false, 4) (.cross true, 6), true), (13, .r2 5 false, true),
   (14, .r3 4 true, true), (16, .r2 4 true, false),
   (12, .exch (.cross true, 3) (.cross false, 5), false),
   (11, .exch (.cross true, 2) (.cross false, 5), false),
   (17, .exch (.cross false, 5) (.cross true, 7), true), (15, .r2 6 false, true),
   (16, .r3 5 true, true), (18, .r2 5 true, false),
   (14, .exch (.cross true, 4) (.cross false, 6), false),
   (13, .exch (.cross true, 3) (.cross false, 6), false),
   (12, .exch (.cross true, 2) (.cross false, 6), false),
   (18, .exch (.cross true, 1) (.cross true, 7), true),
   (17, .exch (.cross true, 1) (.cross true, 6), true),
   (16, .exch (.cross true, 1) (.cross true, 5), true),
   (15, .exch (.cross true, 1) (.cross true, 4), true),
   (14, .exch (.cross true, 1) (.cross true, 3), true),
   (19, .exch (.cross true, 0) (.cross true, 7), true),
   (18, .exch (.cross true, 0) (.cross true, 6), true),
   (17, .exch (.cross true, 0) (.cross true, 5), true),
   (16, .exch (.cross true, 0) (.cross true, 4), true),
   (15, .exch (.cross true, 0) (.cross true, 3), true),
   (20, .exch (.cross false, 1) (.cross true, 7), true),
   (19, .exch (.cross false, 1) (.cross true, 6), true),
   (18, .exch (.cross false, 1) (.cross true, 5), true),
   (17, .exch (.cross false, 1) (.cross true, 4), true),
   (16, .exch (.cross false, 1) (.cross true, 3), true), (17, .r2 2 false, true),
   (23, .exch (.cap, 2) (.cross true, 7), true),
   (22, .exch (.cap, 2) (.cross true, 6), true),
   (21, .exch (.cap, 2) (.cross true, 5), true),
   (20, .exch (.cap, 2) (.cross true, 4), true), (18, .capSlide 2 true true, false)]

/-- The left side of macro `S2a` fits on 5 strands. -/
theorem phaseOneMacroS2a_fits : morseFits 5 phaseOneMacroS2a_lhs = true := by decide

/-- The checker accepts macro `S2a`. -/
theorem phaseOneMacroS2a_ok :
    morseApplyAll 5 phaseOneMacroS2a_lhs phaseOneMacroS2a_moves = some phaseOneMacroS2a_rhs := by
  decide

/-- Macro `S2a` as a reachability statement. -/
theorem morseReach_phaseOneMacroS2a : MorseReach 5 phaseOneMacroS2a_lhs phaseOneMacroS2a_rhs :=
  ⟨_, phaseOneMacroS2a_ok⟩

/-- Macro `S2c` (level 4k-1, end), left side: the travelling cup enters the middle group:
`u0 u4 +3 +2 +1 +0 → u2 +1 +0 u1`, shift `4k - 1`. -/
def phaseOneMacroS2c_lhs : MorseWord :=
  [(.cup, 0), (.cup, 4), (.cross true, 3), (.cross true, 2), (.cross true, 1), (.cross true, 0)]

/-- Macro `S2c`, right side. -/
def phaseOneMacroS2c_rhs : MorseWord :=
  [(.cup, 2), (.cross true, 1), (.cross true, 0), (.cup, 1)]

/-- Macro `S2c`, the moves (4). -/
def phaseOneMacroS2c_moves : List MorseMove :=
  [(0, .exch (.cup, 0) (.cup, 2), false), (1, .exch (.cup, 0) (.cross true, 1), false),
   (2, .exch (.cup, 0) (.cross true, 0), false), (3, .cupSlide 0 true false, false)]

/-- The left side of macro `S2c` fits on 2 strands. -/
theorem phaseOneMacroS2c_fits : morseFits 2 phaseOneMacroS2c_lhs = true := by decide

/-- The checker accepts macro `S2c`. -/
theorem phaseOneMacroS2c_ok :
    morseApplyAll 2 phaseOneMacroS2c_lhs phaseOneMacroS2c_moves = some phaseOneMacroS2c_rhs := by
  decide

/-- Macro `S2c` as a reachability statement. -/
theorem morseReach_phaseOneMacroS2c : MorseReach 2 phaseOneMacroS2c_lhs phaseOneMacroS2c_rhs :=
  ⟨_, phaseOneMacroS2c_ok⟩

end AJConjecture
