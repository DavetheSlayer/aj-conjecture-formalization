import Mathlib
import AJFamily.Skein.TorusPhaseTwoSwing
import AJFamily.Skein.TorusPhaseTwoPass

/-!
# Stage N of phase II: the strip blocks in normal form

`phaseTwo_stageN`: after rewriting `stripWord k` as `phaseTwoW0 k`, the fixed macros `A` and `B` are
applied to each of the `2k - 1` blocks of their kind (`morseReach_blocks`) and the macros `M` and
`Q` once (frame lemma), giving `phaseTwoWN k`.
-/

namespace AJConjecture

/-- Shifting by zero strands does nothing. -/
private theorem morseShiftWord_zero_stageN (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

set_option linter.unusedVariables false in
/-- Stage N: the strip word reaches its block normal form. -/
theorem phaseTwo_stageN (k : ℕ) (hk : 1 ≤ k) : MorseReach 1 (stripWord k) (phaseTwoWN k) := by
  set n := 2 * k - 1
  have hP : morseOut 1 stripP = 3 := by decide
  have hAo : morseOut 3 phaseTwoMacroA_rhs = 3 := by decide
  have hMo : morseOut 3 phaseTwoMacroM_rhs = 9 := by decide
  have hBo : morseOut 9 phaseTwoMacroB_rhs = 9 := by decide
  have hu1 : morseOut 1 (stripP ++ phaseTwoBlk phaseTwoMacroA_rhs n) = 3 := by
    rw [morseOut_append, hP, morseOut_phaseTwoBlk 3 n _ hAo]
  have hu2 : morseOut 1 (stripP ++ phaseTwoBlk phaseTwoMacroA_rhs n ++ phaseTwoMacroM_rhs) = 9 := by
    rw [morseOut_append, hu1, hMo]
  have hu3 : morseOut 1 (stripP ++ phaseTwoBlk phaseTwoMacroA_rhs n ++ phaseTwoMacroM_rhs ++
      phaseTwoBlk phaseTwoMacroB_rhs n) = 9 := by
    rw [morseOut_append, hu2, morseOut_phaseTwoBlk 9 n _ hBo]
  have h1 := morseReach_blocks 1 3 n stripP
    (phaseTwoMacroM_lhs ++ phaseTwoBlk phaseTwoMacroB_lhs n ++ phaseTwoMacroQ_lhs)
    _ _ morseReach_phaseTwoMacroA phaseTwoMacroA_fits hAo hP
  have h2 := morseReach_frame 3 1 0 0 (stripP ++ phaseTwoBlk phaseTwoMacroA_rhs n)
    (phaseTwoBlk phaseTwoMacroB_lhs n ++ phaseTwoMacroQ_lhs)
    _ _ morseReach_phaseTwoMacroM phaseTwoMacroM_fits hu1
  have h3 := morseReach_blocks 1 9 n
    (stripP ++ phaseTwoBlk phaseTwoMacroA_rhs n ++ phaseTwoMacroM_rhs) phaseTwoMacroQ_lhs
    _ _ morseReach_phaseTwoMacroB phaseTwoMacroB_fits hBo hu2
  have h4 := morseReach_frame 9 1 0 0 (stripP ++ phaseTwoBlk phaseTwoMacroA_rhs n ++
      phaseTwoMacroM_rhs ++ phaseTwoBlk phaseTwoMacroB_rhs n) []
    _ _ morseReach_phaseTwoMacroQ phaseTwoMacroQ_fits hu3
  rw [morseShiftWord_zero_stageN, morseShiftWord_zero_stageN] at h2 h4
  rw [stripWord_eq_phaseTwoW0]
  simp only [phaseTwoW0, phaseTwoWN, List.append_assoc, List.append_nil] at h1 h2 h3 h4 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 (morseReach_trans h3 h4))

end AJConjecture
