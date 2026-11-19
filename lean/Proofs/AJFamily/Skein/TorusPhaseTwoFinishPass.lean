import Mathlib
import AJFamily.Skein.TorusPhaseTwoFinishEnd
import AJFamily.Skein.TorusPhaseTwoGadget
import AJFamily.Skein.TorusPhaseTwoPass
import AJFamily.Skein.MorseFrame
import AJFamily.Skein.MorsePhaseTools
import AJFamily.Skein.TorusPhaseTwoFinishMacros
import AJFamily.Skein.TorusPhaseTwoFinishWords

/-!
# Stage E: the curl passes a doubled crossing upwards

`phaseTwo_E_passStep`: on a pass of the band the travelling curl passes one doubled crossing upwards
and changes strand (macro `CU13` or `CU31`, framed after the prefix `phaseTwoEPre m`).
-/

namespace AJConjecture

/-- Shifting by zero strands does nothing. -/
private theorem morseShiftWord_zero_finishPass (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- Blocks of doubled crossings do not change the number of strands. -/
private theorem morseOut_phaseTwoBlk_finishPass (n m : ℕ) :
    morseOut n (phaseTwoBlk phaseTwoD m) = n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show phaseTwoBlk phaseTwoD (m + 1) = phaseTwoD ++ phaseTwoBlk phaseTwoD m by
      simp [phaseTwoBlk, List.replicate_succ], morseOut_append, morseOut_phaseTwoD, ih]

/-- The travelling curl passes one doubled crossing upwards and changes strand
(macros `CU13` and `CU31`, framed on seven strands). -/
private theorem morseReach_curl_up_finishPass (b : Bool) (u v : MorseWord)
    (hu : morseOut 1 u = 7) :
    MorseReach 1 (u ++ (phaseTwoECurl b ++ phaseTwoD) ++ v)
      (u ++ (phaseTwoD ++ phaseTwoECurl (!b)) ++ v) := by
  cases b
  · have h := morseReach_frame 7 1 0 0 u v _ _ morseReach_phaseTwoMacroCU31
      phaseTwoMacroCU31_fits (by rw [hu])
    rw [morseShiftWord_zero_finishPass, morseShiftWord_zero_finishPass] at h
    exact h
  · have h := morseReach_frame 7 1 0 0 u v _ _ morseReach_phaseTwoMacroCU13
      phaseTwoMacroCU13_fits (by rw [hu])
    rw [morseShiftWord_zero_finishPass, morseShiftWord_zero_finishPass] at h
    exact h

/-- The curl passes one doubled crossing upwards: macro `CU13` or `CU31` (frame at the prefix
`phaseTwoEPre m`, 7 strands). -/
theorem phaseTwo_E_passStep (k m : ℕ) (s : Bool) (hm : m < 2 * k + 1) :
    MorseReach 1 (phaseTwoEP k m s) (phaseTwoEP k (m + 1) s) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * k + 1 - m = n + 1 := ⟨2 * k + 1 - (m + 1), by omega⟩
  have hpre : phaseTwoEPre (m + 1) = phaseTwoEPre m ++ phaseTwoD := by
    simp [phaseTwoEPre, phaseTwoBlk, List.replicate_succ', List.flatten_append]
  have hblk : phaseTwoBlk phaseTwoD (n + 1) = phaseTwoD ++ phaseTwoBlk phaseTwoD n := by
    simp [phaseTwoBlk, List.replicate_succ]
  have hpar : (s == decide ((m + 1) % 2 = 0)) = !(s == decide (m % 2 = 0)) := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> cases s <;>
      simp [h, Nat.succ_mod_two_eq_zero_iff]
  have h := morseReach_curl_up_finishPass (s == decide (m % 2 = 0)) (phaseTwoEPre m)
    (phaseTwoBlk phaseTwoD n ++ phaseTwoETail k) (morseOut_phaseTwoEPre m)
  unfold phaseTwoEP
  rw [hn, show 2 * k + 1 - (m + 1) = n by omega, hpre, hblk, hpar]
  simpa only [List.append_assoc] using h

end AJConjecture
