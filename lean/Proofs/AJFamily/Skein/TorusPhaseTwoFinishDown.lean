import Mathlib
import AJFamily.Skein.TorusPhaseTwoFinishEnd
import AJFamily.Skein.TorusPhaseTwoGadget
import AJFamily.Skein.TorusPhaseTwoPass
import AJFamily.Skein.MorsePhaseTools
import AJFamily.Skein.TorusPhaseTwoFinishWords

/-!
# Stage E: the curl passes a doubled crossing downwards

The travelling curl passes one doubled crossing downwards, on the return strand
(`phaseTwo_E_downStepR`) and on the closing arc (`phaseTwo_E_downStepA`), by exchanges: the doubled
crossing is a word of crossings on strands disjoint from the curl.
-/

namespace AJConjecture

/-- Blocks of doubled crossings do not change the number of strands. -/
private theorem morseOut_phaseTwoBlk_finishDown (n m : ℕ) :
    morseOut n (phaseTwoBlk phaseTwoD m) = n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show phaseTwoBlk phaseTwoD (m + 1) = phaseTwoD ++ phaseTwoBlk phaseTwoD m by
      simp [phaseTwoBlk, List.replicate_succ], morseOut_append, morseOut_phaseTwoD, ih]

/-- A curl on strands `≥ 4` passes one doubled crossing downwards. -/
private theorem morseReach_curl_down_finishDown (k m : ℕ) (hm : m < 2 * k + 1) (c : MorseWord)
    (hpos : ∀ a ∈ c, 4 ≤ a.2) (hfit : morseFits 7 (c ++ phaseTwoD) = true) :
    MorseReach 1 (phaseTwoEPre (m + 1) ++ c ++ phaseTwoBlk phaseTwoD (2 * k + 1 - (m + 1)) ++
        phaseTwoETail k)
      (phaseTwoEPre m ++ c ++ phaseTwoBlk phaseTwoD (2 * k + 1 - m) ++ phaseTwoETail k) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * k + 1 - m = n + 1 := ⟨2 * k + 1 - (m + 1), by omega⟩
  rw [hn, show 2 * k + 1 - (m + 1) = n by omega]
  have hpre : phaseTwoEPre (m + 1) = phaseTwoEPre m ++ phaseTwoD := by
    simp [phaseTwoEPre, phaseTwoBlk, List.replicate_succ', List.flatten_append]
  have hblk : phaseTwoBlk phaseTwoD (n + 1) = phaseTwoD ++ phaseTwoBlk phaseTwoD n := by
    simp [phaseTwoBlk, List.replicate_succ]
  have h := morseReach_symm (morseReach_comm 1 (phaseTwoEPre m) phaseTwoD c
    (phaseTwoBlk phaseTwoD n ++ phaseTwoETail k)
    (fun b hb ↦ by
      simp only [phaseTwoD, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨true, rfl⟩)
    (fun b hb a ha ↦ by
      have := hpos a ha
      simp only [phaseTwoD, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> simp only <;> omega)
    (by rw [morseOut_phaseTwoEPre]; exact hfit))
  rw [hpre, hblk]
  simpa only [List.append_assoc] using h

/-- The curl on the return strand passes one doubled crossing downwards (`morseReach_comm`). -/
theorem phaseTwo_E_downStepR (k m : ℕ) (hm : m < 2 * k + 1) :
    MorseReach 1 (phaseTwoER k (m + 1)) (phaseTwoER k m) :=
  morseReach_curl_down_finishDown k m hm _
    (fun a ha ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> decide)
    (by decide)

/-- The curl on the closing arc passes one doubled crossing downwards (`morseReach_comm`). -/
theorem phaseTwo_E_downStepA (k m : ℕ) (hm : m < 2 * k + 1) :
    MorseReach 1 (phaseTwoEA k (m + 1)) (phaseTwoEA k m) :=
  morseReach_curl_down_finishDown k m hm _
    (fun a ha ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> decide)
    (by decide)

end AJConjecture
