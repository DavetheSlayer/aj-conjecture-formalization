import Mathlib
import AJHandoff.TorusKnot.PairKIsoCompReclose
import AJHandoff.TorusKnot.PairKIsoCompSlide

/-!
# The companion isotopy (one strand)

`morseReach_pairCore_torus`: the core reaches the long closure of `torusPairWord r s`:
`morseReach_pairCore_rev`, then the braid identity `morseReach_pairRevTorusWord` inside the long
closure (`morseReach_frame` with the cups as prefix), then the closure slide by `Δ'`.
-/

namespace AJConjecture

/-- A braid word on `n` strands fits on `n` strands as a Morse word. -/
private theorem morseFits_morseOfBraid_companion {n : ℕ} {w : BraidWord} (hw : IsOnStrands n w) :
    morseFits n (morseOfBraid w) = true := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    have hg := hw g List.mem_cons_self
    have ih' := ih fun x hx ↦ hw x (List.mem_cons_of_mem _ hx)
    simp only [morseOfBraid, List.map_cons, morseFits_cons] at ih' ⊢
    refine ⟨by simp only [morseKindIn]; omega, ?_⟩
    simpa only [morseLetterOut, morseKindOut, morseKindIn, Nat.add_sub_cancel] using ih'

/-- The cups of a long closure add two strands each. -/
private theorem morseOut_closureCups_companion (n k : ℕ) :
    morseOut n ((List.range k).map fun j ↦ (MorseKind.cup, j + 1)) = n + 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, morseOut_append, ih]
    simp only [List.map_cons, List.map_nil, morseOut, morseLetterOut, morseKindOut, morseKindIn]
    omega

/-- The companion isotopy. -/
theorem morseReach_pairCore_torus {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairCore r s) (morseLongClosure r (torusPairWord r s)) := by
  have hR : IsOnStrands r (pairRevTorusWord r s) := fun g hg ↦ by
    simp only [pairRevTorusWord, List.mem_flatten, List.mem_replicate] at hg
    obtain ⟨l, ⟨-, rfl⟩, hg⟩ := hg
    simp only [List.mem_map, List.mem_reverse, List.mem_range] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    dsimp only
    omega
  have h2 := morseReach_frame r 1 0 (r - 1)
    ((List.range (r - 1)).map fun j ↦ (MorseKind.cup, j + 1))
    ((List.range (r - 1)).reverse.map fun j ↦ (MorseKind.cap, j + 1)) _ _
    (morseReach_pairRevTorusWord r s (by omega)) (morseFits_morseOfBraid_companion hR)
    (by rw [morseOut_closureCups_companion]; omega)
  have hs : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  have h0 : ∀ w : MorseWord, morseShiftWord 0 w = w := fun w ↦ by
    simp [morseShiftWord, hs]
  rw [h0, h0] at h2
  have hg : ∀ x ∈ pairGarsideTail r, 1 ≤ x.1 ∧ x.1 + 2 ≤ r := fun x hx ↦ by
    simp only [pairGarsideTail, List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_reverse] at hx
    obtain ⟨a, ha, i, hi, rfl⟩ := hx
    dsimp only
    omega
  have h3 := morseReach_closureSlide r (pairGarsideTail r) (torusPairWord r s) hg
    (isOnStrands_torusPairWord r s)
  exact morseReach_trans (morseReach_pairCore_rev h hr) (morseReach_trans h2 h3)

end AJConjecture
