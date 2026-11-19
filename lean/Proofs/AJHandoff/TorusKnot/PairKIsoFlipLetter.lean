import Mathlib
import AJHandoff.TorusKnot.PairKIsoWords

/-!
# The flip of a return strand passes one crossing

During the thinning of a disc its return strand `R` is pushed up through the word as a walk
`morseWalk true p ℓ` (`R` enters at the position `p`, just right of the strand of the disc, and
crosses over the `ℓ` strands inside the loop). A crossing letter met by the walk falls into one of
three cases:

* it lies left of `R` (`i + 2 ≤ p`): the two commute (`morseReach_comm`);
* it lies among the strands crossed by `R` (`p ≤ i`, `i + 2 ≤ p + ℓ`): it passes the walk and is
  shifted one place to the right (`morseReach_pass` with a one-letter tangle);
* it crosses the strand of the disc with the first inner strand (`i + 1 = p`): after the flip it
  becomes the signed band `b(p - 1, p + 1)` around `R` (`R` passes over both of its strands).

Generic in all parameters; the three statements are the letter steps of
`AJHandoff.TorusKnot.PairKIsoFlip`.
-/

namespace AJConjecture

/-- A crossing left of the walk commutes with it. -/
theorem morseReach_isoWalk_left (n₀ p ℓ i : ℕ) (s : Bool) (u v : MorseWord)
    (hi : i + 2 ≤ p) (hu : p + ℓ + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseWalk true p ℓ ++ [isoX s i] ++ v)
      (u ++ [isoX s i] ++ morseWalk true p ℓ ++ v) := by
  refine morseReach_comm n₀ u [isoX s i] (morseWalk true p ℓ) v
    (fun b hb ↦ by rw [List.mem_singleton.mp hb]; exact ⟨s, rfl⟩)
    (fun b hb a ha ↦ by
      rw [List.mem_singleton.mp hb]
      have := mem_morseWalk ha
      simp only [isoX]
      omega) ?_
  rw [morseFits_append, morseOut_morseWalk, Bool.and_eq_true]
  refine ⟨morseFits_of_cross _ _ (fun b hb ↦ ⟨true, (mem_morseWalk hb).1⟩) fun b hb ↦ ?_, ?_⟩
  · have := mem_morseWalk hb
    omega
  · simp only [isoX, morseFits_cons, morseKindIn, morseFits_nil, and_true]
    omega

/-- A crossing among the strands crossed by the walk passes it, one place further right. -/
theorem morseReach_isoWalk_inner (n₀ p ℓ i : ℕ) (s : Bool) (u v : MorseWord)
    (hi : p ≤ i) (hi' : i + 2 ≤ p + ℓ) (hu : p + ℓ + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseWalk true p ℓ ++ [isoX s i] ++ v)
      (u ++ [isoX s (i + 1)] ++ morseWalk true p ℓ ++ v) := by
  have h := morseReach_pass n₀ p ℓ true u [isoX s (i - p)] v (by
    simp only [isoX, morseFits_cons, morseKindIn, morseFits_nil, and_true]
    omega) hu
  have e1 : morseShiftWord p [isoX s (i - p)] = [isoX s i] := by
    simp only [morseShiftWord, List.map_cons, List.map_nil, shiftLetter, isoX, List.cons.injEq,
      Prod.mk.injEq, true_and, and_true]
    omega
  have e2 : morseShiftWord (p + 1) [isoX s (i - p)] = [isoX s (i + 1)] := by
    simp only [morseShiftWord, List.map_cons, List.map_nil, shiftLetter, isoX, List.cons.injEq,
      Prod.mk.injEq, true_and, and_true]
    omega
  have e3 : morseOut ℓ [isoX s (i - p)] = ℓ := by
    simp only [isoX, morseOut, morseLetterOut, morseKindOut, morseKindIn]
    omega
  rwa [e1, e2, e3] at h

/-- A crossing of the disc strand with the first inner strand becomes a band around the return
strand. -/
theorem morseReach_isoWalk_boundary (n₀ p ℓ : ℕ) (s : Bool) (u v : MorseWord)
    (hp : 1 ≤ p) (hℓ : 1 ≤ ℓ) (hu : p + ℓ + 1 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseWalk true p ℓ ++ [isoX s (p - 1)] ++ v)
      (u ++ isoBand (p - 1) (p + 1) s ++ morseWalk true p ℓ ++ v) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have hw : morseWalk true p (k + 1) = isoX true p :: morseWalk true (p + 1) k := by
    simp only [morseWalk, List.range_succ_eq_map, List.map_cons, List.map_map, isoX,
      Nat.add_zero, List.cons.injEq, true_and]
    exact List.map_congr_left fun t _ ↦ by
      simp only [Function.comp_apply, Prod.mk.injEq, true_and]; omega
  have hb : isoBand (p - 1) (p + 1) s = [isoX true p, isoX s (p - 1), isoX false p] := by
    simp only [isoBand, bandWord, morseOfBraid, isoX, show p + 1 - 1 - (p - 1) = 1 by omega,
      List.range_one, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have h1 := morseReach_isoWalk_left n₀ (p + 1) k (p - 1) s (u ++ [isoX true p]) v (by omega)
    (by
      rw [morseOut_append]
      simp only [isoX, morseOut, morseLetterOut, morseKindOut, morseKindIn]
      omega)
  have h2 := morseReach_symm (morseReach_isoRule n₀ (u ++ [isoX true p] ++ [isoX s (p - 1)])
    (morseWalk true (p + 1) k ++ v) (.r2 p false) rfl
    (by
      simp only [morseOut_append, isoX, morseOut, morseLetterOut, morseKindOut, morseKindIn,
        morseRuleLhs, morseFits_cons, morseFits_nil, and_true, Bool.not_false]
      omega)
    rfl)
  rw [hw, hb]
  simp only [morseRuleLhs, morseRuleRhs, List.append_nil, Bool.not_false] at h2
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
  exact morseReach_trans h1 h2

end AJConjecture
