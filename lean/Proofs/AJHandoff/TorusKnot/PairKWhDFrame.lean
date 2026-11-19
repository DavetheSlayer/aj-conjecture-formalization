import Mathlib
import AJHandoff.TorusKnot.PairKWhDDefs
import AJHandoff.TorusKnot.PairKIsoDouble

/-!
# The double of a reachability, framed into the Whitehead double

`morseReach_whDouble_of_writhe`: if `D` reaches `D'` by the moves of the checker and the two
diagrams have the same oriented writhe, then `whDouble D` reaches `whDouble D'`. The doubled
reachability is `morseReach_morseDouble` (`PairKIsoDouble`, generic); it is placed between the
first cup and the twists, clasp and last cap by `morseReach_frame` (one idle strand on the
right). The writhe hypothesis is discharged by `morseWrithe_eq_of_morseReach`
(`PairKWhDOrientReach`): every move preserves the oriented writhe.
-/

namespace AJConjecture

/-- The double of a fitting letter fits on twice the strands and doubles their number. -/
private theorem morseDoubleLetter_fits_whd (n : ℕ) (l : MorseLetter)
    (h : l.2 + morseKindIn l.1 ≤ n) :
    morseFits (2 * n) (morseDoubleLetter l) = true ∧
      morseOut (2 * n) (morseDoubleLetter l) = 2 * morseLetterOut n l := by
  obtain ⟨k, i⟩ := l
  cases k with
  | cup =>
    simp only [morseKindIn] at h
    simp only [morseDoubleLetter, morseFits, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, Bool.and_true, Bool.and_eq_true]
    exact ⟨⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩, by omega⟩
  | cap =>
    simp only [morseKindIn] at h
    simp only [morseDoubleLetter, morseFits, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, Bool.and_true, Bool.and_eq_true]
    exact ⟨⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩, by omega⟩
  | cross s =>
    simp only [morseKindIn] at h
    cases s <;>
    · simp only [morseDoubleLetter, cable, cableGen, morseOfBraid, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, Bool.false_eq_true, ↓reduceIte,
        show List.range 2 = [0, 1] from rfl, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.map_cons, List.map_nil, List.flatMap_cons, morseFits, morseOut,
        morseLetterOut, morseKindIn, morseKindOut, Bool.and_true, Bool.and_eq_true]
      exact ⟨⟨decide_eq_true (by omega), decide_eq_true (by omega), decide_eq_true (by omega),
        decide_eq_true (by omega)⟩, by omega⟩

/-- The double of a fitting word fits on twice the strands and doubles their number. -/
theorem morseDouble_fits_whd :
    ∀ (w : MorseWord) (n : ℕ), morseFits n w = true →
      morseFits (2 * n) (morseDouble w) = true ∧
        morseOut (2 * n) (morseDouble w) = 2 * morseOut n w
  | [], _, _ => ⟨rfl, rfl⟩
  | l :: w, n, h => by
    rw [morseFits_cons] at h
    have hl := morseDoubleLetter_fits_whd n l h.1
    have hw := morseDouble_fits_whd w _ h.2
    rw [show morseDouble (l :: w) = morseDoubleLetter l ++ morseDouble w from List.flatMap_cons,
      morseFits_append, morseOut_append, hl.1, hl.2, hw.1, hw.2]
    exact ⟨rfl, rfl⟩

/-- Shifting by zero does nothing. -/
private theorem morseShiftWord_zero_whd (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- Doubling a reachability of long-knot diagrams with equal oriented writhes gives a
reachability of their Whitehead doubles. -/
theorem morseReach_whDouble_of_writhe {D D' : MorseWord} (hD : morseFits 1 D = true)
    (h : MorseReach 1 D D') (hw : morseWrithe D = morseWrithe D') :
    MorseReach 1 (whDouble D) (whDouble D') := by
  have h2 : MorseReach 2 (morseDouble D) (morseDouble D') := morseReach_morseDouble h hD
  have hF := morseReach_frame 2 1 0 1 [(.cup, 1)]
    (bandUntwist (morseWrithe D) ++ claspWord ++ [(.cap, 1)]) (morseDouble D) (morseDouble D')
    h2 (morseDouble_fits_whd D 1 hD).1 rfl
  rw [morseShiftWord_zero_whd, morseShiftWord_zero_whd] at hF
  simpa only [whDouble, whBand, hw, List.append_assoc] using hF

end AJConjecture
