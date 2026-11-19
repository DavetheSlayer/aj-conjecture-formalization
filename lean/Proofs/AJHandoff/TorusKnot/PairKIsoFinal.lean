import Mathlib
import AJHandoff.TorusKnot.PairKIsoEndFix
import AJHandoff.TorusKnot.PairKIsoEndPark
import AJHandoff.TorusKnot.PairKIsoDouble
import AJHandoff.TorusKnot.PairKIsoCompanion
import AJHandoff.TorusKnot.PairKIsoSwing

/-!
# Assembly of the isotopy for `r ≥ 3`

`morseReach_pairWE_target`: the companion isotopy `morseReach_pairCore_torus`, doubled
(`morseReach_morseDouble`) and framed after the first cup (`morseReach_frame`, prefix `[u1]` on
`2 + 1` strands), turns `pairWE` into `pairTargetWord`.

`morseReach_pair_source_target_ge3`: the chain of junction words

`source → pairStrip → pairWN → pairWS → pairWP1 → pairWP2 → pairWP3 → pairWP → pairWPb → pairWC →
pairWG1 → pairWG2 → pairWE1 → pairWE3 → pairWE4 → pairWE → pairTargetWord`.
-/

namespace AJConjecture

/-- The double of a fitting letter fits on twice the strands and doubles their number. -/
private theorem morseDoubleLetter_fits_final (n : ℕ) (l : MorseLetter)
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

/-- The double of a fitting word fits on twice the strands. -/
private theorem morseDouble_fits_final :
    ∀ (w : MorseWord) (n : ℕ), morseFits n w = true →
      morseFits (2 * n) (morseDouble w) = true ∧
        morseOut (2 * n) (morseDouble w) = 2 * morseOut n w
  | [], _, _ => ⟨rfl, rfl⟩
  | l :: w, n, h => by
    rw [morseFits_cons] at h
    have hl := morseDoubleLetter_fits_final n l h.1
    have hw := morseDouble_fits_final w _ h.2
    rw [show morseDouble (l :: w) = morseDoubleLetter l ++ morseDouble w from List.flatMap_cons,
      morseFits_append, morseOut_append, hl.1, hl.2, hw.1, hw.2]
    exact ⟨rfl, rfl⟩

/-- The doubled companion isotopy. -/
theorem morseReach_pairWE_target {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWE r s) (pairTargetWord r s) := by
  have hf := (morseFits_pairCore h hr).1
  have hd := morseReach_morseDouble (morseReach_pairCore_torus h hr) hf
  have hF := morseReach_frame 2 1 0 1 [isoU 1]
    (List.replicate (2 * ((r - 1) * s)) (isoX false 0) ++ claspWord ++ [isoN 1]) _ _ hd
    (morseDouble_fits_final _ 1 hf).1 rfl
  rw [morseShiftWord_zero_iso, morseShiftWord_zero_iso] at hF
  simp only [pairWE, pairTargetWord, List.append_assoc] at hF ⊢
  exact hF

/-- The isotopy of Theorem T for `r ≥ 3`. -/
theorem morseReach_pair_source_target_ge3 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (morseLongClosure (pairStrands r s) (pairWhiteheadWord r s))
      (pairTargetWord r s) := by
  exact morseReach_trans (morseReach_pair_source_strip h hr) <|
    morseReach_trans (morseReach_pairStrip_WN h hr) <|
    morseReach_trans (morseReach_pairWN_WS h hr) <|
    morseReach_trans (morseReach_pairWS_WP1 h hr) <|
    morseReach_trans (morseReach_pairWP1_WP2 h hr) <|
    morseReach_trans (morseReach_pairWP2_WP3 h hr) <|
    morseReach_trans (morseReach_pairWP3_WP h hr) <|
    morseReach_trans (morseReach_pairWP_WPb h hr) <|
    morseReach_trans (morseReach_pairWPb_WC h hr) <|
    morseReach_trans (morseReach_pairWC_WG1 h hr) <|
    morseReach_trans (morseReach_pairWG1_WG2 h hr) <|
    morseReach_trans (morseReach_pairWG2_WE1 h hr) <|
    morseReach_trans (morseReach_pairWE1_WE3 h hr) <|
    morseReach_trans (morseReach_pairWE3_WE4 h hr) <|
    morseReach_trans (morseReach_pairWE4_WE h hr) (morseReach_pairWE_target h hr)

end AJConjecture
