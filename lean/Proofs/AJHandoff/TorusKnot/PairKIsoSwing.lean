import Mathlib
import AJHandoff.TorusKnot.PairKIsoStageN

/-!
# Stage S: the return strand swings to the right

In `pairWN` the strand left of the band (the left leg of the first cup, after `u1 +0`) is the
return strand; it runs up the far left until the cap of `+0 n1`. As in the library's stage S
(`AJFamily.Skein.TorusPhaseTwoSwing`): the cap moves to the end of the word and one `r2` read
backwards inserts `+1 −1` (macro `RC'`, fixed, on `7` strands); the walk `+0 +1` passes the whole
band `pairSwingT r s` read backwards (`morseReach_pass`, generic, any length); the library macros
`SB` (`u1 +0 +0 +1 → u1 · phaseTwoA1`) and `TC` (`−1 n1 → u1 +2 n1 n1`) tidy the two ends.
Validated outside Lean (writhe, rotation, Jones; `SCR/ISO/tools/lean_words.py`).
-/

namespace AJConjecture

/-- The band in band coordinates, from the first block to the last caps of the Hopf disc. -/
def pairSwingT (r s : ℕ) : MorseWord :=
  pairBandMid r s ++ [isoU 3, isoX false 4, isoN 3, isoN 3, isoN 2]

/-- After macro `RC'`. -/
def pairWS1 (r s : ℕ) : MorseWord :=
  [isoU 1, isoX true 0] ++ morseShiftWord 1 (pairSwingT r s) ++
    [isoX true 0, isoX true 1, isoX false 1, isoN 1]

/-- After the swing of the walk below the band. -/
def pairWS2 (r s : ℕ) : MorseWord :=
  [isoU 1, isoX true 0, isoX true 0, isoX true 1] ++ pairSwingT r s ++ [isoX false 1, isoN 1]

/-- After macro `SB`. -/
def pairWS3 (r s : ℕ) : MorseWord :=
  [isoU 1] ++ phaseTwoA1 ++ pairSwingT r s ++ [isoX false 1, isoN 1]

/-- The word after stage S (after macro `TC`). -/
def pairWS (r s : ℕ) : MorseWord :=
  [isoU 1] ++ phaseTwoA1 ++ pairSwingT r s ++ [isoU 1, isoX true 2, isoN 1, isoN 1]

/-- Shifting by zero does nothing. -/
private theorem morseShiftWord_zero_swing (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- Removing `d` idle strands on the left of a fitting shifted word. -/
private theorem morseFits_unshift_swing (d : ℕ) (w : MorseWord) :
    ∀ n, morseFits (d + n) (morseShiftWord d w) = true →
      morseFits n w = true ∧ morseOut (d + n) (morseShiftWord d w) = d + morseOut n w := by
  induction w with
  | nil => intro n _; exact ⟨rfl, rfl⟩
  | cons l w ih =>
    intro n h
    simp only [morseShiftWord, List.map_cons, morseFits_cons, shiftLetter, morseOut] at h ⊢
    obtain ⟨h1, h2⟩ := h
    have hl : morseLetterOut (d + n) (l.1, l.2 + d) = d + morseLetterOut n l := by
      simp only [morseLetterOut]
      omega
    rw [hl] at h2 ⊢
    obtain ⟨h3, h4⟩ := ih _ h2
    exact ⟨⟨by omega, h3⟩, h4⟩

/-- The band of the normal form fits on two strands and ends on six. -/
private theorem morseFits_pairBandMid_swing {r s : ℕ} (hr : 3 ≤ r) :
    morseFits 2 (pairBandMid r s) = true ∧ morseOut 2 (pairBandMid r s) = 6 := by
  obtain ⟨hf, ho⟩ := morseFits_pairWN (s := s) hr
  rw [pairWN] at hf ho
  simp only [morseFits_append, morseOut_append, Bool.and_eq_true] at hf ho
  obtain ⟨⟨⟨-, hB⟩, hT⟩, -⟩ := hf
  have h3 : morseOut 1 [isoU 1, isoX true 0] = 1 + 2 := rfl
  rw [h3] at hB hT ho
  obtain ⟨hB', hBo⟩ := morseFits_unshift_swing 1 _ 2 hB
  rw [hBo] at hT ho
  simp only [isoFinalNF, morseOut, morseLetterOut, morseFits_cons, morseFits_nil, isoX, isoN, isoU,
    morseKindIn, morseKindOut, and_true] at hT ho
  exact ⟨hB', by omega⟩

/-- Macro `RC'`: the cap of the return strand moves past the last caps, `r2` read backwards. -/
theorem morseReach_isoMacroRC :
    MorseReach 7 ([isoX true 0, isoN 1] ++ isoFinalNF)
      (morseShiftWord 1 [isoU 3, isoX false 4, isoN 3, isoN 3, isoN 2] ++
        [isoX true 0, isoX true 1, isoX false 1, isoN 1]) :=
  ⟨[(1, .exch (.cap, 1) (.cup, 4), false), (0, .exch (.cross true, 0) (.cup, 4), false),
    (2, .exch (.cap, 1) (.cross false, 5), false),
    (1, .exch (.cross true, 0) (.cross false, 5), false), (3, .exch (.cap, 1) (.cap, 4), false),
    (4, .exch (.cap, 1) (.cap, 4), false), (5, .exch (.cap, 1) (.cap, 3), false),
    (6, .r2 1 true, true), (2, .exch (.cross true, 0) (.cap, 4), false),
    (3, .exch (.cross true, 0) (.cap, 4), false), (4, .exch (.cross true, 0) (.cap, 3), false)],
    by decide⟩

set_option linter.unusedVariables false in
/-- The band fits on two strands and ends on two strands. -/
theorem morseFits_pairSwingT {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    morseFits 2 (pairSwingT r s) = true ∧ morseOut 2 (pairSwingT r s) = 2 := by
  obtain ⟨hf, ho⟩ := morseFits_pairBandMid_swing (s := s) hr
  rw [pairSwingT, morseFits_append, morseOut_append, hf, ho]
  decide

/-- Stage S: `pairWN → pairWS1 → pairWS2 → pairWS3 → pairWS`. -/
theorem morseReach_pairWN_WS {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWN r s) (pairWS r s) := by
  obtain ⟨hB, hBo⟩ := morseFits_pairBandMid_swing (s := s) hr
  obtain ⟨hT, hTo⟩ := morseFits_pairSwingT h hr
  have hu : morseOut 1 ([isoU 1, isoX true 0] ++ morseShiftWord 1 (pairBandMid r s)) = 7 := by
    rw [morseOut_append, show morseOut 1 [isoU 1, isoX true 0] = 1 + 2 + 0 from rfl,
      (morseOut_fits_shift 2 1 0 _ hB).1, hBo]
  have s1 := morseReach_frame 7 1 0 0 ([isoU 1, isoX true 0] ++ morseShiftWord 1 (pairBandMid r s))
    [] _ _ morseReach_isoMacroRC (by decide) (by rw [hu])
  have s2 := morseReach_symm (morseReach_pass 1 0 2 true [isoU 1, isoX true 0] (pairSwingT r s)
    [isoX false 1, isoN 1] hT (by decide))
  have s3 := morseReach_frame 1 1 0 0 [] (pairSwingT r s ++ [isoX false 1, isoN 1]) _ _
    morseReach_phaseTwoMacroSB phaseTwoMacroSB_fits rfl
  have hT3 : morseOut 1 ([isoU 1] ++ phaseTwoA1 ++ pairSwingT r s) = 0 + 3 + 0 := by
    rw [morseOut_append, show morseOut 1 ([isoU 1] ++ phaseTwoA1) = 0 + 2 + 1 from rfl,
      ← morseShiftWord_zero_swing (pairSwingT r s), (morseOut_fits_shift 2 0 1 _ hT).1, hTo]
  have s4 := morseReach_frame 3 1 0 0 ([isoU 1] ++ phaseTwoA1 ++ pairSwingT r s) [] _ _
    morseReach_phaseTwoMacroTC phaseTwoMacroTC_fits hT3
  simp only [morseShiftWord_zero_swing, List.append_nil] at s1 s3 s4
  rw [hTo, show morseWalk true 0 2 = [isoX true 0, isoX true 1] from rfl,
    morseShiftWord_zero_swing] at s2
  have a1 : MorseReach 1 (pairWN r s) (pairWS1 r s) := by
    simpa only [pairWN, pairWS1, pairSwingT, morseShiftWord_append, List.append_assoc,
      List.cons_append, List.nil_append] using s1
  have a2 : MorseReach 1 (pairWS1 r s) (pairWS2 r s) := by
    simpa only [pairWS1, pairWS2, Nat.zero_add, List.append_assoc, List.cons_append,
      List.nil_append] using s2
  have a3 : MorseReach 1 (pairWS2 r s) (pairWS3 r s) := by
    simpa only [pairWS2, pairWS3, phaseTwoMacroSB_lhs, phaseTwoMacroSB_rhs, phaseTwoA1, isoU,
      isoX, List.append_assoc, List.cons_append, List.nil_append] using s3
  have a4 : MorseReach 1 (pairWS3 r s) (pairWS r s) := by
    simpa only [pairWS3, pairWS, phaseTwoMacroTC_lhs, phaseTwoMacroTC_rhs, isoU, isoX, isoN,
      List.append_assoc, List.cons_append, List.nil_append] using s4
  exact morseReach_trans a1 (morseReach_trans a2 (morseReach_trans a3 a4))

end AJConjecture
