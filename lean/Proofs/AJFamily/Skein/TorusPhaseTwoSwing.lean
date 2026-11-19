import Mathlib
import AJFamily.Skein.MorseFrame
import AJFamily.Skein.MorsePhaseTools
import AJFamily.Skein.TorusPhaseTwoWords

/-!
# Stage S of phase II: the return strand swings to the far right

`phaseTwo_stageS`: in `phaseTwoWN k` the return strand runs up the far left. Macro `RC` moves its
cap to the end of the word, one inverse `r2` turns that end into a walk, and the walk passes the
whole band in between (`morseReach_pass` with the band as the tangle); macros `SB` and `TC` then
tidy the two ends, giving `phaseTwoWS k`.
-/

namespace AJConjecture

/-- The tail block after the swing without its last four letters `u1 +2 n1 n1`. -/
private def phaseTwoQ1Head : MorseWord :=
  phaseTwoD ++ [(.cross false, 2), (.cross false, 2), (.cup, 3), (.cross false, 4), (.cap, 3),
    (.cap, 3), (.cup, 3), (.cross false, 4), (.cap, 3), (.cap, 3), (.cap, 2)]

/-- The tangle `T` on two strands crossed by the swinging return strand. -/
private def phaseTwoSwingT (m : ℕ) : MorseWord :=
  phaseTwoBlk phaseTwoA1 m ++ phaseTwoM1 ++ phaseTwoBlk phaseTwoB1 m ++ phaseTwoQ1Head

/-- Macro `RC` followed by one inverse `r2` at the end. -/
private theorem morseReach_phaseTwoMacroRC_r2 :
    MorseReach 9 phaseTwoMacroRC_lhs
      (morseShiftWord 1 phaseTwoQ1Head ++
        [(.cross true, 0), (.cross true, 1), (.cross false, 1), (.cap, 1)]) := by
  refine morseReach_trans morseReach_phaseTwoMacroRC ⟨[(16, .r2 1 true, true)], ?_⟩
  decide

/-- Shifting commutes with taking blocks. -/
private theorem morseShiftWord_phaseTwoBlk_swing (d m : ℕ) (w : MorseWord) :
    morseShiftWord d (phaseTwoBlk w m) = phaseTwoBlk (morseShiftWord d w) m := by
  simp [morseShiftWord, phaseTwoBlk, List.map_flatten, List.map_replicate]

/-- Blocks of a strand-neutral word are strand-neutral. -/
theorem morseOut_phaseTwoBlk (n m : ℕ) (y : MorseWord) (hy : morseOut n y = n) :
    morseOut n (phaseTwoBlk y m) = n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show phaseTwoBlk y (m + 1) = y ++ phaseTwoBlk y m by
      simp [phaseTwoBlk, List.replicate_succ], morseOut_append, hy, ih]

/-- Blocks of a strand-neutral fitting word fit. -/
theorem morseFits_phaseTwoBlk (n m : ℕ) (y : MorseWord) (hf : morseFits n y = true)
    (hy : morseOut n y = n) : morseFits n (phaseTwoBlk y m) = true := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show phaseTwoBlk y (m + 1) = y ++ phaseTwoBlk y m by
      simp [phaseTwoBlk, List.replicate_succ], morseFits_append, hf, hy, ih]
    rfl

/-- Shifting by zero strands does nothing. -/
private theorem morseShiftWord_zero_swing (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- The tangle `T` fits on two strands. -/
private theorem morseFits_phaseTwoSwingT (m : ℕ) : morseFits 2 (phaseTwoSwingT m) = true := by
  have h1 : morseOut 2 phaseTwoA1 = 2 := by decide
  have h2 : morseOut 2 phaseTwoM1 = 8 := by decide
  have h3 : morseOut 8 phaseTwoB1 = 8 := by decide
  have f1 : morseFits 2 phaseTwoA1 = true := by decide
  have f2 : morseFits 2 phaseTwoM1 = true := by decide
  have f3 : morseFits 8 phaseTwoB1 = true := by decide
  have f4 : morseFits 8 phaseTwoQ1Head = true := by decide
  simp only [phaseTwoSwingT, morseFits_append, morseOut_append,
    morseOut_phaseTwoBlk 2 m _ h1, morseOut_phaseTwoBlk 8 m _ h3, h2,
    morseFits_phaseTwoBlk 2 m _ f1 h1, morseFits_phaseTwoBlk 8 m _ f3 h3, f2, f4,
    Bool.and_self]

/-- The tangle `T` has two outgoing strands. -/
private theorem morseOut_phaseTwoSwingT (n m : ℕ) (hn : n = 2 ∨ n = 3) :
    morseOut n (phaseTwoSwingT m) = n := by
  rcases hn with rfl | rfl
  · have h1 : morseOut 2 phaseTwoA1 = 2 := by decide
    have h2 : morseOut 2 phaseTwoM1 = 8 := by decide
    have h3 : morseOut 8 phaseTwoB1 = 8 := by decide
    have h4 : morseOut 8 phaseTwoQ1Head = 2 := by decide
    simp only [phaseTwoSwingT, morseOut_append, morseOut_phaseTwoBlk 2 m _ h1, h2,
      morseOut_phaseTwoBlk 8 m _ h3, h4]
  · have h1 : morseOut 3 phaseTwoA1 = 3 := by decide
    have h2 : morseOut 3 phaseTwoM1 = 9 := by decide
    have h3 : morseOut 9 phaseTwoB1 = 9 := by decide
    have h4 : morseOut 9 phaseTwoQ1Head = 3 := by decide
    simp only [phaseTwoSwingT, morseOut_append, morseOut_phaseTwoBlk 3 m _ h1, h2,
      morseOut_phaseTwoBlk 9 m _ h3, h4]

/-- Stage S: the return strand moves to the far right. -/
theorem phaseTwo_stageS (k : ℕ) (hk : 1 ≤ k) : MorseReach 1 (phaseTwoWN k) (phaseTwoWS k) := by
  set n := 2 * k - 1 with hn
  set T := phaseTwoSwingT n with hT
  have hP : morseOut 1 stripP = 3 := by decide
  have hAo : morseOut 3 phaseTwoMacroA_rhs = 3 := by decide
  have hMo : morseOut 3 phaseTwoMacroM_rhs = 9 := by decide
  have hBo : morseOut 9 phaseTwoMacroB_rhs = 9 := by decide
  have hu3 : morseOut 1 (stripP ++ phaseTwoBlk phaseTwoMacroA_rhs n ++ phaseTwoMacroM_rhs ++
      phaseTwoBlk phaseTwoMacroB_rhs n) = 9 := by
    rw [morseOut_append, morseOut_append, morseOut_append, hP, morseOut_phaseTwoBlk 3 n _ hAo,
      hMo, morseOut_phaseTwoBlk 9 n _ hBo]
  -- macro RC and one inverse r2
  have h1 := morseReach_frame 9 1 0 0 (stripP ++ phaseTwoBlk phaseTwoMacroA_rhs n ++
      phaseTwoMacroM_rhs ++ phaseTwoBlk phaseTwoMacroB_rhs n) []
    _ _ morseReach_phaseTwoMacroRC_r2 phaseTwoMacroRC_fits hu3
  rw [morseShiftWord_zero_swing, morseShiftWord_zero_swing] at h1
  have hA : morseShiftWord 1 phaseTwoA1 = phaseTwoMacroA_rhs := by decide
  have hM : morseShiftWord 1 phaseTwoM1 = phaseTwoMacroM_rhs := by decide
  have hB : morseShiftWord 1 phaseTwoB1 = phaseTwoMacroB_rhs := by decide
  have e1 : stripP ++ phaseTwoBlk phaseTwoMacroA_rhs n ++ phaseTwoMacroM_rhs ++
      phaseTwoBlk phaseTwoMacroB_rhs n ++ (morseShiftWord 1 phaseTwoQ1Head ++
        [(.cross true, 0), (.cross true, 1), (.cross false, 1), (.cap, 1)]) ++ [] =
      [(.cup, 1), (.cross true, 0)] ++ morseShiftWord 1 T ++ morseWalk true 0 (morseOut 2 T) ++
        [(.cross false, 1), (.cap, 1)] := by
    rw [morseOut_phaseTwoSwingT 2 n (Or.inl rfl)]
    simp only [hT, phaseTwoSwingT, morseShiftWord_append, morseShiftWord_phaseTwoBlk_swing, hA,
      hM, hB, stripP, List.append_assoc, List.append_nil]
    rfl
  -- the walk passes the tangle `T` (read backwards)
  have h2 := morseReach_symm (morseReach_pass 1 0 2 true [(.cup, 1), (.cross true, 0)] T
    [(.cross false, 1), (.cap, 1)] (morseFits_phaseTwoSwingT n) (by decide))
  rw [morseShiftWord_zero_swing] at h2
  -- macros SB and TC
  have h3 := morseReach_frame 1 1 0 0 [] (T ++ [(.cross false, 1), (.cap, 1)])
    _ _ morseReach_phaseTwoMacroSB phaseTwoMacroSB_fits rfl
  have hu4 : morseOut 1 ([] ++ phaseTwoMacroSB_rhs ++ T) = 3 := by
    rw [morseOut_append, show morseOut 1 ([] ++ phaseTwoMacroSB_rhs) = 3 by decide,
      morseOut_phaseTwoSwingT 3 n (Or.inr rfl)]
  have h4 := morseReach_frame 3 1 0 0 ([] ++ phaseTwoMacroSB_rhs ++ T) []
    _ _ morseReach_phaseTwoMacroTC phaseTwoMacroTC_fits hu4
  rw [morseShiftWord_zero_swing, morseShiftWord_zero_swing] at h3 h4
  have e2 : [(.cup, 1), (.cross true, 0)] ++ morseWalk true 0 2 ++ T ++
      [(.cross false, 1), (.cap, 1)] =
      [] ++ phaseTwoMacroSB_lhs ++ (T ++ [(.cross false, 1), (.cap, 1)]) := by
    simp only [List.append_assoc]
    rfl
  have e3 : [] ++ phaseTwoMacroSB_rhs ++ (T ++ [(.cross false, 1), (.cap, 1)]) =
      [] ++ phaseTwoMacroSB_rhs ++ T ++ phaseTwoMacroTC_lhs ++ [] := by
    simp only [List.append_assoc, List.append_nil]
    rfl
  have hWN : phaseTwoWN k = stripP ++ phaseTwoBlk phaseTwoMacroA_rhs n ++ phaseTwoMacroM_rhs ++
      phaseTwoBlk phaseTwoMacroB_rhs n ++ phaseTwoMacroRC_lhs ++ [] := by
    simp only [phaseTwoWN, List.append_nil]
    rfl
  have hWS : phaseTwoWS k = [] ++ phaseTwoMacroSB_rhs ++ T ++ phaseTwoMacroTC_rhs ++ [] := by
    have e : 2 * k = n + 1 := by omega
    simp only [phaseTwoWS, hT, phaseTwoSwingT, e, phaseTwoBlk, List.replicate_succ,
      List.flatten_cons, List.append_assoc, List.append_nil, List.nil_append]
    rfl
  rw [hWN, hWS]
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  exact morseReach_trans h1 (morseReach_trans h2 (morseReach_trans h3 h4))

end AJConjecture
