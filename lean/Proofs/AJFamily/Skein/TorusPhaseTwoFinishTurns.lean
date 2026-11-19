import Mathlib
import AJFamily.Skein.TorusPhaseTwoFinishEnd
import AJFamily.Skein.TorusPhaseTwoGadget
import AJFamily.Skein.TorusPhaseTwoPass
import AJFamily.Skein.MorseFrame
import AJFamily.Skein.MorsePhaseTools
import AJFamily.Skein.TorusPhaseTwoFinishMacros
import AJFamily.Skein.TorusPhaseTwoFinishWords

/-!
# Stage E: the turns

The fixed parts of the journey of the curl: macro `E1` (`phaseTwo_E1`), the passage onto the return
strand (`phaseTwo_E_toR`) and the turns around the first cup, the closing cap and the closing cup
(`phaseTwo_E_turnBottom`, `phaseTwo_E_turnCap`, `phaseTwo_E_turnCup`). Each is a fixed move list
applied with the frame lemma, plus exchanges past the blocks that depend on `k`.
-/

namespace AJConjecture

/-- Shifting by zero strands does nothing. -/
private theorem morseShiftWord_zero_turns (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- Blocks of doubled crossings do not change the number of strands. -/
private theorem morseOut_phaseTwoBlk_turns (n m : ℕ) :
    morseOut n (phaseTwoBlk phaseTwoD m) = n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show phaseTwoBlk phaseTwoD (m + 1) = phaseTwoD ++ phaseTwoBlk phaseTwoD m by
      simp [phaseTwoBlk, List.replicate_succ], morseOut_append, morseOut_phaseTwoD, ih]

/-- Macro `TurnBottom`, left side. -/
private def macroTurnBottom_lhs_turns : MorseWord :=
  [(.cup, 1), (.cup, 2), (.cup, 3), (.cup, 6), (.cross true, 7), (.cap, 6)]

/-- Macro `TurnBottom`, right side. -/
private def macroTurnBottom_rhs_turns : MorseWord :=
  [(.cup, 1), (.cup, 2), (.cup, 3), (.cup, 2), (.cross true, 1), (.cap, 2)]

/-- Macro `TurnBottom`, the moves (17). -/
private def macroTurnBottom_moves_turns : List MorseMove :=
  [(2, .exch (.cup, 3) (.cup, 4), false), (3, .exch (.cup, 3) (.cross true, 5), false),
    (4, .exch (.cup, 3) (.cap, 4), false), (1, .exch (.cup, 2) (.cup, 2), false),
    (2, .exch (.cup, 2) (.cross true, 3), false), (3, .exch (.cup, 2) (.cap, 2), false),
    (3, .r2 2 true, true), (1, .cupSlide 2 true false, false),
    (0, .exch (.cup, 1) (.cup, 1), false), (3, .r2 1 false, true),
    (1, .cupSlide 1 false false, false), (3, .exch (.cap, 2) (.cup, 4), false),
    (2, .exch (.cross true, 1) (.cup, 4), false), (1, .exch (.cup, 2) (.cup, 2), false),
    (4, .exch (.cap, 2) (.cup, 5), false), (3, .exch (.cross true, 1) (.cup, 5), false),
    (2, .exch (.cup, 2) (.cup, 3), false)]

/-- The left side of macro `TurnBottom` fits on 1 strand. -/
private theorem macroTurnBottom_fits_turns : morseFits 1 macroTurnBottom_lhs_turns = true := by
  decide

/-- Macro `TurnBottom` as a reachability statement (checked by `decide`). -/
private theorem morseReach_macroTurnBottom_turns :
    MorseReach 1 macroTurnBottom_lhs_turns macroTurnBottom_rhs_turns :=
  ⟨macroTurnBottom_moves_turns, by decide⟩

/-- Macro `TurnCap`, left side. -/
private def macroTurnCap_lhs_turns : MorseWord :=
  [(.cup, 4), (.cross true, 3), (.cap, 4), (.cap, 3), (.cap, 2)]

/-- Macro `TurnCap`, right side. -/
private def macroTurnCap_rhs_turns : MorseWord :=
  [(.cup, 4), (.cross true, 5), (.cap, 4), (.cap, 3), (.cap, 2)]

/-- Macro `TurnCap`, the moves (5). -/
private def macroTurnCap_moves_turns : List MorseMove :=
  [(2, .capSlide 3 false true, true), (1, .r2 3 true, false), (2, .exch (.cap, 3) (.cap, 5), false),
    (2, .capSlide 4 true true, true), (1, .r2 4 false, false)]

/-- The left side of macro `TurnCap` fits on 7 strands. -/
private theorem macroTurnCap_fits_turns : morseFits 7 macroTurnCap_lhs_turns = true := by
  decide

/-- Macro `TurnCap` as a reachability statement (checked by `decide`). -/
private theorem morseReach_macroTurnCap_turns :
    MorseReach 7 macroTurnCap_lhs_turns macroTurnCap_rhs_turns :=
  ⟨macroTurnCap_moves_turns, by decide⟩

/-- Macro `TurnCup`, left side. -/
private def macroTurnCup_lhs_turns : MorseWord :=
  [(.cup, 1), (.cup, 2), (.cup, 3), (.cup, 4), (.cross true, 5), (.cap, 4)]

/-- Macro `TurnCup`, right side. -/
private def macroTurnCup_rhs_turns : MorseWord :=
  [(.cup, 1), (.cup, 2), (.cup, 3), (.cup, 4), (.cross true, 3), (.cap, 4)]

/-- Macro `TurnCup`, the moves (5). -/
private def macroTurnCup_moves_turns : List MorseMove :=
  [(5, .r2 4 true, true), (3, .cupSlide 4 true false, false), (2, .exch (.cup, 3) (.cup, 3), false),
    (5, .r2 3 false, true), (3, .cupSlide 3 false false, false)]

/-- The left side of macro `TurnCup` fits on 1 strand. -/
private theorem macroTurnCup_fits_turns : morseFits 1 macroTurnCup_lhs_turns = true := by
  decide

/-- Macro `TurnCup` as a reachability statement (checked by `decide`). -/
private theorem morseReach_macroTurnCup_turns :
    MorseReach 1 macroTurnCup_lhs_turns macroTurnCup_rhs_turns :=
  ⟨macroTurnCup_moves_turns, by decide⟩

/-- Macro `ToR1`, left side. -/
private def macroToR1_lhs_turns : MorseWord :=
  [(.cup, 1), (.cross false, 2), (.cap, 1), (.cross false, 0), (.cup, 2), (.cup, 2),
    (.cross true, 3), (.cap, 2), (.cross true, 1), (.cross true, 1), (.cap, 0), (.cap, 1)]

/-- Macro `ToR1`, right side. -/
private def macroToR1_rhs_turns : MorseWord :=
  [(.cup, 2), (.cross true, 3), (.cap, 2), (.cup, 1), (.cross false, 2), (.cap, 1),
    (.cross false, 0), (.cup, 2), (.cross true, 1), (.cross true, 1), (.cap, 0), (.cap, 1)]

/-- Macro `ToR1`, the moves (46). -/
private def macroToR1_moves_turns : List MorseMove :=
  [(8, .zig 2 true, true), (9, .capSlide 3 true false, true),
    (8, .exch (.cup, 2) (.cross true, 2), false), (7, .exch (.cap, 2) (.cross true, 4), false),
    (4, .exch (.cup, 2) (.cup, 2), true), (5, .cupSlide 3 true true, false),
    (5, .zig 2 false, false), (4, .exch (.cup, 2) (.cup, 2), true),
    (7, .exch (.cross true, 1) (.cap, 4), true), (6, .exch (.cross true, 1) (.cross true, 3), true),
    (5, .exch (.cross true, 1) (.cup, 4), true), (8, .exch (.cross true, 1) (.cap, 4), true),
    (7, .exch (.cross true, 1) (.cross true, 3), true), (6, .exch (.cross true, 1) (.cup, 4), true),
    (9, .exch (.cap, 0) (.cap, 4), true), (8, .exch (.cap, 0) (.cross true, 3), true),
    (7, .exch (.cap, 0) (.cup, 4), true), (10, .capSlide 1 false true, true),
    (9, .r2 1 true, false), (10, .exch (.cap, 1) (.cap, 3), false),
    (10, .capSlide 2 true true, true), (9, .r2 2 false, false),
    (7, .exch (.cap, 0) (.cup, 4), false), (8, .exch (.cap, 0) (.cross true, 5), false),
    (9, .exch (.cap, 0) (.cap, 4), false), (6, .exch (.cross true, 1) (.cup, 4), false),
    (7, .exch (.cross true, 1) (.cross true, 5), false),
    (8, .exch (.cross true, 1) (.cap, 4), false), (5, .exch (.cross true, 1) (.cup, 4), false),
    (6, .exch (.cross true, 1) (.cross true, 5), false),
    (7, .exch (.cross true, 1) (.cap, 4), false), (4, .exch (.cup, 2) (.cup, 2), false),
    (5, .exch (.cup, 2) (.cross true, 3), false), (6, .exch (.cup, 2) (.cap, 2), false),
    (3, .exch (.cross false, 0) (.cup, 2), false),
    (4, .exch (.cross false, 0) (.cross true, 3), false),
    (5, .exch (.cross false, 0) (.cap, 2), false), (2, .exch (.cap, 1) (.cup, 4), false),
    (3, .exch (.cap, 1) (.cross true, 5), false), (4, .exch (.cap, 1) (.cap, 4), false),
    (1, .exch (.cross false, 2) (.cup, 4), false),
    (2, .exch (.cross false, 2) (.cross true, 5), false),
    (3, .exch (.cross false, 2) (.cap, 4), false), (0, .exch (.cup, 1) (.cup, 2), false),
    (1, .exch (.cup, 1) (.cross true, 3), false), (2, .exch (.cup, 1) (.cap, 2), false)]

/-- The left side of macro `ToR1` fits on 3 strands. -/
private theorem macroToR1_fits_turns : morseFits 3 macroToR1_lhs_turns = true := by
  decide

/-- Macro `ToR1` as a reachability statement (checked by `decide`). -/
private theorem morseReach_macroToR1_turns :
    MorseReach 3 macroToR1_lhs_turns macroToR1_rhs_turns :=
  ⟨macroToR1_moves_turns, by decide⟩

/-- Macro `ToR2`, left side. -/
private def macroToR2_lhs_turns : MorseWord :=
  [(.cap, 3), (.cap, 2), (.cup, 2), (.cross true, 3), (.cap, 2)]

/-- Macro `ToR2`, right side. -/
private def macroToR2_rhs_turns : MorseWord :=
  [(.cup, 6), (.cross true, 7), (.cap, 6), (.cap, 3), (.cap, 2)]

/-- Macro `ToR2`, the moves (6). -/
private def macroToR2_moves_turns : List MorseMove :=
  [(1, .exch (.cap, 2) (.cup, 4), false), (2, .exch (.cap, 2) (.cross true, 5), false),
    (3, .exch (.cap, 2) (.cap, 4), false), (0, .exch (.cap, 3) (.cup, 6), false),
    (1, .exch (.cap, 3) (.cross true, 7), false), (2, .exch (.cap, 3) (.cap, 6), false)]

/-- The left side of macro `ToR2` fits on 7 strands. -/
private theorem macroToR2_fits_turns : morseFits 7 macroToR2_lhs_turns = true := by
  decide

/-- Macro `ToR2` as a reachability statement (checked by `decide`). -/
private theorem morseReach_macroToR2_turns :
    MorseReach 7 macroToR2_lhs_turns macroToR2_rhs_turns :=
  ⟨macroToR2_moves_turns, by decide⟩

set_option linter.unusedVariables false in
/-- Macro `E1` (frame at the prefix `u1 u2 u3 D^(2k+1) n3 n2 (−0)^(4k)`, 3 strands). -/
theorem phaseTwo_E1 (k : ℕ) (hk : 1 ≤ k) : MorseReach 1 (phaseTwoWG k) (phaseTwoE1 k) := by
  set u : MorseWord := phaseTwoEPre (2 * k + 1) ++ [(.cap, 3), (.cap, 2)] ++
    List.replicate (4 * k) (MorseKind.cross false, 0) with hu
  have hout : morseOut 1 u = 3 := by
    rw [hu, morseOut_append, morseOut_append, morseOut_phaseTwoEPre,
      morseOut_replicate]
    rfl
  have h := morseReach_frame_zero 3 1 u [] _ _ morseReach_phaseTwoMacroE1
    phaseTwoMacroE1_fits hout
  have h1 : 2 * (2 * k + 1) = 4 * k + 1 + 1 := by ring
  simp only [hu, phaseTwoWG, phaseTwoE1, phaseTwoEPre, phaseTwoMacroE1_lhs, phaseTwoMacroE1_rhs,
    claspWord, h1, Nat.add_sub_cancel, List.replicate_succ', List.append_assoc, List.cons_append,
    List.nil_append, List.append_nil] at h ⊢
  exact h

set_option linter.unusedVariables false in
/-- The curl `c₂` reaches the return strand above everything (fixed: down the X-cup leg, around
the cup, up its right leg, around the last cap; then down the return strand past the clasp, `c₁`,
the half twists and the caps: exchanges). -/
theorem phaseTwo_E_toR (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1 (phaseTwoE1 k) (phaseTwoER k (2 * k + 1)) := by
  set P : MorseWord := phaseTwoEPre (2 * k + 1) with hP
  set R : MorseWord := List.replicate (2 * (2 * k + 1) - 1) (MorseKind.cross false, 0) with hR
  set c : MorseWord := [(.cup, 2), (.cross true, 3), (.cap, 2)] with hc
  set M : MorseWord := [(.cup, 1), (.cross false, 2), (.cap, 1), (.cross false, 0), (.cup, 2),
    (.cross true, 1), (.cross true, 1), (.cap, 0), (.cap, 1)] with hM
  have hPo : morseOut 1 P = 7 := morseOut_phaseTwoEPre _
  have hNo : morseOut 1 (P ++ [(.cap, 3), (.cap, 2)]) = 3 := by
    rw [morseOut_append, hPo]
    rfl
  have s1 := morseReach_frame_zero 3 1 (P ++ [(.cap, 3), (.cap, 2)] ++ R) [] _ _
    morseReach_macroToR1_turns macroToR1_fits_turns
    (by rw [morseOut_append, hNo, hR, morseOut_replicate])
  have s2 := morseReach_symm (morseReach_comm 1 (P ++ [(.cap, 3), (.cap, 2)]) R c M
    (fun _ hb ↦ ⟨false, by rw [List.eq_of_mem_replicate hb]⟩)
    (fun b hb a ha ↦ by
      rw [List.eq_of_mem_replicate hb]
      simp only [hc, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> simp)
    (by
      rw [hNo, morseFits_append, show morseOut 3 c = 3 from rfl, hR,
        morseFits_replicate _ _ _ _ (by norm_num)]
      rfl))
  have s3 := morseReach_frame_zero 7 1 P (R ++ M) _ _ morseReach_macroToR2_turns
    macroToR2_fits_turns hPo
  have e1 : phaseTwoE1 k = P ++ [(.cap, 3), (.cap, 2)] ++ R ++ macroToR1_lhs_turns ++ [] := by
    simp only [hP, hR, phaseTwoE1, macroToR1_lhs_turns, List.append_assoc, List.cons_append,
      List.nil_append, List.append_nil]
  have e2 : P ++ [(.cap, 3), (.cap, 2)] ++ R ++ macroToR1_rhs_turns ++ [] =
      P ++ [(.cap, 3), (.cap, 2)] ++ R ++ c ++ M := by
    simp only [hc, hM, macroToR1_rhs_turns, List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil]
  have e3 : P ++ [(.cap, 3), (.cap, 2)] ++ c ++ R ++ M = P ++ macroToR2_lhs_turns ++ (R ++ M) := by
    simp only [hc, macroToR2_lhs_turns, List.append_assoc, List.cons_append, List.nil_append]
  have e4 : P ++ macroToR2_rhs_turns ++ (R ++ M) = phaseTwoER k (2 * k + 1) := by
    simp only [hP, hR, hM, phaseTwoER, phaseTwoETail, macroToR2_rhs_turns, claspWord,
      Nat.sub_self, phaseTwoBlk, List.replicate_zero, List.flatten_nil, List.append_assoc,
      List.cons_append, List.nil_append, List.append_nil]
  rw [e1, ← e4]
  rw [e2] at s1
  rw [e3] at s2
  exact morseReach_trans s1 (morseReach_trans s2 s3)

set_option linter.unusedVariables false in
/-- Around the first cup onto the input band (fixed). -/
theorem phaseTwo_E_turnBottom (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1 (phaseTwoER k 0) (phaseTwoEP k 0 true) := by
  have h := morseReach_frame_zero 1 1 [] (phaseTwoBlk phaseTwoD (2 * k + 1) ++
    phaseTwoETail k) _ _ morseReach_macroTurnBottom_turns macroTurnBottom_fits_turns rfl
  simp only [phaseTwoER, phaseTwoEP, phaseTwoEPre, phaseTwoECurl, macroTurnBottom_lhs_turns,
    macroTurnBottom_rhs_turns, Nat.sub_zero, Nat.zero_mod, decide_true, beq_self_eq_true,
    phaseTwoBlk, List.replicate_zero, List.flatten_nil, List.cons_append, List.nil_append,
    List.append_nil] at h ⊢
  exact h

set_option linter.unusedVariables false in
/-- Around the closing cap onto the closing arc (fixed). -/
theorem phaseTwo_E_turnCap (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1 (phaseTwoEP k (2 * k + 1) true) (phaseTwoEA k (2 * k + 1)) := by
  have hodd : ¬((2 * k + 1) % 2 = 0) := by omega
  have h := morseReach_frame_zero 7 1 (phaseTwoEPre (2 * k + 1))
    (List.replicate (2 * (2 * k + 1) - 1) (MorseKind.cross false, 0) ++
      [(.cup, 1), (.cross false, 2), (.cap, 1), (.cross false, 0)] ++ claspWord ++ [(.cap, 1)])
    _ _ morseReach_macroTurnCap_turns macroTurnCap_fits_turns (morseOut_phaseTwoEPre _)
  simp only [phaseTwoEP, phaseTwoEA, phaseTwoETail, phaseTwoECurl, hodd, decide_false,
    macroTurnCap_lhs_turns, macroTurnCap_rhs_turns, Nat.sub_self, phaseTwoBlk,
    List.replicate_zero, List.flatten_nil, List.append_assoc, List.cons_append, List.nil_append,
    List.append_nil] at h ⊢
  simpa using h

set_option linter.unusedVariables false in
/-- Around the closing cup onto pass 2 (fixed). -/
theorem phaseTwo_E_turnCup (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1 (phaseTwoEA k 0) (phaseTwoEP k 0 false) := by
  have h := morseReach_frame_zero 1 1 [] (phaseTwoBlk phaseTwoD (2 * k + 1) ++
    phaseTwoETail k) _ _ morseReach_macroTurnCup_turns macroTurnCup_fits_turns rfl
  simp only [phaseTwoEA, phaseTwoEP, phaseTwoEPre, phaseTwoECurl, macroTurnCup_lhs_turns,
    macroTurnCup_rhs_turns, Nat.sub_zero, Nat.zero_mod, decide_true, phaseTwoBlk,
    List.replicate_zero, List.flatten_nil, List.append_assoc, List.cons_append, List.nil_append,
    List.append_nil] at h ⊢
  simpa using h

end AJConjecture
