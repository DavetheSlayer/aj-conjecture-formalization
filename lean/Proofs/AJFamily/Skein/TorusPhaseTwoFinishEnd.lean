import Mathlib
import AJFamily.Skein.TorusPhaseTwoGadget
import AJFamily.Skein.TorusPhaseTwoPass
import AJFamily.Skein.MorseFrame
import AJFamily.Skein.MorsePhaseTools
import AJFamily.Skein.TorusPhaseTwoFinishWords

/-!
# Stage E: the end

`phaseTwo_E_end`: the travelling curl passes the closing caps and the `4k + 1` negative half twists
(by induction, with small fixed macros checked by `decide`), goes up through the hook and around the
cap of the Y end, and cancels the curl `c₁` (one `kink`).
-/

namespace AJConjecture

/-- Shifting by zero strands does nothing. -/
private theorem morseShiftWord_zero_end (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- The frame lemma without shift: a move list on `n` strands applies after a prefix with `n`
strands at its top. -/
theorem morseReach_frame_zero (n n₀ : ℕ) (u v w w' : MorseWord)
    (h : MorseReach n w w') (hfit : morseFits n w = true) (hu : morseOut n₀ u = n) :
    MorseReach n₀ (u ++ w ++ v) (u ++ w' ++ v) := by
  have h' := morseReach_frame n n₀ 0 0 u v w w' h hfit (by rw [hu]; ring)
  rwa [morseShiftWord_zero_end, morseShiftWord_zero_end] at h'

/-- Blocks of doubled crossings do not change the number of strands. -/
private theorem morseOut_phaseTwoBlk_end (n m : ℕ) :
    morseOut n (phaseTwoBlk phaseTwoD m) = n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show phaseTwoBlk phaseTwoD (m + 1) = phaseTwoD ++ phaseTwoBlk phaseTwoD m by
      simp [phaseTwoBlk, List.replicate_succ], morseOut_append, morseOut_phaseTwoD, ih]

/-- The prefix `u1 u2 u3 · D^m` has seven strands at its top. -/
theorem morseOut_phaseTwoEPre (m : ℕ) : morseOut 1 (phaseTwoEPre m) = 7 := by
  rw [phaseTwoEPre, morseOut_append, morseOut_phaseTwoBlk_end]
  rfl

/-- Macro `PastCaps`, left side. -/
private def macroPastCaps_lhs_end : MorseWord :=
  [(.cup, 2), (.cross true, 1), (.cap, 2), (.cap, 3), (.cap, 2)]

/-- Macro `PastCaps`, right side. -/
private def macroPastCaps_rhs_end : MorseWord :=
  [(.cap, 3), (.cap, 2), (.cup, 2), (.cross true, 1), (.cap, 2)]

/-- Macro `PastCaps`, the moves (6). -/
private def macroPastCaps_moves_end : List MorseMove :=
  [(2, .exch (.cap, 2) (.cap, 5), false), (1, .exch (.cross true, 1) (.cap, 5), false),
    (0, .exch (.cup, 2) (.cap, 3), false), (3, .exch (.cap, 2) (.cap, 4), false),
    (2, .exch (.cross true, 1) (.cap, 4), false), (1, .exch (.cup, 2) (.cap, 2), false)]

/-- The left side of macro `PastCaps` fits on 7 strands. -/
private theorem macroPastCaps_fits_end : morseFits 7 macroPastCaps_lhs_end = true := by
  decide

/-- Macro `PastCaps` as a reachability statement (checked by `decide`). -/
private theorem morseReach_macroPastCaps_end :
    MorseReach 7 macroPastCaps_lhs_end macroPastCaps_rhs_end :=
  ⟨macroPastCaps_moves_end, by decide⟩

/-- Macro `PastPair`, left side. -/
private def macroPastPair_lhs_end : MorseWord :=
  [(.cup, 2), (.cross true, 1), (.cap, 2), (.cross false, 0), (.cross false, 0)]

/-- Macro `PastPair`, right side. -/
private def macroPastPair_rhs_end : MorseWord :=
  [(.cross false, 0), (.cross false, 0), (.cup, 2), (.cross true, 1), (.cap, 2)]

/-- Macro `PastPair`, the moves (20). -/
private def macroPastPair_moves_end : List MorseMove :=
  [(0, .cupSlide 1 false false, true), (2, .r2 1 false, false),
    (2, .exch (.cross false, 0) (.cap, 2), true),
    (1, .exch (.cross false, 0) (.cross false, 2), true), (3, .capSlide 1 false true, true),
    (2, .r3 1 false, true), (0, .cupSlide 0 false true, false),
    (0, .exch (.cup, 0) (.cross false, 0), false), (3, .r2 0 false, true),
    (1, .cupSlide 0 false false, false), (1, .cupSlide 0 false false, true),
    (3, .r2 0 false, false), (3, .capSlide 1 false false, true), (2, .r3 1 false, false),
    (1, .exch (.cup, 0) (.cross false, 0), false), (5, .exch (.cross false, 0) (.cap, 2), true),
    (4, .exch (.cross false, 0) (.cross false, 2), true), (2, .cupSlide 0 false false, false),
    (4, .r2 1 false, true), (2, .cupSlide 1 false false, false)]

/-- The left side of macro `PastPair` fits on 3 strands. -/
private theorem macroPastPair_fits_end : morseFits 3 macroPastPair_lhs_end = true := by
  decide

/-- Macro `PastPair` as a reachability statement (checked by `decide`). -/
private theorem morseReach_macroPastPair_end :
    MorseReach 3 macroPastPair_lhs_end macroPastPair_rhs_end :=
  ⟨macroPastPair_moves_end, by decide⟩

/-- Macro `PastOdd`, left side. -/
private def macroPastOdd_lhs_end : MorseWord :=
  [(.cup, 2), (.cross true, 1), (.cap, 2), (.cross false, 0)]

/-- Macro `PastOdd`, right side. -/
private def macroPastOdd_rhs_end : MorseWord :=
  [(.cross false, 0), (.cup, 1), (.cross true, 0), (.cap, 1)]

/-- Macro `PastOdd`, the moves (10). -/
private def macroPastOdd_moves_end : List MorseMove :=
  [(0, .cupSlide 1 false false, true), (2, .r2 1 false, false),
    (2, .exch (.cross false, 0) (.cap, 2), true),
    (1, .exch (.cross false, 0) (.cross false, 2), true), (3, .capSlide 1 false true, true),
    (2, .r3 1 false, true), (0, .cupSlide 0 false true, false),
    (0, .exch (.cup, 0) (.cross false, 0), false), (3, .r2 0 false, true),
    (1, .cupSlide 0 false false, false)]

/-- The left side of macro `PastOdd` fits on 3 strands. -/
private theorem macroPastOdd_fits_end : morseFits 3 macroPastOdd_lhs_end = true := by
  decide

/-- Macro `PastOdd` as a reachability statement (checked by `decide`). -/
private theorem morseReach_macroPastOdd_end :
    MorseReach 3 macroPastOdd_lhs_end macroPastOdd_rhs_end :=
  ⟨macroPastOdd_moves_end, by decide⟩

/-- Macro `Cancel`, left side. -/
private def macroCancel_lhs_end : MorseWord :=
  [(.cup, 1), (.cross true, 0), (.cap, 1), (.cup, 1), (.cross false, 2), (.cap, 1),
    (.cross false, 0), (.cup, 2), (.cross true, 1), (.cross true, 1), (.cap, 0)]

/-- Macro `Cancel`, right side. -/
private def macroCancel_rhs_end : MorseWord :=
  [(.cross false, 0), (.cup, 2), (.cross true, 1), (.cross true, 1), (.cap, 0)]

/-- Macro `Cancel`, the moves (90). -/
private def macroCancel_moves_end : List MorseMove :=
  [(2, .exch (.cap, 1) (.cup, 3), false), (1, .exch (.cross true, 0) (.cup, 3), false),
    (0, .exch (.cup, 1) (.cup, 1), false), (3, .exch (.cap, 1) (.cross false, 4), false),
    (2, .exch (.cross true, 0) (.cross false, 4), false),
    (1, .exch (.cup, 1) (.cross false, 2), false), (4, .exch (.cap, 1) (.cap, 3), false),
    (3, .exch (.cross true, 0) (.cap, 3), false), (2, .exch (.cup, 1) (.cap, 1), false),
    (3, .cupSlide 0 false false, true), (5, .r2 0 false, false), (5, .capSlide 1 false false, true),
    (4, .r3 1 false, false), (3, .exch (.cup, 0) (.cross false, 0), false),
    (7, .exch (.cross false, 0) (.cap, 2), true),
    (6, .exch (.cross false, 0) (.cross false, 2), true), (4, .cupSlide 0 false false, false),
    (6, .r2 1 false, true), (4, .cupSlide 1 false false, false),
    (6, .exch (.cap, 2) (.cup, 4), false), (5, .exch (.cross true, 1) (.cup, 4), false),
    (4, .exch (.cup, 2) (.cup, 2), false), (7, .capSlide 2 true false, true),
    (6, .exch (.cross true, 1) (.cross true, 3), false),
    (9, .exch (.cross true, 1) (.cap, 3), true), (7, .r3 1 true, false),
    (5, .cupSlide 2 true false, false), (5, .exch (.cross true, 1) (.cup, 3), true),
    (8, .exch (.cross true, 1) (.cap, 3), true), (9, .capSlide 2 true true, true),
    (7, .r3 1 true, true), (9, .exch (.cross true, 1) (.cross true, 3), false),
    (6, .exch (.cross true, 1) (.cup, 3), true), (7, .cupSlide 2 true true, false),
    (7, .zig 1 true, true), (7, .cupSlide 0 true false, true),
    (9, .exch (.cross true, 0) (.cap, 2), false), (10, .exch (.cross true, 0) (.cup, 2), false),
    (13, .exch (.cap, 0) (.cap, 2), true), (11, .capSlide 0 true true, false),
    (10, .zig 1 false, false), (9, .exch (.cap, 0) (.cap, 2), true),
    (6, .exch (.cup, 0) (.cross true, 1), true), (7, .exch (.cross true, 1) (.cross true, 3), true),
    (8, .exch (.cap, 0) (.cross true, 3), true), (5, .exch (.cup, 0) (.cross true, 1), true),
    (6, .exch (.cross true, 1) (.cross true, 3), true), (7, .exch (.cap, 0) (.cross true, 3), true),
    (4, .exch (.cup, 0) (.cup, 2), true), (5, .exch (.cross true, 1) (.cup, 4), true),
    (6, .exch (.cap, 0) (.cup, 4), true), (6, .r2 0 true, true), (4, .cupSlide 0 true false, false),
    (4, .cupSlide 1 false true, true), (6, .exch (.cross false, 0) (.cross false, 2), true),
    (7, .exch (.cap, 0) (.cross false, 2), true), (3, .exch (.cross false, 0) (.cup, 2), false),
    (4, .r3 0 false, false), (5, .capSlide 0 false true, false), (3, .cupSlide 1 true false, true),
    (5, .r2 1 true, false), (3, .kink 1 true, true), (1, .r2 1 true, true),
    (2, .capSlide 1 false true, false), (2, .exch (.cup, 2) (.cap, 2), true),
    (2, .cupSlide 2 true true, true), (1, .exch (.cross true, 1) (.cup, 3), false),
    (0, .exch (.cup, 1) (.cup, 1), false), (5, .exch (.cross true, 1) (.cap, 4), true),
    (4, .exch (.cross true, 1) (.cross true, 3), true), (2, .r3 1 true, false),
    (6, .exch (.cap, 2) (.cap, 4), true), (4, .capSlide 2 true true, false),
    (1, .cupSlide 1 true false, false), (1, .zig 2 true, false), (0, .zig 1 true, false),
    (2, .capSlide 1 true true, true), (1, .r2 1 false, false),
    (2, .exch (.cap, 1) (.cup, 3), false), (2, .cupSlide 2 true false, true),
    (1, .exch (.cup, 2) (.cross true, 2), true), (0, .exch (.cup, 2) (.cup, 2), true),
    (5, .exch (.cap, 1) (.cross true, 4), false),
    (4, .exch (.cross true, 2) (.cross true, 4), false), (2, .r3 3 true, true),
    (6, .exch (.cap, 1) (.cap, 3), false), (4, .capSlide 2 true false, false),
    (1, .cupSlide 3 true true, false), (1, .zig 2 false, false), (0, .zig 1 false, false)]

/-- The left side of macro `Cancel` fits on 3 strands. -/
private theorem macroCancel_fits_end : morseFits 3 macroCancel_lhs_end = true := by
  decide

/-- Macro `Cancel` as a reachability statement (checked by `decide`). -/
private theorem morseReach_macroCancel_end :
    MorseReach 3 macroCancel_lhs_end macroCancel_rhs_end :=
  ⟨macroCancel_moves_end, by decide⟩

/-- The curl on the strand `1` of three strands passes `2j` negative half twists `−0`. -/
private theorem morseReach_curl_past_twists_end (j : ℕ) :
    ∀ (Q V : MorseWord), morseOut 1 Q = 3 →
      MorseReach 1 (Q ++ phaseTwoECurl true ++
          (List.replicate (2 * j) (MorseKind.cross false, 0) ++ V))
        (Q ++ List.replicate (2 * j) (MorseKind.cross false, 0) ++
          (phaseTwoECurl true ++ V)) := by
  induction j with
  | zero => intro Q V _; simpa using morseReach_refl 1 _
  | succ j ih =>
    intro Q V hQ
    have h1 := morseReach_frame_zero 3 1 Q
      (List.replicate (2 * j) (MorseKind.cross false, 0) ++ V) _ _ morseReach_macroPastPair_end
      macroPastPair_fits_end hQ
    have h2 := ih (Q ++ [(.cross false, 0), (.cross false, 0)]) V
      (by rw [morseOut_append, hQ]; rfl)
    have e : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    simp only [phaseTwoECurl, ite_true, macroPastPair_lhs_end, macroPastPair_rhs_end, e,
      List.replicate_succ, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

set_option linter.unusedVariables false in
/-- The end: past the caps, the `4k + 1` half twists (one curl slide each, induction), up through
the hook, around the cap of the Y end; `c₁` and `c₂` cancel (one `kink`). -/
theorem phaseTwo_E_end (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1 (phaseTwoEP k (2 * k + 1) false) (torusTargetWord k) := by
  set P : MorseWord := phaseTwoEPre (2 * k + 1) with hP
  set R : MorseWord := List.replicate (2 * (2 * k)) (MorseKind.cross false, 0) with hR
  have hPo : morseOut 1 P = 7 := morseOut_phaseTwoEPre _
  have hNo : morseOut 1 (P ++ [(.cap, 3), (.cap, 2)]) = 3 := by
    rw [morseOut_append, hPo]
    rfl
  have hRo : morseOut 1 (P ++ [(.cap, 3), (.cap, 2)] ++ R) = 3 := by
    rw [morseOut_append, hNo, hR, morseOut_replicate]
  have s1 := morseReach_frame_zero 7 1 P
    (R ++ (MorseKind.cross false, 0) :: [(.cup, 1), (.cross false, 2), (.cap, 1),
      (.cross false, 0)] ++ claspWord ++ [(.cap, 1)]) _ _
    morseReach_macroPastCaps_end macroPastCaps_fits_end hPo
  have s2 := morseReach_curl_past_twists_end (2 * k) (P ++ [(.cap, 3), (.cap, 2)])
    ((MorseKind.cross false, 0) :: [(.cup, 1), (.cross false, 2), (.cap, 1),
      (.cross false, 0)] ++ claspWord ++ [(.cap, 1)]) hNo
  have s3 := morseReach_frame_zero 3 1 (P ++ [(.cap, 3), (.cap, 2)] ++ R)
    ([(.cup, 1), (.cross false, 2), (.cap, 1), (.cross false, 0)] ++ claspWord ++ [(.cap, 1)])
    _ _ morseReach_macroPastOdd_end macroPastOdd_fits_end hRo
  have s4 := morseReach_frame_zero 3 1
    (P ++ [(.cap, 3), (.cap, 2)] ++ R ++ [(.cross false, 0)]) [(.cap, 1)] _ _
    morseReach_macroCancel_end macroCancel_fits_end
    (by rw [morseOut_append, hRo]; rfl)
  have e1 : 2 * (2 * k + 1) - 1 = 2 * (2 * k) + 1 := by omega
  have e2 : 2 * (2 * k + 1) = 2 * (2 * k) + 1 + 1 := by ring
  have hodd : ¬((2 * k + 1) % 2 = 0) := by omega
  have eP : [(MorseKind.cup, 1), (.cup, 2), (.cup, 3)] ++ phaseTwoBlk phaseTwoD (2 * k + 1) = P :=
    rfl
  rw [torusTargetWord_eq_blocks, eP, phaseTwoEP, phaseTwoETail, e1, e2]
  simp only [phaseTwoECurl, hodd, decide_false, Bool.false_beq, Bool.not_false, ite_true,
    Nat.sub_self, phaseTwoBlk, List.replicate_zero, List.flatten_nil, List.replicate_succ', ← hP,
    ← hR, claspWord, macroPastCaps_lhs_end, macroPastCaps_rhs_end, macroPastOdd_lhs_end,
    macroPastOdd_rhs_end, macroCancel_lhs_end, macroCancel_rhs_end, List.append_assoc,
    List.cons_append, List.nil_append, List.append_nil] at s1 s2 s3 s4 ⊢
  exact morseReach_trans s1 (morseReach_trans s2 (morseReach_trans s3 s4))

end AJConjecture
