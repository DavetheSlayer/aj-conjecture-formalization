import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkWords
import AJHandoff.TorusKnot.PairKIsoParkComm
import AJHandoff.TorusKnot.PairKIsoParkMacros
import AJHandoff.TorusKnot.PairKIsoParkWrapMacros
import AJHandoff.TorusKnot.PairKIsoBeadStep
import AJHandoff.TorusKnot.PairKIsoParkProc
import AJHandoff.TorusKnot.PairKIsoParkPorts
import AJHandoff.TorusKnot.PairKIsoParkGadget

/-!
# Stage C by ports: the return strand, the last cancellations, the clasp back in place

* `morseReach_park_wrap`: right-edge curls at the top end travel to the bottom end through the
  return strand: the curl next to the last cap turns onto the return strand
  (`morseReach_isoPark_capP`/`capN`), passes the whole middle of the word, which lies on its left
  (`morseReach_isoBead_commL` with `b = 1`, the strand count left of it is the same at both
  ends), and turns onto the right edge at the first cup (`cupP`/`cupN`). Induction on the stack.
* `morseReach_isoPark_cancelBottom`: on two strands, `cS(w) · T^C · cS(-w) ~ T^C` (the curls pass
  the twists, `TP`, `NT`, and cancel, `PN`, `NP`).
* `morseReach_pairParkW8_WC`: the clasp at the port `r - 1` (band `2q + 1`, band frame) turns
  around the doubled cup `u_{2q+1}` onto the right strand (`morseReach_isoBead_cup`, read as
  `isoClaspS` there, `isoRot_isoClaspS`) and passes the doubled first crossing of round `0`
  (exchange): this is `pairWC` (`pairCore_eq_head_tail`).
-/

namespace AJConjecture

/-- The doubled caps fit on the strands of the port level and close all but two of them. -/
private theorem morseDouble_pairCaps_fits_wrap (r n : ℕ) (hr : 3 ≤ r) (hn : 4 * r - 2 ≤ n) :
    morseFits n (morseDouble (pairCaps r)) = true ∧
      morseOut n (morseDouble (pairCaps r)) = n - (4 * r - 4) := by
  have e : morseDouble (pairCaps r) =
      [(MorseKind.cap, 2 * (r - 3) + 1), (MorseKind.cap, 2 * (r - 3)),
        (MorseKind.cap, 2 * (2 * r - 5) + 1), (MorseKind.cap, 2 * (2 * r - 5))] ++
      morseDouble ((List.range (r - 3)).reverse.map fun i ↦ isoN (0 + i)) := by
    simp only [pairCaps, morseDouble, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Nat.zero_add]
    rfl
  have hK := morseDouble_caps_fits_park 0 (r - 3) (n - 8) (by omega)
  rw [e, morseFits_append, morseOut_append]
  have h4 : morseFits n [(MorseKind.cap, 2 * (r - 3) + 1), (MorseKind.cap, 2 * (r - 3)),
        (MorseKind.cap, 2 * (2 * r - 5) + 1), (MorseKind.cap, 2 * (2 * r - 5))] = true ∧
      morseOut n [(MorseKind.cap, 2 * (r - 3) + 1), (MorseKind.cap, 2 * (r - 3)),
        (MorseKind.cap, 2 * (2 * r - 5) + 1), (MorseKind.cap, 2 * (2 * r - 5))] = n - 8 := by
    simp only [morseFits_cons, morseFits_nil, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, and_true]
    omega
  rw [h4.1, h4.2, hK.1, hK.2]
  exact ⟨rfl, by omega⟩

/-- The middle of a port word (between the bottom and the top stack) fits on two strands. -/
private theorem morseFits_parkMid_wrap (r s : ℕ) (S : ℕ → List IsoBead) (hr : 3 ≤ r) :
    morseFits 2 (morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble (pairCaps r)) = true ∧
    morseOut 2 (morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble (pairCaps r)) = 2 := by
  have h1 := morseDouble_pairCups_fits_park r 2 hr le_rfl
  have h2 := morseFits_portW_park r S (List.range r) (2 + 4 * r - 4)
    (fun c hc ↦ by have := List.mem_range.1 hc; omega)
  have h3 := morseDouble_pairConv_fits_park r s (2 + 4 * r - 4) hr (by omega)
  have h4 := morseDouble_pairCaps_fits_wrap r (2 + 4 * r - 4) hr (by omega)
  simp only [morseFits_append, morseOut_append, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2.1, h4.1, h4.2,
    Bool.and_true]
  exact ⟨trivial, by omega⟩

/-- One curl next to the last cap moves to the first cup through the return strand. -/
private theorem morseReach_wrapOne_gen (M : MorseWord) (hM : morseFits 2 M = true ∧ morseOut 2 M = 2)
    (B T : List IsoBead) (x : IsoBead) (hx : x = .p ∨ x = .n) :
    MorseReach 1 ([isoU 1] ++ isoBeadsWord B ++ M ++ isoBeadsWord T ++ isoBeadsWord [x] ++ [isoN 1])
      ([isoU 1] ++ isoBeadsWord [x] ++ isoBeadsWord B ++ M ++ isoBeadsWord T ++ [isoN 1]) := by
  have hB := morseFits_isoBeadsWord B 0
  have hT := morseFits_isoBeadsWord T 0
  have hwf : morseFits 2 (isoBeadsWord B ++ M ++ isoBeadsWord T) = true ∧
      morseOut 2 (isoBeadsWord B ++ M ++ isoBeadsWord T) = 2 := by
    simp only [morseFits_append, morseOut_append, hB.1, hB.2, hM.1, hM.2, hT.1, hT.2]
    exact ⟨rfl, trivial⟩
  have hw3 : morseOut 3 (isoBeadsWord B ++ M ++ isoBeadsWord T) = 3 := by
    have := morseOut_add_right 2 1 _ hwf.1
    rw [hwf.2] at this
    exact this
  have hcap : MorseReach 3 (isoBeadsWord [x] ++ [isoN 1])
      (morseShiftWord 2 [isoU 1, isoX (x == .p) 0, isoN 1] ++ [isoN 1]) := by
    rcases hx with rfl | rfl
    · exact morseReach_isoPark_capP
    · exact morseReach_isoPark_capN
  have h1 := morseReach_frame 3 1 0 0 ([isoU 1] ++ (isoBeadsWord B ++ M ++ isoBeadsWord T)) [] _ _
    hcap (by rcases hx with rfl | rfl <;> decide)
    (by rw [morseOut_append, show morseOut 1 [isoU 1] = 3 from rfl, hw3])
  have h2 := morseReach_isoBead_commL 1 2 1 0 [isoU 1, isoX (x == .p) 0, isoN 1] [isoU 1]
    (isoBeadsWord B ++ M ++ isoBeadsWord T) [isoN 1] (by rcases hx with rfl | rfl <;> decide)
    (by rcases hx with rfl | rfl <;> decide) hwf.1 rfl
  rw [hwf.2] at h2
  have hcup : MorseReach 1 ([isoU 1] ++ morseShiftWord 2 [isoU 1, isoX (x == .p) 0, isoN 1])
      ([isoU 1] ++ isoBeadsWord [x]) := by
    rcases hx with rfl | rfl
    · exact morseReach_isoPark_cupP
    · exact morseReach_isoPark_cupN
  have h3 := morseReach_frame 1 1 0 0 [] (isoBeadsWord B ++ M ++ isoBeadsWord T ++ [isoN 1]) _ _
    hcup (by rcases hx with rfl | rfl <;> decide) rfl
  simp only [morseShiftWord_zero_iso, List.nil_append, List.append_nil, List.append_assoc]
    at h1 h2 h3 ⊢
  exact morseReach_trans h1 (morseReach_trans (morseReach_symm h2) h3)

/-- One curl of the top stack moves to the bottom stack through the return strand. -/
private theorem morseReach_park_wrapOne (r s : ℕ) (S : ℕ → List IsoBead) (B T : List IsoBead)
    (x : IsoBead) (hr : 3 ≤ r) (hx : x = .p ∨ x = .n) :
    MorseReach 1 (pairParkW r s B S (T ++ [x])) (pairParkW r s (x :: B) S T) := by
  have h := morseReach_wrapOne_gen _ (morseFits_parkMid_wrap r s S hr) B T x hx
  rw [pairParkW, pairParkW, isoBeadsWord_append_park,
    show isoBeadsWord (x :: B) = isoBeadsWord [x] ++ isoBeadsWord B by simp [isoBeadsWord]]
  simpa only [List.append_assoc] using h

/-- A doubled positive crossing is a shifted `phaseTwoD`. -/
private theorem morseDouble_cross_wrap (j : ℕ) :
    morseDouble [isoX true j] = morseShiftWord (2 * j) phaseTwoD := by
  simp [morseDouble, isoX, morseDoubleLetter, morseOfBraid, cable, cableGen, phaseTwoD,
    morseShiftWord, shiftLetter, List.range_succ]
  omega

/-- The port stacks with only the clasp at the port `r - 1`. -/
private theorem portW_clasp_wrap (r : ℕ) (hr : 3 ≤ r) :
    (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c))
      (isoBeadsWord (pairParkAt r [.cs] c))) = morseShiftWord (2 * (2 * r - 3)) isoClaspU := by
  rw [portW_split_park r (r - 1) _ (by omega)]
  have hA : (List.range (r - 1)).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c))
      (isoBeadsWord (pairParkAt r [.cs] c))) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro c hc
    have : c ≠ r - 1 := by have := List.mem_range.1 hc; omega
    simp [pairParkAt, this, isoBeadsWord, morseShiftWord]
  rw [hA, show r - 1 - (r - 1) = 0 by omega]
  simp [pairParkAt, isoBeadsWord, isoBeadWord, show r - 2 + (r - 1) = 2 * r - 3 by omega]

/-- The conveyor and the caps are the first crossing and the tail of the core. -/
private theorem pairConv_caps_wrap (r s : ℕ) (hr : 3 ≤ r) (hs : 1 ≤ s) :
    pairConv r s ++ pairCaps r = [isoX true (2 * r - 4)] ++ pairCoreTail r s := by
  have h := (pairCore_eq_parts r s).symm.trans (pairCore_eq_head_tail hr hs)
  simp only [pairCups, pairCoreHead, List.append_assoc] at h
  have h' := List.append_cancel_left h
  simp only [List.cons_append, List.nil_append] at h'
  have h'' := List.cons.inj h'
  simpa using h''.2

/-- Right-edge curls at the top end move to the bottom end through the return strand. -/
theorem morseReach_park_wrap (r s : ℕ) (S : ℕ → List IsoBead) (L : List IsoBead) (hr : 3 ≤ r)
    (hL : ∀ x ∈ L, x = .p ∨ x = .n) :
    MorseReach 1 (pairParkW r s [] S L) (pairParkW r s L S []) := by
  have key : ∀ (L B : List IsoBead), (∀ x ∈ L, x = .p ∨ x = .n) →
      MorseReach 1 (pairParkW r s B S L) (pairParkW r s (L ++ B) S []) := by
    intro L
    induction L using List.reverseRecOn with
    | nil => intro B _; exact morseReach_refl 1 _
    | append_singleton L x ih =>
      intro B hL
      have h1 := morseReach_park_wrapOne r s S B L x hr (hL x (List.mem_append_right _
        (List.mem_singleton_self x)))
      have h2 := ih (x :: B) (fun y hy ↦ hL y (List.mem_append_left _ hy))
      rw [List.append_assoc, List.singleton_append]
      exact morseReach_trans h1 h2
  simpa using key L [] hL


set_option linter.unusedVariables false in
/-- `pairParkW5 → pairParkW6`. -/
theorem morseReach_pairParkW5_W6 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairParkW5 r s) (pairParkW6 r s) := by
  exact morseReach_park_wrap r s _ _ hr (isoCurlStack_mem _)

/-- The curl stacks at the bottom end cancel across the twists. -/
theorem morseReach_isoPark_cancelBottom (w : ℤ) (c : ℕ) :
    MorseReach 2 (isoBeadsWord (isoCurlStack w ++ List.replicate c .t ++ isoCurlStack (-w)))
      (isoBeadsWord (List.replicate c .t)) := by
  have h1 := morseReach_isoBeads_frame [] (isoCurlStack (-w)) _ _ (morseReach_isoCurlStack_twists w c)
  have h2 := morseReach_isoBeads_frame (List.replicate c .t) [] _ _ (morseReach_isoCurlStack_cancel w)
  simp only [List.nil_append, List.append_nil, List.append_assoc] at h1 h2 ⊢
  exact morseReach_trans h1 h2

set_option linter.unusedVariables false in
/-- `pairParkW7 → pairParkW8`. -/
theorem morseReach_pairParkW7_W8 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairParkW7 r s) (pairParkW8 r s) := by
  have hc := morseReach_isoPark_cancelBottom (pairParkWa r s) (pairC r s)
  have hf := morseReach_frame 2 1 0 1 [isoU 1] (morseDouble (pairCups r) ++
    (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c))
      (isoBeadsWord (pairParkAt r [.cs] c))) ++
    morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++ isoBeadsWord [] ++ [isoN 1]) _ _ hc
    (morseFits_isoBeadsWord _ 0).1 rfl
  simp only [morseShiftWord_zero_iso] at hf
  simpa only [pairParkW7, pairParkW8, pairParkW, List.append_assoc] using hf


/-- The clasp goes back to its place: `pairParkW8 → pairWC`. -/
theorem morseReach_pairParkW8_WC {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairParkW8 r s) (pairWC r s) := by
  have hs : 1 ≤ s := by have := h.2.1; omega
  have hL := morseDouble_cups_fits_park 0 (r - 2) 3 (by omega)
  rw [← cups_zero_park] at hL
  have hX : morseOut 3 (List.replicate (2 * ((r - 1) * s)) (isoX false 0)) = 3 :=
    morseOut_of_cross _ _ (fun b hb ↦ ⟨false, by rw [List.eq_of_mem_replicate hb]; rfl⟩)
  set u := [isoU 1] ++ List.replicate (2 * ((r - 1) * s)) (isoX false 0) ++
    morseDouble ((List.range (r - 2)).map isoU) with hu
  have hou : morseOut 1 u = 4 * r - 5 := by
    rw [hu, morseOut_append, morseOut_append, show morseOut 1 [isoU 1] = 3 from rfl, hX, hL.2]
    omega
  -- the clasp turns around the doubled cup of the right arc
  have h1 := morseReach_isoBead_cup 1 (2 * r - 3) isoClaspU u
    (morseDouble (pairConv r s ++ pairCaps r) ++ [isoN 1]) (by decide) (by decide)
    (by rw [hou]; omega)
  rw [show isoRot 2 isoClaspU = isoClaspS by decide,
    show 2 * (2 * r - 3) + 2 = 2 * (2 * r - 2) by omega] at h1
  -- and passes the doubled first crossing of the conveyor
  have hD := morseOut_shift_iso (2 * (2 * r - 4)) 4 0 phaseTwoD (by decide)
  rw [show morseOut 4 phaseTwoD = 4 by decide,
    show 2 * (2 * r - 4) + 4 + 0 = 2 * (2 * r - 2) by omega] at hD
  have hou2 : morseOut 1 (u ++ morseDouble [isoU (2 * r - 3)]) = 2 * (2 * r - 2) + 2 + 1 := by
    rw [morseOut_append, hou]
    simp only [morseDouble, isoU, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      morseDoubleLetter, morseOut, morseLetterOut, morseKindOut, morseKindIn]
    omega
  have h2 := morseReach_isoBead_commL 1 (2 * (2 * r - 2)) 2 1 isoClaspS
    (u ++ morseDouble [isoU (2 * r - 3)]) (morseDouble [isoX true (2 * r - 4)])
    (morseDouble (pairCoreTail r s) ++ [isoN 1]) (by decide) (by decide)
    (by rw [morseDouble_cross_wrap]; exact hD.2) hou2
  rw [morseDouble_cross_wrap, hD.1, ← morseDouble_cross_wrap] at h2
  have e8 : pairParkW8 r s = u ++ morseDouble [isoU (2 * r - 3)] ++
      morseShiftWord (2 * (2 * r - 3)) isoClaspU ++
      morseDouble (pairConv r s ++ pairCaps r) ++ [isoN 1] := by
    rw [pairParkW8, pairParkW, portW_clasp_wrap r hr, isoBeadsWord_replicate_t, hu]
    simp [pairCups, morseDouble, List.flatMap_append, List.append_assoc, isoBeadsWord, pairC]
  have eC : pairWC r s = u ++ morseDouble [isoU (2 * r - 3)] ++
      morseDouble [isoX true (2 * r - 4)] ++ morseShiftWord (2 * (2 * r - 2)) isoClaspS ++
      morseDouble (pairCoreTail r s) ++ [isoN 1] := by
    rw [pairWC, hu]
    simp [pairCoreHead, morseDouble, List.flatMap_append, List.append_assoc]
  rw [e8, eC]
  rw [pairConv_caps_wrap r s hr hs] at h1 ⊢
  simp only [morseDouble, List.flatMap_append, List.append_assoc] at h1 h2 ⊢
  exact morseReach_trans h1 h2


end AJConjecture
