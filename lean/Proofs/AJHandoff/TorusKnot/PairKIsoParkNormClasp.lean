import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkNormDefs
import AJHandoff.TorusKnot.PairKIsoParkComm
import AJHandoff.TorusKnot.PairKIsoBeadStep

/-!
# Stage C by ports, normalisation step 1: the clasp and `h` to the port `r - 1`

`morseReach_pairWPb_V1`: in `pairWPb` the window `morseShiftWord (4q) isoWinR` is
`morseDouble [u_{2q+1}] · D_{2q} · C_S` with `C_S = isoClaspS` on the band `2q + 2` (the right
strand) and `D_{2q}` the first doubled crossing of round `0`.

1. `C_S` exchanges with `D_{2q}` (disjoint bands, `morseReach_isoBead_commR` read backwards) and
   turns around the doubled cup `u_{2q+1}` onto the band `2q + 1` (`morseReach_isoBead_cup` read
   backwards with `isoRot_isoClaspS`): it becomes `isoClaspU = isoBeadsWord [.cs]` at the port
   `r - 1`.
2. The twist `h = morseShiftWord (4q - 2) [−0, −0]` (after the cap `n_{q-1}` of the last round,
   on the output band `2q + 1`) turns around the doubled cap `n_{2q-1}` onto the right strand
   (`morseReach_isoBead_cap`; a twist is invariant under rotation, `isoRot_replicate_twist`),
   travels down the right strand past everything on its left (`morseReach_isoBead_commL`: the cap
   `n_{q-1}`, the rounds, the beads of the bands `q - 1, q`, the clasp at the port `r - 1`) and
   turns around the doubled cup `u_{2q+1}` (`morseReach_isoBead_cup`) to the bottom of the port
   `r - 1`, below the clasp.

The rest of the word is unchanged; `D_{2q} · morseDouble (walkL q q)` is the doubled round
`pairDRound r`.
-/

namespace AJConjecture

/-- A word fits on `N` strands and ends on `M`. -/
private def ClaspNormFits (N M : ℕ) (w : MorseWord) : Prop :=
  morseFits N w = true ∧ morseOut N w = M

/-- Arities of consecutive words compose. -/
private theorem ClaspNormFits.append {N M K : ℕ} {a b : MorseWord} (ha : ClaspNormFits N M a)
    (hb : ClaspNormFits M K b) : ClaspNormFits N K (a ++ b) := by
  refine ⟨?_, ?_⟩
  · rw [morseFits_append, ha.1, ha.2, hb.1]; rfl
  · rw [morseOut_append, ha.2, hb.2]

/-- Idle strands on the right. -/
private theorem ClaspNormFits.weaken {n m : ℕ} {w : MorseWord} (h : ClaspNormFits n m w)
    (e : ℕ) : ClaspNormFits (n + e) (m + e) w := by
  have := morseOut_fits_shift n 0 e w h.1
  rw [morseShiftWord_zero_iso, Nat.zero_add, Nat.zero_add, h.2] at this
  exact ⟨this.2, this.1⟩

/-- A run of equal blocks. -/
private theorem ClaspNormFits.blk {N : ℕ} {X : MorseWord} (h : ClaspNormFits N N X) (k : ℕ) :
    ClaspNormFits N N (phaseTwoBlk X k) := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact h.append ih

/-- A doubled left walk is a word of crossings at the positions up to `2 (p + len)`. -/
private theorem mem_double_walk_claspNorm (p len : ℕ) :
    ∀ l ∈ morseDouble (morseWalkL true p len),
      (∃ s, l.1 = MorseKind.cross s) ∧ l.2 ≤ 2 * (p + len) := by
  intro l hl
  simp only [morseDouble, List.mem_flatMap, morseWalkL, List.mem_map, List.mem_reverse,
    List.mem_range] at hl
  obtain ⟨_, ⟨i, hi, rfl⟩, hl⟩ := hl
  simp [morseDoubleLetter, cable, cableGen, morseOfBraid, List.range_succ] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> exact ⟨⟨_, rfl⟩, by simp only; omega⟩

/-- Arity of a doubled left walk. -/
private theorem claspNormFits_double_walk (p len N : ℕ) (h : 2 * (p + len) + 2 ≤ N) :
    ClaspNormFits N N (morseDouble (morseWalkL true p len)) :=
  ⟨morseFits_of_cross _ _ (fun l hl ↦ (mem_double_walk_claspNorm p len l hl).1)
    (fun l hl ↦ by have := (mem_double_walk_claspNorm p len l hl).2; omega),
    morseOut_of_cross _ _ (fun l hl ↦ (mem_double_walk_claspNorm p len l hl).1)⟩

/-- Closes arity goals of explicit words. -/
local macro "cnf_tac" : tactic =>
  `(tactic| (simp only [ClaspNormFits, morseOut_append, morseOut, morseLetterOut, morseFits_cons,
    morseFits_nil, morseFits_append, isoX, isoU, isoN, isoCurlL, phaseTwoA1, morseShiftWord,
    List.map_cons, List.map_nil, List.map_append, shiftLetter, morseDouble, morseDoubleLetter,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
    morseKindIn, morseKindOut, Bool.and_eq_true, decide_eq_true_eq, and_true, true_and] <;>
    omega))

/-- Arity of the left climbs. -/
private theorem claspNormFits_LCs (m : ℕ) :
    ClaspNormFits 3 (4 * m + 3) ((List.range m).flatMap fun i ↦ isoBLC (i + 1)) := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    have hLC : ClaspNormFits (4 * m + 3) (4 * m + 7) (isoBLC (m + 1)) := by
      rw [isoBLC, Nat.add_sub_cancel]; cnf_tac
    have := ih.append hLC
    rwa [show 4 * m + 7 = 4 * (m + 1) + 3 by ring] at this

/-- Arity of the part below round `0`. -/
private theorem claspNormFits_Pre (t s : ℕ) :
    ClaspNormFits 1 (4 * t + 7) (pairPlumbPre (t + 3) s) := by
  rw [pairPlumbPre, show t + 3 - 2 = t + 1 by omega, Nat.add_sub_cancel]
  have hA : ClaspNormFits 1 3 ([isoU 1] ++ phaseTwoA1) := ⟨rfl, rfl⟩
  have hLC : ClaspNormFits (4 * t + 3) (4 * t + 7) (isoBLC (t + 1)) := by
    rw [isoBLC, Nat.add_sub_cancel]; cnf_tac
  have hDec : ClaspNormFits (4 * t + 7) (4 * t + 7) (isoBDec (t + 1)) := by
    rw [isoBDec, Nat.add_sub_cancel]; cnf_tac
  have hInc : ClaspNormFits (4 * t + 7) (4 * t + 7) (isoBInc (t + 1)) := by
    rw [isoBInc]; cnf_tac
  exact (((hA.append (claspNormFits_LCs t)).append hLC).append (hDec.blk _)).append (hInc.blk _)

/-- Arity of the rounds and the last round. -/
private theorem claspNormFits_Mid (t s : ℕ) :
    ClaspNormFits (4 * t + 8) (4 * t + 4) (pairDRound (t + 3) ++
      phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3)) := by
  have hD : ClaspNormFits (4 * t + 8) (4 * t + 8) (pairDRound (t + 3)) := by
    rw [pairDRound, show t + 3 - 2 = t + 1 by omega, show t + 3 - 1 = t + 2 by omega]
    exact claspNormFits_double_walk _ _ _ (by omega)
  have hR : ClaspNormFits (4 * t + 8) (4 * t + 8) (isoBRound (t + 1) (t + 3)) := by
    rw [isoBRound, show t + 3 - 1 = t + 2 by omega]
    exact (claspNormFits_double_walk _ _ _ (by omega)).append (by cnf_tac)
  have hL : ClaspNormFits (4 * t + 8) (4 * t + 4) (isoBLast (t + 1) (t + 3)) := by
    rw [isoBLast, morseDouble, List.flatMap_append, ← morseDouble, Nat.add_sub_cancel,
      show t + 3 - 1 = t + 2 by omega]
    refine ClaspNormFits.append (M := 4 * t + 8) (by cnf_tac) (ClaspNormFits.append
      (M := 4 * t + 8) (claspNormFits_double_walk _ _ _ (by omega)) ?_)
    cnf_tac
  exact (hD.append (hR.blk _)).append hL

/-- A doubled positive crossing is a shifted `phaseTwoD`. -/
private theorem morseDouble_cross_claspNorm (j : ℕ) :
    morseDouble [isoX true j] = morseShiftWord (2 * j) phaseTwoD := by
  simp [morseDouble, isoX, morseDoubleLetter, morseOfBraid, cable, cableGen, phaseTwoD,
    morseShiftWord, shiftLetter, List.range_succ]
  omega

/-- The window of the clasp: the doubled cup of the right arc, the first doubled crossing of
round `0`, the clasp on the right strand. -/
private theorem isoWinR_shift_claspNorm (t : ℕ) :
    morseShiftWord (4 * (t + 1)) isoWinR = morseDouble [isoU (2 * t + 3)] ++
      morseDouble [isoX true (2 * t + 2)] ++ morseShiftWord (4 * t + 8) isoClaspS := by
  rw [morseDouble_cross_claspNorm]
  simp [isoWinR, phaseTwoD, phaseTwoClaspS, isoClaspS, claspWord, morseDouble, morseDoubleLetter,
    isoU, isoX, morseShiftWord, shiftLetter]
  omega

/-- The pieces of `pairWPb`. -/
private theorem pairWPb_eq_claspNorm (t s : ℕ) :
    pairWPb (t + 3) s = pairPlumbPre (t + 3) s ++ morseDouble [isoU (2 * t + 3)] ++
      morseDouble [isoX true (2 * t + 2)] ++ morseShiftWord (4 * t + 8) isoClaspS ++
      morseDouble (morseWalkL true (t + 1) (t + 1)) ++
      phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3) ++
      morseShiftWord (2 * (2 * t + 1)) (isoBeadsWord [.t]) ++ morseDouble [isoN (2 * t + 1)] ++
      pairPlumbRd (t + 3) ++ isoBeadsWord [.p] ++ [isoN 1] := by
  rw [pairWPb, show t + 3 - 2 = t + 1 by omega, isoWinR_shift_claspNorm,
    show 4 * (t + 1) - 2 = 2 * (2 * t + 1) by omega, show 2 * (t + 3) - 5 = 2 * t + 1 by omega]
  simp only [List.append_assoc]
  rfl

/-- The pieces of `pairParkV1`. -/
private theorem pairParkV1_eq_claspNorm (t s : ℕ) :
    pairParkV1 (t + 3) s = pairPlumbPre (t + 3) s ++ morseDouble [isoU (2 * t + 3)] ++
      morseShiftWord (2 * (2 * t + 3)) (isoBeadsWord [.t]) ++
      morseShiftWord (2 * (2 * t + 3)) isoClaspU ++
      morseDouble [isoX true (2 * t + 2)] ++ morseDouble (morseWalkL true (t + 1) (t + 1)) ++
      phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3) ++
      morseDouble [isoN (2 * t + 1)] ++ pairPlumbRd (t + 3) ++ isoBeadsWord [.p] ++
      [isoN 1] := by
  have hD : pairDRound (t + 3) = morseDouble [isoX true (2 * t + 2)] ++
      morseDouble (morseWalkL true (t + 1) (t + 1)) := by
    have hw : morseWalkL true (t + 1) (t + 1 + 1) =
        (MorseKind.cross true, t + 1 + (t + 1)) :: morseWalkL true (t + 1) (t + 1) := by
      simp [morseWalkL, List.range_succ]
    rw [pairDRound, show t + 3 - 2 = t + 1 by omega, show t + 3 - 1 = t + 1 + 1 by omega, hw,
      show t + 1 + (t + 1) = 2 * t + 2 by omega]
    rfl
  rw [pairParkV1, hD, show 2 * (t + 3) - 3 = 2 * t + 3 by omega,
    show 2 * (t + 3) - 5 = 2 * t + 1 by omega, show t + 3 - 2 = t + 1 by omega,
    show isoBeadsWord [.t, .cs] = isoBeadsWord [.t] ++ isoClaspU from rfl, morseShiftWord_append]
  simp only [List.append_assoc]

/-- Normalisation step 1. -/
theorem morseReach_pairWPb_V1 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWPb r s) (pairParkV1 r s) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 3 := ⟨r - 3, by omega⟩
  rw [pairWPb_eq_claspNorm, pairParkV1_eq_claspNorm]
  have hP := claspNormFits_Pre t s
  have hU : morseOut 1 (pairPlumbPre (t + 3) s ++ morseDouble [isoU (2 * t + 3)]) = 4 * t + 11 := by
    rw [morseOut_append, hP.2]
    simp only [morseDouble, isoU, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      morseDoubleLetter, morseOut, morseLetterOut, morseKindOut, morseKindIn]
    omega
  have hMid := claspNormFits_Mid t s
  have hXM : pairDRound (t + 3) ++ phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++
      isoBLast (t + 1) (t + 3) = morseDouble [isoX true (2 * t + 2)] ++
      (morseDouble (morseWalkL true (t + 1) (t + 1)) ++
        phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3)) := by
    have hw : morseWalkL true (t + 1) (t + 1 + 1) =
        (MorseKind.cross true, t + 1 + (t + 1)) :: morseWalkL true (t + 1) (t + 1) := by
      simp [morseWalkL, List.range_succ]
    rw [pairDRound, show t + 3 - 2 = t + 1 by omega, show t + 3 - 1 = t + 1 + 1 by omega, hw,
      show t + 1 + (t + 1) = 2 * t + 2 by omega]
    simp only [List.append_assoc]
    rfl
  rw [hXM] at hMid
  have hX : morseFits (4 * t + 8) (morseDouble [isoX true (2 * t + 2)]) = true ∧
      morseOut (4 * t + 8) (morseDouble [isoX true (2 * t + 2)]) = 4 * t + 8 := by
    have := morseOut_shift_iso (2 * (2 * t + 2)) 4 0 phaseTwoD (by decide)
    rw [show morseOut 4 phaseTwoD = 4 by decide, show 2 * (2 * t + 2) + 4 + 0 = 4 * t + 8 by omega]
      at this
    rw [morseDouble_cross_claspNorm]
    exact ⟨this.2, this.1⟩
  have hTw : morseFits 2 (isoBeadsWord [.t]) = true ∧ morseOut 2 (isoBeadsWord [.t]) = 2 :=
    ⟨rfl, rfl⟩
  have hc := morseOut_shift_iso (2 * (2 * t + 3)) 2 3 isoClaspU (by decide)
  rw [show morseOut 2 isoClaspU = 2 by decide, show 2 * (2 * t + 3) + 2 + 3 = 4 * t + 11 by omega]
    at hc
  have hUC : morseOut 1 (pairPlumbPre (t + 3) s ++ morseDouble [isoU (2 * t + 3)] ++
      morseShiftWord (2 * (2 * t + 3)) isoClaspU) = 4 * t + 11 := by
    rw [morseOut_append, hU, hc.1]
  -- 1. the clasp exchanges with the first doubled crossing of round `0`
  have s1 := morseReach_isoBead_commL 1 (4 * t + 8) 2 1 isoClaspS
    (pairPlumbPre (t + 3) s ++ morseDouble [isoU (2 * t + 3)]) (morseDouble [isoX true (2 * t + 2)])
    ((morseDouble (morseWalkL true (t + 1) (t + 1)) ++
        phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3)) ++
      morseShiftWord (2 * (2 * t + 1)) (isoBeadsWord [.t]) ++ morseDouble [isoN (2 * t + 1)] ++
      pairPlumbRd (t + 3) ++ isoBeadsWord [.p] ++ [isoN 1]) (by decide) (by decide) hX.1
    (by rw [hU])
  rw [hX.2] at s1
  -- 2. it turns around the doubled cup of the right arc
  have s2 := morseReach_isoBead_cup 1 (2 * t + 3) isoClaspU (pairPlumbPre (t + 3) s)
    (morseDouble [isoX true (2 * t + 2)] ++ (morseDouble (morseWalkL true (t + 1) (t + 1)) ++
        phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3)) ++
      morseShiftWord (2 * (2 * t + 1)) (isoBeadsWord [.t]) ++ morseDouble [isoN (2 * t + 1)] ++
      pairPlumbRd (t + 3) ++ isoBeadsWord [.p] ++ [isoN 1]) (by decide) (by decide)
    (by rw [hP.2]; omega)
  rw [show isoRot 2 isoClaspU = isoClaspS by decide,
    show 2 * (2 * t + 3) + 2 = 4 * t + 8 by omega] at s2
  -- 3. the twist `h` turns around the doubled cap of the right arc
  have hm := hMid.weaken 3
  have s3 := morseReach_isoBead_cap 1 (2 * t + 1) (isoBeadsWord [.t])
    (pairPlumbPre (t + 3) s ++ morseDouble [isoU (2 * t + 3)] ++
      morseShiftWord (2 * (2 * t + 3)) isoClaspU ++ (morseDouble [isoX true (2 * t + 2)] ++
        (morseDouble (morseWalkL true (t + 1) (t + 1)) ++
        phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3))))
    (pairPlumbRd (t + 3) ++ isoBeadsWord [.p] ++ [isoN 1]) hTw.1 hTw.2
    (by rw [morseOut_append, hUC, show 4 * t + 11 = 4 * t + 8 + 3 by omega, hm.2]; omega)
  rw [show isoRot 2 (isoBeadsWord [.t]) = isoBeadsWord [.t] by decide,
    show 2 * (2 * t + 1) + 2 = 4 * t + 4 by omega] at s3
  -- 4. it travels down the right strand
  have s4 := morseReach_isoBead_commL 1 (4 * t + 8) 2 1 (isoBeadsWord [.t])
    (pairPlumbPre (t + 3) s ++ morseDouble [isoU (2 * t + 3)] ++
      morseShiftWord (2 * (2 * t + 3)) isoClaspU) (morseDouble [isoX true (2 * t + 2)] ++
        (morseDouble (morseWalkL true (t + 1) (t + 1)) ++
        phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3)))
    (morseDouble [isoN (2 * t + 1)] ++ pairPlumbRd (t + 3) ++ isoBeadsWord [.p] ++ [isoN 1])
    hTw.1 hTw.2 hMid.1 (by rw [hUC])
  rw [hMid.2] at s4
  -- 5. it passes the clasp
  have hsh := morseOut_shift_iso (4 * t + 8) 2 1 (isoBeadsWord [.t]) hTw.1
  have s5 := morseReach_isoBead_commR 1 (2 * (2 * t + 3)) 2 isoClaspU
    (pairPlumbPre (t + 3) s ++ morseDouble [isoU (2 * t + 3)])
    (morseShiftWord (4 * t + 8) (isoBeadsWord [.t]))
    (morseDouble [isoX true (2 * t + 2)] ++ (morseDouble (morseWalkL true (t + 1) (t + 1)) ++
        phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3)) ++
      morseDouble [isoN (2 * t + 1)] ++ pairPlumbRd (t + 3) ++ isoBeadsWord [.p] ++ [isoN 1])
    (by decide) (by decide)
    (by simp [isoBeadsWord, isoBeadWord, morseShiftWord, shiftLetter, isoX]; omega)
    (by rw [hU]; exact hsh.2) (by rw [hU]; omega)
  -- 6. it turns around the doubled cup to the bottom of the port `r - 1`
  have s6 := morseReach_isoBead_cup 1 (2 * t + 3) (isoBeadsWord [.t]) (pairPlumbPre (t + 3) s)
    (morseShiftWord (2 * (2 * t + 3)) isoClaspU ++ morseDouble [isoX true (2 * t + 2)] ++
      (morseDouble (morseWalkL true (t + 1) (t + 1)) ++
        phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3)) ++
      morseDouble [isoN (2 * t + 1)] ++ pairPlumbRd (t + 3) ++ isoBeadsWord [.p] ++ [isoN 1])
    hTw.1 hTw.2 (by rw [hP.2]; omega)
  rw [show isoRot 2 (isoBeadsWord [.t]) = isoBeadsWord [.t] by decide,
    show 2 * (2 * t + 3) + 2 = 4 * t + 8 by omega] at s6
  simp only [List.append_assoc] at s1 s2 s3 s4 s5 s6 ⊢
  exact morseReach_trans (morseReach_symm s1) <| morseReach_trans (morseReach_symm s2) <|
    morseReach_trans s3 <| morseReach_trans (morseReach_symm s4) <| morseReach_trans s5 <|
    morseReach_symm s6

end AJConjecture
