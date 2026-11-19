import Mathlib
import AJHandoff.TorusKnot.PairKIsoPlumb
import AJHandoff.TorusKnot.PairKIsoEndDefs
import AJHandoff.TorusKnot.PairKIsoBeadSlide
import AJHandoff.TorusKnot.PairKIsoParkNormClasp
import AJHandoff.TorusKnot.PairKIsoParkNormArc
import AJHandoff.TorusKnot.PairKIsoParkNormRound
import AJHandoff.TorusKnot.PairKIsoParkSnow
import AJHandoff.TorusKnot.PairKIsoParkProcInst
import AJHandoff.TorusKnot.PairKIsoParkBack
import AJHandoff.TorusKnot.PairKIsoParkWrap

/-!
# Stage C: the curls cancel and the twists gather at the bottom end (crux)

`morseReach_pairWP_WPb`: the cap `n2` of the tail of `pairWP` moves down past the right descents
(exchanges) next to the inner cap `n_{4q-1}`: the band is literally `morseDouble (pairCore r s)`
with beads (`pairWPb`, defined in `PairKIsoParkNormDefs`).

`morseReach_pairWPb_WC` (stage C) is organised by **ports** (`PairKIsoParkDefs`): the port
`a < r` is the band `q + a` before the doubled conveyor. Junction words, all validated
(`SCR/ISO2/tools/park2.py`: equal Kauffman bracket and writhe for `(3,4), (3,5), (4,5), (5,6),
(3,7), (4,7), (5,7)`; Lean `#eval` agrees with the Python words):

* `pairWPb → pairParkV1 → pairParkV2 → pairParkW1` (normalisation: every bead at a port);
* `pairParkW1 → pairParkWF 0 → … → pairParkWF K* → pairParkWB 1 → … → pairParkWB (r - K*) =
  pairParkW3` (the forward snowball from the bottom end and the backward snowball from the top
  end gather all beads at the port `r - 1`, where the clasp sits; one generic lemma,
  `morseReach_park_hop`);
* `pairParkW3 → pairParkW4` (processing on two strands: the twists cross the clasp by macro `K6`,
  the left-edge curls cross to the right edge at the clasp, the curls cancel);
* `pairParkW4 → pairParkW5 → pairParkW6 → pairParkW7 → pairParkW8` (the curls left after the
  clasp go to the top end and through the return strand to the bottom end, the rest goes to the
  bottom end, and they cancel across the twists);
* `pairParkW8 → pairWC` (the clasp turns back onto the right strand).

The sequence is uniform in `(r, s)`: the residue of `s` modulo `r` only enters through the orbit
`a_k = (q + k s) mod r` and `K*` (`PairKIsoParkOrbit`), which the snowball inductions follow.
-/

namespace AJConjecture

/-- A word fits on `N` strands and ends on `M`. -/
private def WPbFits (N M : ℕ) (w : MorseWord) : Prop :=
  morseFits N w = true ∧ morseOut N w = M

/-- Arities of consecutive words compose. -/
private theorem WPbFits.append {N M K : ℕ} {a b : MorseWord} (ha : WPbFits N M a)
    (hb : WPbFits M K b) : WPbFits N K (a ++ b) := by
  refine ⟨?_, ?_⟩
  · rw [morseFits_append, ha.1, ha.2, hb.1]; rfl
  · rw [morseOut_append, ha.2, hb.2]

/-- Idle strands on the right. -/
private theorem WPbFits.weaken {n m : ℕ} {w : MorseWord} (h : WPbFits n m w) (e : ℕ) :
    WPbFits (n + e) (m + e) w := by
  have := morseOut_fits_shift n 0 e w h.1
  rw [morseShiftWord_zero_iso, Nat.zero_add, Nat.zero_add, h.2] at this
  exact ⟨this.2, this.1⟩

/-- Changing the presentation of the arities. -/
private theorem WPbFits.of_eq {N M N' M' : ℕ} {w : MorseWord} (h : WPbFits N M w)
    (hN : N = N') (hM : M = M') : WPbFits N' M' w := by
  subst hN hM
  exact h

/-- A run of equal blocks. -/
private theorem WPbFits.blk {N : ℕ} {X : MorseWord} (h : WPbFits N N X) (k : ℕ) :
    WPbFits N N (phaseTwoBlk X k) := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact h.append ih

/-- A doubled left walk is a word of crossings at the positions up to `2 (p + len)`. -/
private theorem mem_double_walk_wpb (p len : ℕ) :
    ∀ l ∈ morseDouble (morseWalkL true p len),
      (∃ s, l.1 = MorseKind.cross s) ∧ l.2 ≤ 2 * (p + len) := by
  intro l hl
  simp only [morseDouble, List.mem_flatMap, morseWalkL, List.mem_map, List.mem_reverse,
    List.mem_range] at hl
  obtain ⟨_, ⟨i, hi, rfl⟩, hl⟩ := hl
  simp [morseDoubleLetter, cable, cableGen, morseOfBraid, List.range_succ] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> exact ⟨⟨_, rfl⟩, by simp only; omega⟩

/-- Arity of a doubled left walk. -/
private theorem wpbFits_double_walk (p len N : ℕ) (h : 2 * (p + len) + 2 ≤ N) :
    WPbFits N N (morseDouble (morseWalkL true p len)) :=
  ⟨morseFits_of_cross _ _ (fun l hl ↦ (mem_double_walk_wpb p len l hl).1)
    (fun l hl ↦ by have := (mem_double_walk_wpb p len l hl).2; omega),
    morseOut_of_cross _ _ (fun l hl ↦ (mem_double_walk_wpb p len l hl).1)⟩

/-- Closes arity goals of explicit words. -/
local macro "wpb_tac" : tactic =>
  `(tactic| (simp only [WPbFits, morseOut_append, morseOut, morseLetterOut, morseFits_cons,
    morseFits_nil, morseFits_append, isoX, isoU, isoN, isoCurlL, phaseTwoA1, morseShiftWord,
    List.map_cons, List.map_nil, List.map_append, shiftLetter, morseDouble, morseDoubleLetter,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
    morseKindIn, morseKindOut, Bool.and_eq_true, decide_eq_true_eq, and_true, true_and,
    isoWinR, phaseTwoD, phaseTwoClaspS] <;> omega))

/-- Arity of block `LC`. -/
private theorem wpbFits_LC (k : ℕ) : WPbFits (4 * k + 3) (4 * k + 7) (isoBLC (k + 1)) := by
  rw [isoBLC, Nat.add_sub_cancel]
  wpb_tac

/-- Arity of the left climbs. -/
private theorem wpbFits_LCs (m : ℕ) :
    WPbFits 3 (4 * m + 3) ((List.range m).flatMap fun i ↦ isoBLC (i + 1)) := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact (ih.append (wpbFits_LC m)).of_eq rfl (by ring)

/-- Arity of block `DEC`. -/
private theorem wpbFits_Dec (t : ℕ) : WPbFits (4 * t + 7) (4 * t + 7) (isoBDec (t + 1)) := by
  rw [isoBDec, Nat.add_sub_cancel]
  wpb_tac

/-- Arity of block `INC`. -/
private theorem wpbFits_Inc (t : ℕ) : WPbFits (4 * t + 7) (4 * t + 7) (isoBInc (t + 1)) := by
  rw [isoBInc]
  wpb_tac

/-- Arity of the part below round `0`. -/
private theorem wpbFits_Pre (t s : ℕ) : WPbFits 1 (4 * t + 7) (pairPlumbPre (t + 3) s) := by
  rw [pairPlumbPre, show t + 3 - 2 = t + 1 by omega, Nat.add_sub_cancel]
  have hA : WPbFits 1 3 ([isoU 1] ++ phaseTwoA1) := ⟨rfl, rfl⟩
  exact (((hA.append (wpbFits_LCs t)).append
    (wpbFits_LC t)).append ((wpbFits_Dec t).blk _)).append ((wpbFits_Inc t).blk _)

/-- Arity of the window `WIN` (right side). -/
private theorem wpbFits_WinR (t : ℕ) :
    WPbFits (4 * t + 7) (4 * t + 11) (morseShiftWord (4 * (t + 1)) isoWinR) := by
  wpb_tac

/-- Arity of block `ROUND`. -/
private theorem wpbFits_Round (t : ℕ) :
    WPbFits (4 * t + 8) (4 * t + 8) (isoBRound (t + 1) (t + 3)) := by
  rw [isoBRound, show t + 3 - 1 = t + 2 by omega]
  exact (wpbFits_double_walk _ _ _ (by omega)).append (by wpb_tac)

/-- Arity of block `LAST`. -/
private theorem wpbFits_Last (t : ℕ) :
    WPbFits (4 * t + 8) (4 * t + 4) (isoBLast (t + 1) (t + 3)) := by
  rw [isoBLast, morseDouble, List.flatMap_append, ← morseDouble, Nat.add_sub_cancel,
    show t + 3 - 1 = t + 2 by omega]
  refine WPbFits.append (M := 4 * t + 8) (by wpb_tac) (WPbFits.append (M := 4 * t + 8)
    (wpbFits_double_walk _ _ _ (by omega)) ?_)
  wpb_tac

/-- Arity of block `RD`, without the return strand. -/
private theorem wpbFits_Rd (k : ℕ) : WPbFits (4 * k + 6) (4 * k + 2) (isoBRd (k + 1)) := by
  rw [isoBRd, Nat.add_sub_cancel]
  wpb_tac

/-- Arity of the right descents, without the return strand. -/
private theorem wpbFits_Rds (m : ℕ) :
    WPbFits (4 * m + 2) 2 ((List.range m).reverse.flatMap fun i ↦ isoBRd (i + 1)) := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.flatMap_cons]
    exact ((wpbFits_Rd m).append ih).of_eq (by ring) rfl

/-- The prefix of `pairWP` in front of the right descents ends on `4 q + 1` strands. -/
private theorem morseOut_pairWP_prefix (t s : ℕ) :
    morseOut 1 (pairPlumbPre (t + 3) s ++ morseShiftWord (4 * (t + 1)) isoWinR ++
      morseDouble (morseWalkL true (t + 1) (t + 1)) ++
      phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3) ++
      morseShiftWord (4 * (t + 1) - 2) [isoX false 0, isoX false 0, isoN 1]) = 4 * t + 5 := by
  have hS : WPbFits (4 * t + 7) (4 * t + 5)
      (morseShiftWord (4 * (t + 1) - 2) [isoX false 0, isoX false 0, isoN 1]) := by
    wpb_tac
  have hR : WPbFits (4 * t + 11) (4 * t + 11) (phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2)) :=
    (((wpbFits_Round t).blk (s - 2)).weaken 3).of_eq (by ring) (by ring)
  have hL : WPbFits (4 * t + 11) (4 * t + 7) (isoBLast (t + 1) (t + 3)) :=
    ((wpbFits_Last t).weaken 3).of_eq (by ring) (by ring)
  have hW : WPbFits (4 * t + 11) (4 * t + 11) (morseDouble (morseWalkL true (t + 1) (t + 1))) :=
    wpbFits_double_walk _ _ _ (by omega)
  exact ((((((wpbFits_Pre t s).append (wpbFits_WinR t)).append hW).append hR).append
    hL).append hS).2

/-- The cap moves past the right descents. -/
theorem morseReach_pairWP_WPb {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWP r s) (pairWPb r s) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 3 := ⟨r - 3, by omega⟩
  have hRd := wpbFits_Rds t
  have h := morseReach_isoShiftComm 1 (4 * t + 2) 2 1
    (pairPlumbPre (t + 3) s ++ morseShiftWord (4 * (t + 1)) isoWinR ++
      morseDouble (morseWalkL true (t + 1) (t + 1)) ++
      phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3) ++
      morseShiftWord (4 * (t + 1) - 2) [isoX false 0, isoX false 0, isoN 1])
    ((List.range t).reverse.flatMap fun i ↦ isoBRd (i + 1)) [isoN 0]
    [isoU 1, isoX true 2, isoN 1, isoN 1] hRd.1 (by decide)
    (by rw [morseOut_pairWP_prefix])
  rw [hRd.2] at h
  have e : morseShiftWord (4 * (t + 1) - 2) [isoX false 0, isoX false 0] ++
      morseDouble [isoN (2 * (t + 3) - 5)] =
      morseShiftWord (4 * (t + 1) - 2) [isoX false 0, isoX false 0, isoN 1] ++
        morseShiftWord (4 * t + 2) [isoN 0] := by
    simp only [morseShiftWord, List.map_cons, List.map_nil, shiftLetter, morseDouble,
      morseDoubleLetter, isoN, isoX, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.append_nil, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  rw [pairWP, pairWPb, pairPlumbRd, pairPlumbTail, show t + 3 - 2 = t + 1 by omega,
    show t + 1 - 1 = t by omega,
    List.append_assoc _ (morseShiftWord _ [isoX false 0, isoX false 0]), e]
  have e2 : morseShiftWord 2 [isoN 0] ++ [isoU 1, isoX true 2, isoN 1, isoN 1] =
      [isoN 2, isoU 1, isoX true 2, isoN 1, isoN 1] := rfl
  simpa only [List.append_assoc, e2] using morseReach_symm h

/-- Stage C (crux): the curls cancel, the twists gather at the bottom end. -/
theorem morseReach_pairWPb_WC {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWPb r s) (pairWC r s) := by
  obtain ⟨hK1, hKr, -, -⟩ := pairParkKs_spec h hr
  have hF : ∀ k ≤ pairParkKs r s, MorseReach 1 (pairParkWF r s 0) (pairParkWF r s k) := by
    intro k hk
    induction k with
    | zero => exact morseReach_refl 1 _
    | succ k ih =>
      exact morseReach_trans (ih (by omega)) (morseReach_pairParkWF_succ h hr (by omega))
  have hB : ∀ m, 1 ≤ m → m ≤ r - pairParkKs r s →
      MorseReach 1 (pairParkWB r s 1) (pairParkWB r s m) := by
    intro m hm1 hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · exact morseReach_refl 1 _
      · exact morseReach_trans (ih hm0 (by omega)) (morseReach_pairParkWB_succ h hr hm0 (by omega))
  have h3 := hB (r - pairParkKs r s) (by omega) le_rfl
  rw [pairParkWB_last h hr] at h3
  exact morseReach_trans (morseReach_pairWPb_V1 h hr) <|
    morseReach_trans (morseReach_pairParkV1_V2 h hr) <|
    morseReach_trans (morseReach_pairParkV2_W1 h hr) <|
    morseReach_trans (morseReach_pairParkW1_WF0 h hr) <|
    morseReach_trans (hF _ le_rfl) <|
    morseReach_trans (morseReach_pairParkWF_WB1 h hr) <|
    morseReach_trans h3 <|
    morseReach_trans (morseReach_pairParkW3_W4 h hr) <|
    morseReach_trans (morseReach_pairParkW4_W5 h hr) <|
    morseReach_trans (morseReach_pairParkW5_W6 h hr) <|
    morseReach_trans (morseReach_pairParkW6_W7 h hr) <|
    morseReach_trans (morseReach_pairParkW7_W8 h hr) (morseReach_pairParkW8_WC h hr)

end AJConjecture
