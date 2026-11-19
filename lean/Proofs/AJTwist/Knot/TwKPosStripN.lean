import Mathlib
import AJTwist.Knot.TwKPosWords
import AJTwist.Knot.TwKPrefix
import AJHandoff.TorusKnot.PairKIsoStageN

/-!
# Stage N for a clasp of either sign (`r ≥ 3`)

`morseReach_twkStripN`: the strip word with clasp sign `σ` and `n` negative full twists after
`u1 +0` reaches the word after stage N. The isotopy does not touch `u1 +0` and the twists: it is
`morseReach_frame` applied to an isotopy of the tangle `twkStripTail r s σ` (three strands: the
return strand and the first thin pair, to one strand) into `twkNTail r s σ`. For `σ = true` the
statement was first planned as `morseReach_twRel_strip_WN` (`twkStripTail_true`, `twkNTail_true`).

Route: the proof of `morseReach_pairStrip_WN` (`AJHandoff.TorusKnot.PairKIsoStageN`), one frame
per block with the public macros `morseReach_isoMacroLC`, `…DEC`, `…TRC`, `…RD`
(`PairKIsoMacros`), the library macro `A` and the round normal forms `morseReach_isoRoundNF`,
`morseReach_isoR0NF`, `morseReach_isoLastNF` (`PairKIsoRoundNF`). The first Hopf block is not
touched, so its sign plays no role. The last block: for `σ = true` the macro
`morseReach_isoMacroFINAL`; for `σ = false` first `morseReach_twkTipFlip` (frame: five strands,
followed by `n1`), then the letters `morseShiftWord 3 (twkTw 1)` stay in front of the block and
`morseReach_isoMacroFINAL` applies to `isoStFinal`.

Checked outside Lean (`SCR/KP/tools/tangle_test.py`, `final_words.py`): `twkStripTail` and
`twkNTail` have equal Kauffman-bracket operators as tangles from three strands to one for
`(3,4), (3,5), (4,5)`, both signs; with the twists, `|ℓ| ≤ 2`, for `(3,4)`.
-/

namespace AJConjecture

/-- A replacement of a block: reachability, the source fits on `N` strands and ends on `M`. -/
private def TwkNBlock (N M : ℕ) (w w' : MorseWord) : Prop :=
  MorseReach N w w' ∧ morseFits N w = true ∧ morseOut N w = M

/-- Replacements of consecutive blocks compose. -/
private theorem TwkNBlock.append {N M K : ℕ} {a a' b b' : MorseWord} (ha : TwkNBlock N M a a')
    (hb : TwkNBlock M K b b') : TwkNBlock N K (a ++ b) (a' ++ b') := by
  obtain ⟨ra, fa, oa⟩ := ha
  obtain ⟨rb, fb, ob⟩ := hb
  have oa' := (morseFits_morseOut_of_morseReach ra fa).2
  have h1 := morseReach_frame N N 0 0 [] b a a' ra fa (by simp [morseOut])
  have h2 := morseReach_frame M N 0 0 a' [] b b' rb fb (by simp [oa', oa])
  simp only [morseShiftWord_zero_iso, List.nil_append, List.append_nil] at h1 h2
  refine ⟨morseReach_trans h1 h2, ?_, ?_⟩
  · rw [morseFits_append, fa, oa, fb]; rfl
  · rw [morseOut_append, oa, ob]

/-- A macro moved by `d` strands, with `e` idle strands on the right. -/
private theorem TwkNBlock.shift {n m : ℕ} (d e : ℕ) {X Y : MorseWord} (h : MorseReach n X Y)
    (hf : morseFits n X = true) (ho : morseOut n X = m) :
    TwkNBlock (d + n + e) (d + m + e) (morseShiftWord d X) (morseShiftWord d Y) := by
  have h1 := morseReach_frame n (d + n + e) d e [] [] X Y h hf (by simp [morseOut])
  simp only [List.nil_append, List.append_nil] at h1
  obtain ⟨o, f⟩ := morseOut_fits_shift n d e X hf
  exact ⟨h1, f, by rw [o, ho]⟩

/-- A block left unchanged. -/
private theorem TwkNBlock.refl {N M : ℕ} {w : MorseWord} (hf : morseFits N w = true)
    (ho : morseOut N w = M) : TwkNBlock N M w w :=
  ⟨morseReach_refl N w, hf, ho⟩

/-- Changing the presentation of the data of a block replacement. -/
private theorem TwkNBlock.of_eq {N M N' M' : ℕ} {w w' v v' : MorseWord}
    (h : TwkNBlock N M w w') (hN : N = N') (hM : M = M') (hw : w = v) (hw' : w' = v') :
    TwkNBlock N' M' v v' := by
  subst hN hM hw hw'
  exact h

/-- A run of equal blocks is replaced block by block. -/
private theorem TwkNBlock.blk {N : ℕ} {X Y : MorseWord} (h : TwkNBlock N N X Y) (k : ℕ) :
    TwkNBlock N N (phaseTwoBlk X k) (phaseTwoBlk Y k) := by
  induction k with
  | zero => exact TwkNBlock.refl rfl rfl
  | succ k ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact h.append ih

/-- Shifting a run of blocks. -/
private theorem morseShiftWord_phaseTwoBlk_twKStripN (d : ℕ) (X : MorseWord) (k : ℕ) :
    morseShiftWord d (phaseTwoBlk X k) = phaseTwoBlk (morseShiftWord d X) k := by
  simp [morseShiftWord, phaseTwoBlk, List.map_flatten, List.map_replicate]

/-- Shifting a concatenation of words. -/
private theorem morseShiftWord_flatMap_twKStripN (d : ℕ) (L : List ℕ) (f : ℕ → MorseWord) :
    morseShiftWord d (L.flatMap f) = L.flatMap fun i ↦ morseShiftWord d (f i) :=
  List.map_flatMap

/-- Shifting a word twice. -/
private theorem morseShiftWord_shift_twKStripN (a b : ℕ) (w : MorseWord) :
    morseShiftWord a (morseShiftWord b w) = morseShiftWord (b + a) w := by
  simp only [morseShiftWord, List.map_map]
  refine List.map_congr_left fun l _ ↦ ?_
  simp only [Function.comp_apply, shiftLetter, Prod.mk.injEq, true_and]
  omega

/-- A left walk is the shifted walk from zero. -/
private theorem morseWalkL_eq_shift_twKStripN (s : Bool) (p len : ℕ) :
    morseWalkL s p len = morseShiftWord p (morseWalkL s 0 len) := by
  simp only [morseWalkL, morseShiftWord, List.map_map]
  refine List.map_congr_left fun l _ ↦ ?_
  simp only [Function.comp_apply, shiftLetter, Prod.mk.injEq, true_and]
  omega

/-- Closes equalities of explicit words with shifted positions. -/
local macro "twkn_word_eq" : tactic =>
  `(tactic| (simp only [morseShiftWord, List.map_cons, List.map_nil, List.map_append, shiftLetter,
    isoU, isoN, isoX, isoCurlL, phaseTwoA1, phaseTwoMacroA_rhs, phaseTwoMacroA_lhs, morseDouble,
    morseDoubleLetter, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.append_nil, List.cons.injEq, Prod.mk.injEq, true_and, and_true] <;> omega))

/-- Block `LC`. -/
private theorem twkNBlock_LC_twKStripN (k : ℕ) :
    TwkNBlock (4 * k + 3) (4 * k + 7) (isoStLC (k + 1))
      (morseShiftWord 1 (isoBLC (k + 1))) := by
  refine (TwkNBlock.shift (2 * k) (2 * k + 2) morseReach_isoMacroLC (by decide)
    (by decide : morseOut 1 (isoStLC 1) = 5)).of_eq (by ring) (by ring) ?_ ?_
  · rw [isoStLC, isoStLC, show 2 * (k + 1) - 1 = 1 + 2 * k by omega,
      show 2 * (k + 1) + 1 = 3 + 2 * k by omega, isoBand_add, morseShiftWord_append]
    twkn_word_eq
  · rw [isoBLC, Nat.add_sub_cancel]
    twkn_word_eq

/-- Block `DEC`. -/
private theorem twkNBlock_Dec_twKStripN (t : ℕ) :
    TwkNBlock (4 * t + 7) (4 * t + 7) (isoStDec (t + 1))
      (morseShiftWord 1 (isoBDec (t + 1))) := by
  refine (TwkNBlock.shift (2 * t) (2 * t + 4) morseReach_isoMacroDEC (by decide)
    (by decide : morseOut 3 (isoStDec 1) = 3)).of_eq (by ring) (by ring) ?_ ?_
  · rw [isoStDec, isoStDec, show 2 * (t + 1) - 1 = 1 + 2 * t by omega,
      show 2 * (t + 1) + 1 = 3 + 2 * t by omega, isoBand_add, morseShiftWord_append,
      morseShiftWord_append]
    twkn_word_eq
  · rw [isoBDec, Nat.add_sub_cancel]
    twkn_word_eq

/-- Block `INC` (library macro `A`). -/
private theorem twkNBlock_Inc_twKStripN (t : ℕ) :
    TwkNBlock (4 * t + 7) (4 * t + 7) (isoStInc (t + 1))
      (morseShiftWord 1 (isoBInc (t + 1))) := by
  refine (TwkNBlock.shift (2 * t + 2) (2 * t + 2) morseReach_phaseTwoMacroA phaseTwoMacroA_fits
    (by decide : morseOut 3 phaseTwoMacroA_lhs = 3)).of_eq (by ring) (by ring) ?_ ?_
  · rw [isoStInc, show 2 * (t + 1) + 1 = 1 + (2 * t + 2) by omega,
      show 2 * (t + 1) + 3 = 3 + (2 * t + 2) by omega, isoBand_add,
      show isoBand 1 3 true = [isoX true 2, isoX true 1, isoX false 2] from rfl]
    twkn_word_eq
  · rw [isoBInc]
    twkn_word_eq

/-- Block `TRC`. -/
private theorem twkNBlock_Trc_twKStripN (t : ℕ) :
    TwkNBlock (4 * t + 9) (4 * t + 7) (isoStTrc (t + 1))
      (morseShiftWord 1 (isoBTrc (t + 1))) := by
  refine (TwkNBlock.shift (4 * t + 2) 2 morseReach_isoMacroTRC (by decide)
    (by decide : morseOut 5 (isoBand 1 3 true ++ [isoN 1]) = 3)).of_eq (by ring) (by ring) ?_ ?_
  · rw [isoStTrc, show 4 * (t + 1) - 1 = 1 + (4 * t + 2) by omega,
      show 4 * (t + 1) + 1 = 3 + (4 * t + 2) by omega, isoBand_add, morseShiftWord_append]
    twkn_word_eq
  · rw [isoBTrc, show 4 * (t + 1) - 2 = 4 * t + 2 by omega,
      show 4 * (t + 1) - 1 = 4 * t + 3 by omega]
    twkn_word_eq

/-- Block `RD`. -/
private theorem twkNBlock_Rd_twKStripN (k : ℕ) :
    TwkNBlock (4 * k + 11) (4 * k + 7) (isoStRd (k + 1))
      (morseShiftWord 1 (isoBRd (k + 1))) := by
  refine (TwkNBlock.shift (2 * k) (2 * k + 6) morseReach_isoMacroRD (by decide)
    (by decide : morseOut 5 (isoBand 1 3 true ++ [isoN 3, isoN 1]) = 1)).of_eq (by ring)
    (by ring) ?_ ?_
  · rw [isoStRd, show 2 * (k + 1) - 1 = 1 + 2 * k by omega,
      show 2 * (k + 1) + 1 = 3 + 2 * k by omega, isoBand_add, morseShiftWord_append]
    twkn_word_eq
  · rw [isoBRd, Nat.add_sub_cancel]
    twkn_word_eq

/-- Closes arity goals of explicit words. -/
local macro "twkn_fits_tac" : tactic =>
  `(tactic| (simp only [morseOut_append, morseOut, morseLetterOut, morseFits_cons, morseFits_nil,
    morseFits_append, isoX, isoU, isoN, morseKindIn, morseKindOut, Bool.and_eq_true,
    decide_eq_true_eq, and_true, true_and] <;> omega))

/-- The left side of `R0` fits. -/
private theorem morseFits_r0_twKStripN (r : ℕ) (hr : 1 ≤ r) :
    morseFits (2 * r - 1) ([isoU 1, isoU (1 + 2 * r)] ++ isoBand 1 (1 + 2 * r) true) = true ∧
      morseOut (2 * r - 1) ([isoU 1, isoU (1 + 2 * r)] ++ isoBand 1 (1 + 2 * r) true) =
        2 * r + 3 := by
  rw [morseFits_append, morseOut_append, morseOut_isoBand,
    morseFits_isoBand_of_le (by omega) (by twkn_fits_tac)]
  constructor <;> twkn_fits_tac

/-- The left side of `ROUND` fits. -/
private theorem morseFits_round_twKStripN (r : ℕ) (hr : 1 ≤ r) :
    morseFits (2 * r + 1) ([isoU 1] ++ isoBand 1 (1 + 2 * r) true ++ [isoN (1 + 2 * r)]) = true ∧
      morseOut (2 * r + 1) ([isoU 1] ++ isoBand 1 (1 + 2 * r) true ++ [isoN (1 + 2 * r)]) =
        2 * r + 1 := by
  rw [morseFits_append, morseFits_append, morseOut_append, morseOut_append, morseOut_append,
    morseOut_isoBand, morseFits_isoBand_of_le (by omega) (by twkn_fits_tac)]
  constructor <;> twkn_fits_tac

/-- The left side of `LAST` fits. -/
private theorem morseFits_last_twKStripN (r : ℕ) (hr : 1 ≤ r) :
    morseFits (2 * r + 3) (isoBand 1 (1 + 2 * r) true ++ [isoN (1 + 2 * r), isoN 1]) = true ∧
      morseOut (2 * r + 3) (isoBand 1 (1 + 2 * r) true ++ [isoN (1 + 2 * r), isoN 1]) =
        2 * r - 1 := by
  rw [morseFits_append, morseOut_append, morseOut_isoBand,
    morseFits_isoBand_of_le (by omega) (by omega)]
  constructor <;> twkn_fits_tac

/-- Block `R0`. -/
private theorem twkNBlock_R0_twKStripN (t : ℕ) :
    TwkNBlock (4 * t + 7) (4 * t + 11) (isoStR0 (t + 1) (t + 3))
      (morseShiftWord 1 (isoBR0 (t + 1) (t + 3))) := by
  have hf := morseFits_r0_twKStripN (t + 3) (by omega)
  refine (TwkNBlock.shift (2 * t + 2) 0 (morseReach_isoR0NF (t + 3) (by omega)) hf.1 hf.2).of_eq
    (by omega) (by omega) ?_ ?_
  · rw [isoStR0, show 2 * (t + 1) + 1 = 1 + (2 * t + 2) by omega,
      show 1 + (2 * t + 2) + 2 * (t + 3) = 1 + 2 * (t + 3) + (2 * t + 2) by omega,
      isoBand_add, morseShiftWord_append]
    twkn_word_eq
  · rw [isoBR0, show t + 1 + (t + 3) - 1 = (t + 3 - 1) + (t + 1) by omega,
      morseWalkL_eq_shift_twKStripN true (t + 1),
      show [isoU (t + 3 - 1 + (t + 1))] = morseShiftWord (t + 1) [isoU (t + 3 - 1)] by
        simp [morseShiftWord, shiftLetter, isoU],
      ← morseShiftWord_append, morseDouble_morseShiftWord, morseShiftWord_append,
      morseShiftWord_append, morseShiftWord_shift_twKStripN, morseShiftWord_shift_twKStripN,
      morseShiftWord_shift_twKStripN, show 1 + (2 * t + 2) = 2 * (t + 1) + 1 by ring]
    congr 1
    twkn_word_eq

/-- Block `ROUND`. -/
private theorem twkNBlock_Round_twKStripN (t : ℕ) :
    TwkNBlock (4 * t + 13) (4 * t + 13) (isoStRound (t + 1) (t + 3))
      (morseShiftWord 1 (isoBRound (t + 1) (t + 3))) := by
  have hf := morseFits_round_twKStripN (t + 3) (by omega)
  refine (TwkNBlock.shift (2 * t + 2) 4 (morseReach_isoRoundNF (t + 3) (by omega)) hf.1
    hf.2).of_eq (by omega) (by omega) ?_ ?_
  · rw [isoStRound, show 2 * (t + 1) + 1 = 1 + (2 * t + 2) by omega,
      show 1 + (2 * t + 2) + 2 * (t + 3) = 1 + 2 * (t + 3) + (2 * t + 2) by omega,
      isoBand_add, morseShiftWord_append, morseShiftWord_append]
    twkn_word_eq
  · rw [isoBRound, morseWalkL_eq_shift_twKStripN true (t + 1), morseDouble_morseShiftWord,
      morseShiftWord_append, morseShiftWord_append, morseShiftWord_shift_twKStripN,
      morseShiftWord_shift_twKStripN, morseShiftWord_shift_twKStripN,
      show 1 + (2 * t + 2) = 2 * (t + 1) + 1 by ring]
    congr 1
    twkn_word_eq

/-- Block `LAST`. -/
private theorem twkNBlock_Last_twKStripN (t : ℕ) :
    TwkNBlock (4 * t + 13) (4 * t + 9) (isoStLast (t + 1) (t + 3))
      (morseShiftWord 1 (isoBLast (t + 1) (t + 3))) := by
  have hf := morseFits_last_twKStripN (t + 3) (by omega)
  refine (TwkNBlock.shift (2 * t) 4 (morseReach_isoLastNF (t + 3) (by omega)) hf.1
    hf.2).of_eq (by omega) (by omega) ?_ ?_
  · rw [isoStLast, show 2 * (t + 1) - 1 = 1 + 2 * t by omega,
      show 1 + 2 * t + 2 * (t + 3) = 1 + 2 * (t + 3) + 2 * t by omega,
      isoBand_add, morseShiftWord_append]
    twkn_word_eq
  · have hw : morseWalkL true (t + 1) (t + 3 - 1) ++ [isoN (t + 1 - 1)] =
        morseShiftWord t (morseWalkL true 1 (t + 3 - 1) ++ [isoN 0]) := by
      rw [morseShiftWord_append, morseWalkL_eq_shift_twKStripN true (t + 1),
        morseWalkL_eq_shift_twKStripN true 1, morseShiftWord_shift_twKStripN, Nat.add_comm 1 t]
      simp [morseShiftWord, shiftLetter, isoN]
    rw [isoBLast, hw, morseDouble_morseShiftWord, morseShiftWord_append, morseShiftWord_append,
      morseShiftWord_shift_twKStripN, morseShiftWord_shift_twKStripN,
      morseShiftWord_shift_twKStripN, show 1 + 2 * t = 2 * t + 1 by ring, Nat.add_sub_cancel]
    congr 1
    twkn_word_eq

/-- The left climbs. -/
private theorem twkNBlock_LCs_twKStripN (m : ℕ) :
    TwkNBlock 3 (4 * m + 3) ((List.range m).flatMap fun i ↦ isoStLC (i + 1))
      ((List.range m).flatMap fun i ↦ morseShiftWord 1 (isoBLC (i + 1))) := by
  induction m with
  | zero => exact TwkNBlock.refl rfl rfl
  | succ m ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact (ih.append (twkNBlock_LC_twKStripN m)).of_eq rfl (by ring) rfl rfl

/-- The right descents. -/
private theorem twkNBlock_Rds_twKStripN (m : ℕ) :
    TwkNBlock (4 * m + 7) 7 ((List.range m).reverse.flatMap fun i ↦ isoStRd (i + 1))
      ((List.range m).reverse.flatMap fun i ↦ morseShiftWord 1 (isoBRd (i + 1))) := by
  induction m with
  | zero => exact TwkNBlock.refl rfl rfl
  | succ m ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.flatMap_cons]
    exact ((twkNBlock_Rd_twKStripN m).append ih).of_eq (by ring) rfl rfl rfl

/-- The first Hopf block of either sign, unchanged. -/
private theorem twkNBlock_Hopf_twKStripN (t : ℕ) (σ : Bool) :
    TwkNBlock (4 * t + 11) (4 * t + 13) (twkStHopf (t + 1) (t + 3) σ)
      (morseShiftWord 1 (twkBHopf (t + 1) (t + 3) σ)) := by
  have hH : twkStHopf (t + 1) (t + 3) σ =
      [isoU (4 * t + 11), isoX true (4 * t + 10), isoX (!σ) (4 * t + 9),
        isoX false (4 * t + 10)] := by
    rw [twkStHopf, show 2 * (t + 1) + 1 + 2 * (t + 3) = 1 + (4 * t + 8) by omega,
      show 2 * (t + 1) + 3 + 2 * (t + 3) = 3 + (4 * t + 8) by omega, isoBand_add,
      show isoBand 1 3 (!σ) = [isoX true 2, isoX (!σ) 1, isoX false 2] from rfl]
    twkn_word_eq
  refine (TwkNBlock.refl (by rw [hH]; twkn_fits_tac) (by rw [hH]; twkn_fits_tac)).of_eq rfl rfl
    rfl ?_
  rw [hH, twkBHopf, show 2 * (t + 1) + 2 * (t + 3) - 1 = 4 * t + 7 by omega]
  twkn_word_eq

/-- The last block: for the positive clasp the tip flip, then the macro `FINAL`. -/
private theorem twkNBlock_Final_twKStripN (σ : Bool) :
    TwkNBlock 5 1 (twkStFinal σ) (morseShiftWord 3 (twkTw (twkTipTw σ)) ++ isoFinalNF) := by
  cases σ with
  | true => exact ⟨morseReach_isoMacroFINAL, by decide, by decide⟩
  | false =>
    have h1 := morseReach_frame 5 5 0 0 [] [isoN 1] _ _ morseReach_twkTipFlip (by decide) rfl
    have h2 := morseReach_frame 5 5 0 0 (morseShiftWord 3 (twkTw 1)) [] _ _
      morseReach_isoMacroFINAL (by decide) (by decide)
    simp only [morseShiftWord_zero_iso, List.nil_append, List.append_nil] at h1 h2
    refine ⟨morseReach_trans ?_ h2, by decide, by decide⟩
    simpa only [twkStFinal, isoStFinal, List.append_assoc, List.cons_append, List.nil_append,
      Bool.not_false] using h1

/-- Stage N for the tail of the strip word: a tangle from three strands to one. -/
private theorem twkNBlock_tail_twKStripN {r s : ℕ} (hr : 3 ≤ r) (σ : Bool) :
    TwkNBlock 3 1 (twkStripTail r s σ) (twkNTail r s σ) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 3 := ⟨r - 3, by omega⟩
  have e1 : t + 3 - 2 = t + 1 := by omega
  have hRd0 : TwkNBlock 7 5 isoStRd0 [isoX true 0, isoN 1] :=
    TwkNBlock.refl (by decide) (by decide)
  have hall := (twkNBlock_LCs_twKStripN t).append ((twkNBlock_LC_twKStripN t).append
    (((twkNBlock_Dec_twKStripN t).blk (pairRunDown (t + 3) s - 1)).append
    (((twkNBlock_Inc_twKStripN t).blk (pairRunUp (t + 3) s + 1)).append
    ((twkNBlock_R0_twKStripN t).append ((twkNBlock_Hopf_twKStripN t σ).append
    (((twkNBlock_Round_twKStripN t).blk (s - 2)).append ((twkNBlock_Last_twKStripN t).append
    ((twkNBlock_Trc_twKStripN t).append ((twkNBlock_Rds_twKStripN t).append
    (hRd0.append (twkNBlock_Final_twKStripN σ)))))))))))
  rw [twkStripTail, twkNTail, twkBandMid, e1, Nat.add_sub_cancel]
  simp only [morseShiftWord_append, morseShiftWord_phaseTwoBlk_twKStripN,
    morseShiftWord_flatMap_twKStripN, List.append_assoc] at hall ⊢
  exact hall

/-- A run of half twists does not change the number of strands. -/
private theorem morseOut_twTwistWord_twKStripN (N d : ℕ) (k : ℤ) :
    morseOut N (morseShiftWord d (twTwistWord k)) = N := by
  rw [twTwistWord]
  induction k.natAbs with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ]
    simpa [morseShiftWord, morseOut, morseLetterOut, shiftLetter, isoX, morseKindIn,
      morseKindOut] using ih

set_option linter.unusedVariables false in
/-- Stage N with `n` negative full twists after `u1 +0`, both clasp signs. -/
theorem morseReach_twkStripN {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) (σ : Bool) (n : ℕ) :
    MorseReach 1
      ([isoU 1, isoX true 0] ++ morseShiftWord 1 (twTwistWord (-(2 * (n : ℤ)))) ++
        twkStripTail r s σ)
      ([isoU 1, isoX true 0] ++ morseShiftWord 1 (twTwistWord (-(2 * (n : ℤ)))) ++
        twkNTail r s σ) := by
  obtain ⟨hreach, hfit, -⟩ := twkNBlock_tail_twKStripN (s := s) hr σ
  have hu : morseOut 1 ([isoU 1, isoX true 0] ++
      morseShiftWord 1 (twTwistWord (-(2 * (n : ℤ))))) = 0 + 3 + 0 := by
    rw [morseOut_append, morseOut_twTwistWord_twKStripN]
    rfl
  have hfr := morseReach_frame 3 1 0 0 _ [] _ _ hreach hfit hu
  simpa only [morseShiftWord_zero_iso, List.append_nil] using hfr

end AJConjecture
