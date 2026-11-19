import Mathlib
import AJHandoff.TorusKnot.PairKIsoRoundNF
import AJHandoff.TorusKnot.PairKIsoStrip

/-!
# Stage N

`morseReach_pairStrip_WN`: the strip word reaches its normal form. Every strip block is replaced
by its normal form with the frame lemma `morseReach_frame` (block by block; the runs `isoStDec`,
`isoStInc`, `isoStRound` by `morseReach_blocks` or induction on the run, each block on a prefix of
fixed size): macros `LC` (at the shifts `2i - 2`), `DEC` (at `2q - 2`), library `A` (at `2q`),
`R0`/`ROUND`/`LAST` of `PairKIsoRoundNF` (at `2q`, `2q`, `2q - 2`), `TRC` (at `4q - 2`), `RD`
(at `2i - 2`), `FINAL` (at `0`). The identity `morseDouble (morseShiftWord q w) =
morseShiftWord (2q) (morseDouble w)` matches the doubled pieces.
-/

namespace AJConjecture

/-- Doubling commutes with shifting. -/
theorem morseDouble_morseShiftWord (q : ℕ) (w : MorseWord) :
    morseDouble (morseShiftWord q w) = morseShiftWord (2 * q) (morseDouble w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨κ, i⟩ := l
    simp only [morseShiftWord, List.map_cons, morseDouble, List.flatMap_cons, List.map_append,
      shiftLetter] at ih ⊢
    rw [ih]
    congr 1
    cases κ with
    | cup => simp [morseDoubleLetter, shiftLetter]; omega
    | cap => simp [morseDoubleLetter, shiftLetter]; omega
    | cross s =>
      cases s <;> simp [morseDoubleLetter, cable, cableGen, morseOfBraid, shiftLetter,
        List.range_succ] <;> omega

/-- Shifting by zero does nothing. -/
private theorem morseShiftWord_zero_stageN (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- A reachable word fits and has the same number of output strands. -/
private theorem morseReach_fits_out_stageN {n : ℕ} {w w' : MorseWord} (h : MorseReach n w w')
    (hw : morseFits n w = true) : morseFits n w' = true ∧ morseOut n w' = morseOut n w := by
  obtain ⟨mvs, hm⟩ := h
  induction mvs generalizing w with
  | nil =>
    simp only [morseApplyAll, Option.some.injEq] at hm
    exact ⟨hm ▸ hw, by rw [hm]⟩
  | cons mv mvs ih =>
    simp only [morseApplyAll] at hm
    cases h1 : morseApply n w mv with
    | none => simp [h1] at hm
    | some w₁ =>
      rw [h1, Option.bind_some] at hm
      obtain ⟨p, r, bk⟩ := mv
      obtain ⟨a, rest, -, rfl, rfl, hok, hs, hd⟩ := morseApply_shape n w w₁ p r bk h1
      have hrule : ∀ src dst : MorseWord, morseFits (morseOut n a) src = true →
          morseFits (morseOut n a) dst = true →
          morseOut (morseOut n a) src = morseOut (morseOut n a) dst →
          morseFits n (a ++ src ++ rest) = true →
          morseFits n (a ++ dst ++ rest) = true ∧
            morseOut n (a ++ dst ++ rest) = morseOut n (a ++ src ++ rest) := by
        intro src dst hs' hd' ho hf
        simp only [morseFits_append, morseOut_append, Bool.and_eq_true] at hf ⊢
        rw [← ho]
        exact ⟨⟨⟨hf.1.1, hd'⟩, hf.2⟩, rfl⟩
      have ho := morseOut_rule_sides r (morseOut n a) hok
      have ho' : morseOut (morseOut n a) (if bk then morseRuleRhs r else morseRuleLhs r) =
          morseOut (morseOut n a) (if bk then morseRuleLhs r else morseRuleRhs r) := by
        cases bk
        · simp only [Bool.false_eq_true, ↓reduceIte] at hs hd ⊢
          exact ho hs hd
        · simp only [↓reduceIte] at hs hd ⊢
          exact (ho hd hs).symm
      obtain ⟨hf1, ho1⟩ := hrule _ _ hs hd ho' hw
      obtain ⟨hf2, ho2⟩ := ih hf1 hm
      exact ⟨hf2, ho2.trans ho1⟩

/-- A replacement of a block: reachability, the source fits on `N` strands and ends on `M`. -/
private def BlockReach (N M : ℕ) (w w' : MorseWord) : Prop :=
  MorseReach N w w' ∧ morseFits N w = true ∧ morseOut N w = M

/-- Replacements of consecutive blocks compose. -/
private theorem BlockReach.append {N M K : ℕ} {a a' b b' : MorseWord} (ha : BlockReach N M a a')
    (hb : BlockReach M K b b') : BlockReach N K (a ++ b) (a' ++ b') := by
  obtain ⟨ra, fa, oa⟩ := ha
  obtain ⟨rb, fb, ob⟩ := hb
  have oa' := (morseReach_fits_out_stageN ra fa).2
  have h1 := morseReach_frame N N 0 0 [] b a a' ra fa (by simp [morseOut])
  have h2 := morseReach_frame M N 0 0 a' [] b b' rb fb (by simp [oa', oa])
  simp only [morseShiftWord_zero_stageN, List.nil_append, List.append_nil] at h1 h2
  refine ⟨morseReach_trans h1 h2, ?_, ?_⟩
  · rw [morseFits_append, fa, oa, fb]; rfl
  · rw [morseOut_append, oa, ob]

/-- A macro moved by `d` strands, with `e` idle strands on the right. -/
private theorem BlockReach.shift {n m : ℕ} (d e : ℕ) {X Y : MorseWord} (h : MorseReach n X Y)
    (hf : morseFits n X = true) (ho : morseOut n X = m) :
    BlockReach (d + n + e) (d + m + e) (morseShiftWord d X) (morseShiftWord d Y) := by
  have h1 := morseReach_frame n (d + n + e) d e [] [] X Y h hf (by simp [morseOut])
  simp only [List.nil_append, List.append_nil] at h1
  obtain ⟨o, f⟩ := morseOut_fits_shift n d e X hf
  exact ⟨h1, f, by rw [o, ho]⟩

/-- A block left unchanged. -/
private theorem BlockReach.refl {N M : ℕ} {w : MorseWord} (hf : morseFits N w = true)
    (ho : morseOut N w = M) : BlockReach N M w w :=
  ⟨morseReach_refl N w, hf, ho⟩

/-- Changing the presentation of the data of a block replacement. -/
private theorem BlockReach.of_eq {N M N' M' : ℕ} {w w' v v' : MorseWord}
    (h : BlockReach N M w w') (hN : N = N') (hM : M = M') (hw : w = v) (hw' : w' = v') :
    BlockReach N' M' v v' := by
  subst hN hM hw hw'
  exact h

/-- A run of equal blocks is replaced block by block. -/
private theorem BlockReach.blk {N : ℕ} {X Y : MorseWord} (h : BlockReach N N X Y) (k : ℕ) :
    BlockReach N N (phaseTwoBlk X k) (phaseTwoBlk Y k) := by
  induction k with
  | zero => exact BlockReach.refl rfl rfl
  | succ k ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact h.append ih

/-- Shifting a run of blocks. -/
private theorem morseShiftWord_phaseTwoBlk_stageN (d : ℕ) (X : MorseWord) (k : ℕ) :
    morseShiftWord d (phaseTwoBlk X k) = phaseTwoBlk (morseShiftWord d X) k := by
  simp [morseShiftWord, phaseTwoBlk, List.map_flatten, List.map_replicate]

/-- Shifting a concatenation of words. -/
private theorem morseShiftWord_flatMap_stageN (d : ℕ) (L : List ℕ) (f : ℕ → MorseWord) :
    morseShiftWord d (L.flatMap f) = L.flatMap fun i ↦ morseShiftWord d (f i) :=
  List.map_flatMap

/-- Shifting a word twice. -/
private theorem morseShiftWord_shift_stageN (a b : ℕ) (w : MorseWord) :
    morseShiftWord a (morseShiftWord b w) = morseShiftWord (b + a) w := by
  simp only [morseShiftWord, List.map_map]
  refine List.map_congr_left fun l _ ↦ ?_
  simp only [Function.comp_apply, shiftLetter, Prod.mk.injEq, true_and]
  omega

/-- A left walk is the shifted walk from zero. -/
private theorem morseWalkL_eq_shift_stageN (s : Bool) (p len : ℕ) :
    morseWalkL s p len = morseShiftWord p (morseWalkL s 0 len) := by
  simp only [morseWalkL, morseShiftWord, List.map_map]
  refine List.map_congr_left fun l _ ↦ ?_
  simp only [Function.comp_apply, shiftLetter, Prod.mk.injEq, true_and]
  omega

/-- Closes equalities of explicit words with shifted positions. -/
local macro "word_eq" : tactic =>
  `(tactic| (simp only [morseShiftWord, List.map_cons, List.map_nil, List.map_append, shiftLetter,
    isoU, isoN, isoX, isoCurlL, phaseTwoA1, phaseTwoMacroA_rhs, phaseTwoMacroA_lhs, morseDouble,
    morseDoubleLetter, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.append_nil, List.cons.injEq, Prod.mk.injEq, true_and, and_true] <;> omega))

/-- Block `LC`. -/
private theorem blockReach_LC_stageN (k : ℕ) :
    BlockReach (4 * k + 3) (4 * k + 7) (isoStLC (k + 1))
      (morseShiftWord 1 (isoBLC (k + 1))) := by
  refine (BlockReach.shift (2 * k) (2 * k + 2) morseReach_isoMacroLC (by decide)
    (by decide : morseOut 1 (isoStLC 1) = 5)).of_eq (by ring) (by ring) ?_ ?_
  · rw [isoStLC, isoStLC, show 2 * (k + 1) - 1 = 1 + 2 * k by omega,
      show 2 * (k + 1) + 1 = 3 + 2 * k by omega, isoBand_add, morseShiftWord_append]
    word_eq
  · rw [isoBLC, Nat.add_sub_cancel]
    word_eq

/-- Block `DEC`. -/
private theorem blockReach_Dec_stageN (t : ℕ) :
    BlockReach (4 * t + 7) (4 * t + 7) (isoStDec (t + 1))
      (morseShiftWord 1 (isoBDec (t + 1))) := by
  refine (BlockReach.shift (2 * t) (2 * t + 4) morseReach_isoMacroDEC (by decide)
    (by decide : morseOut 3 (isoStDec 1) = 3)).of_eq (by ring) (by ring) ?_ ?_
  · rw [isoStDec, isoStDec, show 2 * (t + 1) - 1 = 1 + 2 * t by omega,
      show 2 * (t + 1) + 1 = 3 + 2 * t by omega, isoBand_add, morseShiftWord_append,
      morseShiftWord_append]
    word_eq
  · rw [isoBDec, Nat.add_sub_cancel]
    word_eq

/-- Block `INC` (library macro `A`). -/
private theorem blockReach_Inc_stageN (t : ℕ) :
    BlockReach (4 * t + 7) (4 * t + 7) (isoStInc (t + 1))
      (morseShiftWord 1 (isoBInc (t + 1))) := by
  refine (BlockReach.shift (2 * t + 2) (2 * t + 2) morseReach_phaseTwoMacroA phaseTwoMacroA_fits
    (by decide : morseOut 3 phaseTwoMacroA_lhs = 3)).of_eq (by ring) (by ring) ?_ ?_
  · rw [isoStInc, show 2 * (t + 1) + 1 = 1 + (2 * t + 2) by omega,
      show 2 * (t + 1) + 3 = 3 + (2 * t + 2) by omega, isoBand_add,
      show isoBand 1 3 true = [isoX true 2, isoX true 1, isoX false 2] from rfl]
    word_eq
  · rw [isoBInc]
    word_eq

/-- Block `TRC`. -/
private theorem blockReach_Trc_stageN (t : ℕ) :
    BlockReach (4 * t + 9) (4 * t + 7) (isoStTrc (t + 1))
      (morseShiftWord 1 (isoBTrc (t + 1))) := by
  refine (BlockReach.shift (4 * t + 2) 2 morseReach_isoMacroTRC (by decide)
    (by decide : morseOut 5 (isoBand 1 3 true ++ [isoN 1]) = 3)).of_eq (by ring) (by ring) ?_ ?_
  · rw [isoStTrc, show 4 * (t + 1) - 1 = 1 + (4 * t + 2) by omega,
      show 4 * (t + 1) + 1 = 3 + (4 * t + 2) by omega, isoBand_add, morseShiftWord_append]
    word_eq
  · rw [isoBTrc, show 4 * (t + 1) - 2 = 4 * t + 2 by omega,
      show 4 * (t + 1) - 1 = 4 * t + 3 by omega]
    word_eq

/-- Block `RD`. -/
private theorem blockReach_Rd_stageN (k : ℕ) :
    BlockReach (4 * k + 11) (4 * k + 7) (isoStRd (k + 1))
      (morseShiftWord 1 (isoBRd (k + 1))) := by
  refine (BlockReach.shift (2 * k) (2 * k + 6) morseReach_isoMacroRD (by decide)
    (by decide : morseOut 5 (isoBand 1 3 true ++ [isoN 3, isoN 1]) = 1)).of_eq (by ring)
    (by ring) ?_ ?_
  · rw [isoStRd, show 2 * (k + 1) - 1 = 1 + 2 * k by omega,
      show 2 * (k + 1) + 1 = 3 + 2 * k by omega, isoBand_add, morseShiftWord_append]
    word_eq
  · rw [isoBRd, Nat.add_sub_cancel]
    word_eq

/-- Closes arity goals of explicit words. -/
local macro "fits_tac" : tactic =>
  `(tactic| (simp only [morseOut_append, morseOut, morseLetterOut, morseFits_cons, morseFits_nil,
    morseFits_append, isoX, isoU, isoN, morseKindIn, morseKindOut, Bool.and_eq_true,
    decide_eq_true_eq, and_true, true_and] <;> omega))

/-- The left side of `R0` fits. -/
private theorem morseFits_r0_stageN (r : ℕ) (hr : 1 ≤ r) :
    morseFits (2 * r - 1) ([isoU 1, isoU (1 + 2 * r)] ++ isoBand 1 (1 + 2 * r) true) = true ∧
      morseOut (2 * r - 1) ([isoU 1, isoU (1 + 2 * r)] ++ isoBand 1 (1 + 2 * r) true) =
        2 * r + 3 := by
  rw [morseFits_append, morseOut_append, morseOut_isoBand,
    morseFits_isoBand_of_le (by omega) (by fits_tac)]
  constructor <;> fits_tac

/-- The left side of `ROUND` fits. -/
private theorem morseFits_round_stageN (r : ℕ) (hr : 1 ≤ r) :
    morseFits (2 * r + 1) ([isoU 1] ++ isoBand 1 (1 + 2 * r) true ++ [isoN (1 + 2 * r)]) = true ∧
      morseOut (2 * r + 1) ([isoU 1] ++ isoBand 1 (1 + 2 * r) true ++ [isoN (1 + 2 * r)]) =
        2 * r + 1 := by
  rw [morseFits_append, morseFits_append, morseOut_append, morseOut_append, morseOut_append,
    morseOut_isoBand, morseFits_isoBand_of_le (by omega) (by fits_tac)]
  constructor <;> fits_tac

/-- The left side of `LAST` fits. -/
private theorem morseFits_last_stageN (r : ℕ) (hr : 1 ≤ r) :
    morseFits (2 * r + 3) (isoBand 1 (1 + 2 * r) true ++ [isoN (1 + 2 * r), isoN 1]) = true ∧
      morseOut (2 * r + 3) (isoBand 1 (1 + 2 * r) true ++ [isoN (1 + 2 * r), isoN 1]) =
        2 * r - 1 := by
  rw [morseFits_append, morseOut_append, morseOut_isoBand,
    morseFits_isoBand_of_le (by omega) (by omega)]
  constructor <;> fits_tac

/-- Block `R0`. -/
private theorem blockReach_R0_stageN (t : ℕ) :
    BlockReach (4 * t + 7) (4 * t + 11) (isoStR0 (t + 1) (t + 3))
      (morseShiftWord 1 (isoBR0 (t + 1) (t + 3))) := by
  have hf := morseFits_r0_stageN (t + 3) (by omega)
  refine (BlockReach.shift (2 * t + 2) 0 (morseReach_isoR0NF (t + 3) (by omega)) hf.1 hf.2).of_eq
    (by omega) (by omega) ?_ ?_
  · rw [isoStR0, show 2 * (t + 1) + 1 = 1 + (2 * t + 2) by omega,
      show 1 + (2 * t + 2) + 2 * (t + 3) = 1 + 2 * (t + 3) + (2 * t + 2) by omega,
      isoBand_add, morseShiftWord_append]
    word_eq
  · rw [isoBR0, show t + 1 + (t + 3) - 1 = (t + 3 - 1) + (t + 1) by omega,
      morseWalkL_eq_shift_stageN true (t + 1),
      show [isoU (t + 3 - 1 + (t + 1))] = morseShiftWord (t + 1) [isoU (t + 3 - 1)] by
        simp [morseShiftWord, shiftLetter, isoU],
      ← morseShiftWord_append, morseDouble_morseShiftWord, morseShiftWord_append,
      morseShiftWord_append, morseShiftWord_shift_stageN, morseShiftWord_shift_stageN,
      morseShiftWord_shift_stageN, show 1 + (2 * t + 2) = 2 * (t + 1) + 1 by ring]
    congr 1
    word_eq

/-- Block `ROUND`. -/
private theorem blockReach_Round_stageN (t : ℕ) :
    BlockReach (4 * t + 13) (4 * t + 13) (isoStRound (t + 1) (t + 3))
      (morseShiftWord 1 (isoBRound (t + 1) (t + 3))) := by
  have hf := morseFits_round_stageN (t + 3) (by omega)
  refine (BlockReach.shift (2 * t + 2) 4 (morseReach_isoRoundNF (t + 3) (by omega)) hf.1
    hf.2).of_eq (by omega) (by omega) ?_ ?_
  · rw [isoStRound, show 2 * (t + 1) + 1 = 1 + (2 * t + 2) by omega,
      show 1 + (2 * t + 2) + 2 * (t + 3) = 1 + 2 * (t + 3) + (2 * t + 2) by omega,
      isoBand_add, morseShiftWord_append, morseShiftWord_append]
    word_eq
  · rw [isoBRound, morseWalkL_eq_shift_stageN true (t + 1), morseDouble_morseShiftWord,
      morseShiftWord_append, morseShiftWord_append, morseShiftWord_shift_stageN,
      morseShiftWord_shift_stageN, morseShiftWord_shift_stageN,
      show 1 + (2 * t + 2) = 2 * (t + 1) + 1 by ring]
    congr 1
    word_eq

/-- Block `LAST`. -/
private theorem blockReach_Last_stageN (t : ℕ) :
    BlockReach (4 * t + 13) (4 * t + 9) (isoStLast (t + 1) (t + 3))
      (morseShiftWord 1 (isoBLast (t + 1) (t + 3))) := by
  have hf := morseFits_last_stageN (t + 3) (by omega)
  refine (BlockReach.shift (2 * t) 4 (morseReach_isoLastNF (t + 3) (by omega)) hf.1
    hf.2).of_eq (by omega) (by omega) ?_ ?_
  · rw [isoStLast, show 2 * (t + 1) - 1 = 1 + 2 * t by omega,
      show 1 + 2 * t + 2 * (t + 3) = 1 + 2 * (t + 3) + 2 * t by omega,
      isoBand_add, morseShiftWord_append]
    word_eq
  · have hw : morseWalkL true (t + 1) (t + 3 - 1) ++ [isoN (t + 1 - 1)] =
        morseShiftWord t (morseWalkL true 1 (t + 3 - 1) ++ [isoN 0]) := by
      rw [morseShiftWord_append, morseWalkL_eq_shift_stageN true (t + 1),
        morseWalkL_eq_shift_stageN true 1, morseShiftWord_shift_stageN, Nat.add_comm 1 t]
      simp [morseShiftWord, shiftLetter, isoN]
    rw [isoBLast, hw, morseDouble_morseShiftWord, morseShiftWord_append, morseShiftWord_append,
      morseShiftWord_shift_stageN, morseShiftWord_shift_stageN, morseShiftWord_shift_stageN,
      show 1 + 2 * t = 2 * t + 1 by ring, Nat.add_sub_cancel]
    congr 1
    word_eq

/-- The first Hopf letter, unchanged. -/
private theorem blockReach_Hopf_stageN (t : ℕ) :
    BlockReach (4 * t + 11) (4 * t + 13) (isoStHopf (t + 1) (t + 3))
      (morseShiftWord 1 (isoBHopf (t + 1) (t + 3))) := by
  have hH : isoStHopf (t + 1) (t + 3) =
      [isoU (4 * t + 11), isoX true (4 * t + 10), isoX false (4 * t + 9),
        isoX false (4 * t + 10)] := by
    rw [isoStHopf, show 2 * (t + 1) + 1 + 2 * (t + 3) = 1 + (4 * t + 8) by omega,
      show 2 * (t + 1) + 3 + 2 * (t + 3) = 3 + (4 * t + 8) by omega, isoBand_add,
      show isoBand 1 3 false = [isoX true 2, isoX false 1, isoX false 2] from rfl]
    word_eq
  refine (BlockReach.refl (by rw [hH]; fits_tac) (by rw [hH]; fits_tac)).of_eq rfl rfl rfl ?_
  rw [hH, isoBHopf, show 2 * (t + 1) + 2 * (t + 3) - 1 = 4 * t + 7 by omega]
  word_eq

/-- The left climbs. -/
private theorem blockReach_LCs_stageN (m : ℕ) :
    BlockReach 3 (4 * m + 3) ((List.range m).flatMap fun i ↦ isoStLC (i + 1))
      ((List.range m).flatMap fun i ↦ morseShiftWord 1 (isoBLC (i + 1))) := by
  induction m with
  | zero => exact BlockReach.refl rfl rfl
  | succ m ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact (ih.append (blockReach_LC_stageN m)).of_eq rfl (by ring) rfl rfl

/-- The right descents. -/
private theorem blockReach_Rds_stageN (m : ℕ) :
    BlockReach (4 * m + 7) 7 ((List.range m).reverse.flatMap fun i ↦ isoStRd (i + 1))
      ((List.range m).reverse.flatMap fun i ↦ morseShiftWord 1 (isoBRd (i + 1))) := by
  induction m with
  | zero => exact BlockReach.refl rfl rfl
  | succ m ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.flatMap_cons]
    exact ((blockReach_Rd_stageN m).append ih).of_eq (by ring) rfl rfl rfl

/-- Stage N without the coprimality hypothesis, with the arities of the strip. -/
private theorem blockReach_pairStrip_WN {r s : ℕ} (hr : 3 ≤ r) :
    BlockReach 1 1 (pairStrip r s) (pairWN r s) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 3 := ⟨r - 3, by omega⟩
  have e1 : t + 3 - 2 = t + 1 := by omega
  have hA0 : BlockReach 1 3 [isoU 1, isoX true 0] [isoU 1, isoX true 0] :=
    BlockReach.refl (by decide) (by decide)
  have hRd0 : BlockReach 7 5 isoStRd0 [isoX true 0, isoN 1] :=
    BlockReach.refl (by decide) (by decide)
  have hFin : BlockReach 5 1 isoStFinal isoFinalNF :=
    ⟨morseReach_isoMacroFINAL, by decide, by decide⟩
  have hall := hA0.append ((blockReach_LCs_stageN t).append ((blockReach_LC_stageN t).append
    (((blockReach_Dec_stageN t).blk (pairRunDown (t + 3) s - 1)).append
    (((blockReach_Inc_stageN t).blk (pairRunUp (t + 3) s + 1)).append
    ((blockReach_R0_stageN t).append ((blockReach_Hopf_stageN t).append
    (((blockReach_Round_stageN t).blk (s - 2)).append ((blockReach_Last_stageN t).append
    ((blockReach_Trc_stageN t).append ((blockReach_Rds_stageN t).append
    (hRd0.append hFin)))))))))))
  rw [pairStrip, pairWN, pairBandMid, e1, Nat.add_sub_cancel]
  simp only [morseShiftWord_append, morseShiftWord_phaseTwoBlk_stageN,
    morseShiftWord_flatMap_stageN, List.append_assoc] at hall ⊢
  exact hall

set_option linter.unusedVariables false in
/-- Stage N: the strip word reaches its normal form. -/
theorem morseReach_pairStrip_WN {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairStrip r s) (pairWN r s) :=
  (blockReach_pairStrip_WN hr).1

/-- A word reachable from a fitting word fits and ends on the same number of strands. -/
theorem morseFits_morseOut_of_morseReach {n : ℕ} {w w' : MorseWord} (h : MorseReach n w w')
    (hw : morseFits n w = true) : morseFits n w' = true ∧ morseOut n w' = morseOut n w :=
  morseReach_fits_out_stageN h hw

/-- The word after stage N fits on one strand and ends on one strand. -/
theorem morseFits_pairWN {r s : ℕ} (hr : 3 ≤ r) :
    morseFits 1 (pairWN r s) = true ∧ morseOut 1 (pairWN r s) = 1 := by
  obtain ⟨h, hf, ho⟩ := blockReach_pairStrip_WN (s := s) hr
  have := morseReach_fits_out_stageN h hf
  exact ⟨this.1, this.2.trans ho⟩

end AJConjecture
