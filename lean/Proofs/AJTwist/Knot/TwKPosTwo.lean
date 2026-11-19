import Mathlib
import AJTwist.Knot.TwKPosWords
import AJTwist.Knot.TwKPrefix
import AJHandoff.TorusKnot.PairKIsoRoundNF
import AJHandoff.TorusKnot.PairKIsoMacros

/-!
# The companion `T(2, s)`: stage N, both clasp signs

For `r = 2` the route of `r ≥ 3` applies to the generic fence word (`twkStrip2Tail`), with the
core `twkCore2 s`; the older chain of `AJFamily.Skein.TorusPhaseTwo*` is not used.

* `morseReach_twkStrip2N` (stage N; a frame of an isotopy of tangles from three strands): the
  `s - 2` blocks of the increasing run by the library macro `A` (`morseReach_twIncP`); round `0`
  and the rounds by `morseReach_isoR0NF 2`, `morseReach_isoRoundNF 2`; the hook unchanged; the
  last three blocks `b(0,3) n3 · b(1,3) n1 · twkStFinal σ` by `morseReach_isoMacroFINAL` (after
  `morseReach_twkTipFlip` for `σ = false`) and one new fixed macro on seven strands,
  `morseReach_twkTop2` (proved here: eight moves for the descent, then the moves of the library
  macro `TRC`).

Checked outside Lean (`SCR/KP/tools/final_words.py`, `tangle_test.py`): for `(2,3)`, `(2,5)`,
`|ℓ| ≤ 2`, both signs, both words have the Kauffman-bracket operator (thickness one) of the
band-and-clasp word; as tangles from three strands, at thickness one and for `(2,3)` also two.
-/

namespace AJConjecture

/-- The last blocks of the positive bands for `r = 2`: the descent to the disc `0` over the last
open pair and the top-right climb become the last doubled crossing, the right descent and a
block `A1` with the inner cap. A fixed macro (three open pairs and the return strand in, the
return-strand part `+0 n1` and the Hopf pair out). -/
theorem morseReach_twkTop2 :
    MorseReach 7 (isoBand 0 3 true ++ [isoN 3] ++ isoBand 1 3 true ++ [isoN 1])
      (morseShiftWord 1 phaseTwoD ++ [isoX true 0, isoN 1] ++ morseShiftWord 1 phaseTwoA1 ++
        [isoN 2]) := by
  exact ⟨[(1, .r2 3 true, true), (2, .exch (.cross true, 1) (.cross false, 3), true),
      (3, .exch (.cross true, 0) (.cross false, 3), true), (3, .r2 2 true, true),
      (4, .exch (.cross true, 0) (.cross false, 2), true),
      (6, .exch (.cross false, 1) (.cross false, 3), true), (7, .capSlide 2 false false, false),
      (5, .capSlide 1 false false, false), (9, .capSlide 1 false false, true),
      (11, .zig 2 true, true), (12, .capSlide 3 false false, true),
      (14, .exch (.cap, 2) (.cap, 4), true), (11, .exch (.cup, 2) (.cross false, 2), false),
      (9, .r3 1 false, true), (8, .r3 1 false, true), (7, .r2 1 true, false),
      (6, .r2 2 true, false)], by decide⟩

/-- A replacement of a block: reachability, the source fits on `N` strands and ends on `M`. -/
private def TwkN2Block (N M : ℕ) (w w' : MorseWord) : Prop :=
  MorseReach N w w' ∧ morseFits N w = true ∧ morseOut N w = M

/-- Replacements of consecutive blocks compose. -/
private theorem TwkN2Block.append {N M K : ℕ} {a a' b b' : MorseWord} (ha : TwkN2Block N M a a')
    (hb : TwkN2Block M K b b') : TwkN2Block N K (a ++ b) (a' ++ b') := by
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
private theorem TwkN2Block.shift {n m : ℕ} (d e : ℕ) {X Y : MorseWord} (h : MorseReach n X Y)
    (hf : morseFits n X = true) (ho : morseOut n X = m) :
    TwkN2Block (d + n + e) (d + m + e) (morseShiftWord d X) (morseShiftWord d Y) := by
  have h1 := morseReach_frame n (d + n + e) d e [] [] X Y h hf (by simp [morseOut])
  simp only [List.nil_append, List.append_nil] at h1
  obtain ⟨o, f⟩ := morseOut_fits_shift n d e X hf
  exact ⟨h1, f, by rw [o, ho]⟩

/-- A block left unchanged. -/
private theorem TwkN2Block.refl {N M : ℕ} {w : MorseWord} (hf : morseFits N w = true)
    (ho : morseOut N w = M) : TwkN2Block N M w w :=
  ⟨morseReach_refl N w, hf, ho⟩

/-- Changing the presentation of the data of a block replacement. -/
private theorem TwkN2Block.of_eq {N M N' M' : ℕ} {w w' v v' : MorseWord}
    (h : TwkN2Block N M w w') (hN : N = N') (hM : M = M') (hw : w = v) (hw' : w' = v') :
    TwkN2Block N' M' v v' := by
  subst hN hM hw hw'
  exact h

/-- A run of equal blocks is replaced block by block. -/
private theorem TwkN2Block.blk {N : ℕ} {X Y : MorseWord} (h : TwkN2Block N N X Y) (k : ℕ) :
    TwkN2Block N N (phaseTwoBlk X k) (phaseTwoBlk Y k) := by
  induction k with
  | zero => exact TwkN2Block.refl rfl rfl
  | succ k ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact h.append ih

/-- Shifting a run of blocks. -/
private theorem morseShiftWord_phaseTwoBlk_twKTwo (d : ℕ) (X : MorseWord) (k : ℕ) :
    morseShiftWord d (phaseTwoBlk X k) = phaseTwoBlk (morseShiftWord d X) k := by
  simp [morseShiftWord, phaseTwoBlk, List.map_flatten, List.map_replicate]

/-- A macro with `e` idle strands on the right. -/
private theorem TwkN2Block.idle {n m : ℕ} (e : ℕ) {X Y : MorseWord} (h : MorseReach n X Y)
    (hf : morseFits n X = true) (ho : morseOut n X = m) : TwkN2Block (n + e) (m + e) X Y :=
  (TwkN2Block.shift 0 e h hf ho).of_eq (by omega) (by omega) (morseShiftWord_zero_iso X)
    (morseShiftWord_zero_iso Y)

/-- A block of the increasing run (library macro `A`). -/
private theorem twkN2Block_Inc : TwkN2Block 3 3 (isoStInc 0) (morseShiftWord 1 (isoBInc 0)) :=
  ⟨morseReach_twIncP, by decide, by decide⟩

/-- Round `0`. -/
private theorem twkN2Block_R0 : TwkN2Block 3 7 (isoStR0 0 2) (morseShiftWord 1 (isoBR0 0 2)) :=
  ⟨morseReach_isoR0NF 2 le_rfl, by decide, by decide⟩

/-- The first Hopf block of either sign, unchanged. -/
private theorem twkN2Block_Hopf (σ : Bool) :
    TwkN2Block 7 9 (twkStHopf 0 2 σ) (morseShiftWord 1 (twkBHopf 0 2 σ)) := by
  have e : morseShiftWord 1 (twkBHopf 0 2 σ) = twkStHopf 0 2 σ := by cases σ <;> rfl
  rw [e]
  exact TwkN2Block.refl (by cases σ <;> decide) (by cases σ <;> decide)

/-- A round. -/
private theorem twkN2Block_Round :
    TwkN2Block 9 9 (isoStRound 0 2) (morseShiftWord 1 (isoBRound 0 2)) :=
  TwkN2Block.idle (n := 5) (m := 5) 4 (morseReach_isoRoundNF 2 le_rfl) (by decide) (by decide)

/-- The descent to the disc `0` and the top-right climb (macro `morseReach_twkTop2`). -/
private theorem twkN2Block_Top :
    TwkN2Block 9 5 (isoBand 0 3 true ++ [isoN 3] ++ isoBand 1 3 true ++ [isoN 1])
      (morseShiftWord 1 phaseTwoD ++ [isoX true 0, isoN 1] ++ morseShiftWord 1 phaseTwoA1 ++
        [isoN 2]) :=
  TwkN2Block.idle (n := 7) (m := 3) 2 morseReach_twkTop2 (by decide) (by decide)

/-- The last block: for the positive clasp the tip flip, then the macro `FINAL`. -/
private theorem twkN2Block_Final (σ : Bool) :
    TwkN2Block 5 1 (twkStFinal σ) (morseShiftWord 3 (twkTw (twkTipTw σ)) ++ isoFinalNF) := by
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

/-- Stage N for the tail of the strip word, `r = 2`: a tangle from three strands to one. -/
private theorem twkN2Block_tail (s : ℕ) (σ : Bool) :
    TwkN2Block 3 1 (twkStrip2Tail s σ) (twkN2Tail s σ) := by
  have hall := (twkN2Block_Inc.blk (s - 2)).append (twkN2Block_R0.append
    ((twkN2Block_Hopf σ).append ((twkN2Block_Round.blk (s - 2)).append
    (twkN2Block_Top.append (twkN2Block_Final σ)))))
  rw [twkStrip2Tail, twkN2Tail, twkMid2]
  simp only [morseShiftWord_append, morseShiftWord_phaseTwoBlk_twKTwo, List.append_assoc]
    at hall ⊢
  exact hall

/-- A run of half twists does not change the number of strands. -/
private theorem morseOut_twTwistWord_twKTwo (N d : ℕ) (k : ℤ) :
    morseOut N (morseShiftWord d (twTwistWord k)) = N := by
  rw [twTwistWord]
  induction k.natAbs with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ]
    simpa [morseShiftWord, morseOut, morseLetterOut, shiftLetter, isoX, morseKindIn,
      morseKindOut] using ih

set_option linter.unusedVariables false in
/-- Stage N for `r = 2` with `n` negative full twists after `u1 +0`, both clasp signs. -/
theorem morseReach_twkStrip2N {s : ℕ} (h : IsTorusPair 2 s) (σ : Bool) (n : ℕ) :
    MorseReach 1
      ([isoU 1, isoX true 0] ++ morseShiftWord 1 (twTwistWord (-(2 * (n : ℤ)))) ++
        twkStrip2Tail s σ)
      ([isoU 1, isoX true 0] ++ morseShiftWord 1 (twTwistWord (-(2 * (n : ℤ)))) ++
        twkN2Tail s σ) := by
  obtain ⟨hreach, hfit, -⟩ := twkN2Block_tail s σ
  have hu : morseOut 1 ([isoU 1, isoX true 0] ++
      morseShiftWord 1 (twTwistWord (-(2 * (n : ℤ))))) = 0 + 3 + 0 := by
    rw [morseOut_append, morseOut_twTwistWord_twKTwo]
    rfl
  have hfr := morseReach_frame 3 1 0 0 _ [] _ _ hreach hfit hu
  simpa only [morseShiftWord_zero_iso, List.append_nil] using hfr

end AJConjecture
