import Mathlib
import AJTwist.Knot.TwKPosWords
import AJTwist.Knot.TwKPrefix
import AJHandoff.TorusKnot.PairKIsoSwing

/-!
# The companion `T(2, s)`: stage S and the doubled core with beads, both clasp signs

The statements of `TwKPosSwing` for `r = 2`, with the same routes.

* `morseReach_twkSwing2`: the return strand swings to the right (`morseReach_pass` with the band
  tangle, the macros `RC'`, `SB`, `TC` used by `morseReach_pairWN_WS`); the twists stay at the
  bottom end of the band in front of the new block `A1`.
* `morseReach_twkSQ2`: the tip and the twists of the Hopf pair move down to the hook
  (exchanges), the raw clasp bead is the clasp (`morseReach_twkKRaw`), the outer cap `n2` moves
  next to the inner cap `n3` (exchanges): the result is the doubled core `twkCore2 s` with beads.

Checked outside Lean (`SCR/KP/tools/final_words.py`, `tangle_test.py`): for `(2,3)`, `(2,5)`,
`|ℓ| ≤ 2`, both signs, all words have the Kauffman-bracket operator (thickness one) of the
band-and-clasp word; the two sides of `morseReach_twkSQ2` without `u1 · twists` are equal as
tangles from three strands (thickness one; two for `(2,3)`).
-/

namespace AJConjecture

/-- Interchange of two tangles side by side: `X` on the strands `d … d + a - 1` and `Y` on the `b`
strands to its right exchange their heights (exchanges, letter by letter). -/
private theorem morseReach_interchange_twKTwoSwing (n₀ d a b e : ℕ) (u v X Y : MorseWord)
    (hX : morseFits a X = true) (hY : morseFits b Y = true) (hu : morseOut n₀ u = d + a + b + e) :
    MorseReach n₀ (u ++ morseShiftWord d X ++ morseShiftWord (d + morseOut a X) Y ++ v)
      (u ++ morseShiftWord (d + a) Y ++ morseShiftWord d X ++ v) := by
  induction X using List.reverseRecOn generalizing v with
  | nil =>
    simpa [morseOut, morseShiftWord] using morseReach_refl n₀ (u ++ morseShiftWord (d + a) Y ++ v)
  | append_singleton X0 l ih =>
    rw [morseFits_append, Bool.and_eq_true] at hX
    obtain ⟨hX0, hl⟩ := hX
    set c := morseOut a X0 with hc
    rw [morseFits_cons] at hl
    obtain ⟨hl1, -⟩ := hl
    have hout : morseOut a (X0 ++ [l]) = c + morseKindOut l.1 - morseKindIn l.1 := by
      rw [morseOut_append]; rfl
    have hu' : morseOut n₀ (u ++ morseShiftWord d X0) = d + c + (b + e) := by
      rw [morseOut_append, hu, show d + a + b + e = d + a + (b + e) by ring,
        (morseOut_fits_shift a d (b + e) X0 hX0).1]
    have hsw := morseReach_sweep n₀ (u ++ morseShiftWord d X0) (morseShiftWord (d + c) Y) v
      (shiftLetter d l) (fun y hy ↦ by
        simp only [morseShiftWord, List.mem_map] at hy
        obtain ⟨y', -, rfl⟩ := hy
        simp only [shiftLetter]
        omega)
      (by
        have hYs := morseOut_fits_shift b (d + c) e Y hY
        rw [hu', show d + c + (b + e) = d + c + b + e by ring, morseFits_append, hYs.2, hYs.1]
        simp only [Bool.true_and, morseFits_cons, shiftLetter, morseFits_nil, and_true]
        omega)
    have hmap : (morseShiftWord (d + c) Y).map
        (fun y ↦ (y.1,
          y.2 + morseKindOut (shiftLetter d l).1 - morseKindIn (shiftLetter d l).1)) =
        morseShiftWord (d + morseOut a (X0 ++ [l])) Y := by
      rw [hout]
      simp only [morseShiftWord, List.map_map]
      refine List.map_congr_left fun y _ ↦ ?_
      simp only [Function.comp_apply, shiftLetter, Prod.mk.injEq, true_and]
      omega
    rw [hmap] at hsw
    have h2 := ih (shiftLetter d l :: v) hX0
    rw [morseShiftWord_append]
    simp only [morseShiftWord, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
      List.nil_append] at hsw h2 ⊢
    exact morseReach_trans hsw h2

/-- A word fits on `N` strands and ends on `M`. -/
private def TwkS2Fits (N M : ℕ) (w : MorseWord) : Prop :=
  morseFits N w = true ∧ morseOut N w = M

/-- Arities of consecutive words compose. -/
private theorem TwkS2Fits.append {N M K : ℕ} {a b : MorseWord} (ha : TwkS2Fits N M a)
    (hb : TwkS2Fits M K b) : TwkS2Fits N K (a ++ b) := by
  refine ⟨?_, ?_⟩
  · rw [morseFits_append, ha.1, ha.2, hb.1]; rfl
  · rw [morseOut_append, ha.2, hb.2]

/-- Changing the presentation of the arities. -/
private theorem TwkS2Fits.of_eq {N M N' M' : ℕ} {w : MorseWord} (h : TwkS2Fits N M w)
    (hN : N = N') (hM : M = M') : TwkS2Fits N' M' w := by
  subst hN hM
  exact h

/-- A run of equal blocks. -/
private theorem TwkS2Fits.blk {N : ℕ} {X : MorseWord} (h : TwkS2Fits N N X) (k : ℕ) :
    TwkS2Fits N N (phaseTwoBlk X k) := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact h.append ih

/-- A shifted word with idle strands on the right. -/
private theorem TwkS2Fits.shift {n m : ℕ} {w : MorseWord} (h : TwkS2Fits n m w) (d e : ℕ) :
    TwkS2Fits (d + n + e) (d + m + e) (morseShiftWord d w) := by
  have := morseOut_fits_shift n d e w h.1
  exact ⟨this.2, by rw [this.1, h.2]⟩

/-- Arity of a run of half twists of the band. -/
private theorem twkS2Fits_tw (N : ℕ) (hN : 2 ≤ N) (m : ℕ) :
    TwkS2Fits N N (List.replicate m (isoX false 0)) := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    rw [List.replicate_succ]
    refine TwkS2Fits.append (a := [isoX false 0]) ⟨?_, ?_⟩ ih
    · simp only [morseFits_cons, morseFits_nil, isoX, morseKindIn, and_true]
      omega
    · simp only [morseOut, morseLetterOut, isoX, morseKindIn, morseKindOut]
      omega

/-- The run of negative half twists as a list. -/
private theorem twTwistWord_neg_twKTwoSwing (n : ℕ) :
    twTwistWord (-(2 * (n : ℤ))) = List.replicate (2 * n) (isoX false 0) := by
  rw [twTwistWord, show (-(2 * (n : ℤ))).natAbs = 2 * n by omega,
    show decide (0 < -(2 * (n : ℤ))) = false from decide_eq_false (by omega)]

/-- The twists of the Hopf pair for the negative clasp: none. -/
private theorem twkTw_true_twKTwoSwing : twkTw (twkTipTw true) = [] := rfl

/-- The twists of the Hopf pair for the positive clasp: one negative full twist. -/
private theorem twkTw_false_twKTwoSwing :
    twkTw (twkTipTw false) = [isoX false 0, isoX false 0] := rfl

/-- Macro `RC'` with the twists of the Hopf pair: the cap of the return strand moves past the
twists and the last caps. -/
private theorem morseReach_twkRC_two (σ : Bool) :
    MorseReach 7 ([isoX true 0, isoN 1] ++ morseShiftWord 3 (twkTw (twkTipTw σ)) ++ isoFinalNF)
      (morseShiftWord 1 (morseShiftWord 4 (twkTw (twkTipTw σ)) ++
        [isoU 3, isoX false 4, isoN 3, isoN 3, isoN 2]) ++
        [isoX true 0, isoX true 1, isoX false 1, isoN 1]) := by
  cases σ
  · exact ⟨[(1, .exch (.cap, 1) (.cross false, 5), false),
      (0, .exch (.cross true, 0) (.cross false, 5), false),
      (2, .exch (.cap, 1) (.cross false, 5), false),
      (1, .exch (.cross true, 0) (.cross false, 5), false),
      (3, .exch (.cap, 1) (.cup, 4), false), (2, .exch (.cross true, 0) (.cup, 4), false),
      (4, .exch (.cap, 1) (.cross false, 5), false),
      (3, .exch (.cross true, 0) (.cross false, 5), false), (5, .exch (.cap, 1) (.cap, 4), false),
      (6, .exch (.cap, 1) (.cap, 4), false), (7, .exch (.cap, 1) (.cap, 3), false),
      (8, .r2 1 true, true), (4, .exch (.cross true, 0) (.cap, 4), false),
      (5, .exch (.cross true, 0) (.cap, 4), false), (6, .exch (.cross true, 0) (.cap, 3), false)],
      by decide⟩
  · exact morseReach_isoMacroRC

/-- The block `A1` passes a negative full twist of the band (library macro `NT`). -/
private theorem morseReach_twkA1_twist_two :
    MorseReach 2 (phaseTwoA1 ++ [isoX false 0, isoX false 0])
      ([isoX false 0, isoX false 0] ++ phaseTwoA1) := by
  have h := morseReach_frame 2 2 0 0 [isoX false 0, isoX false 0] [] _ _ morseReach_isoPark_NT
    (by decide) (by decide)
  rw [morseShiftWord_zero_iso, morseShiftWord_zero_iso] at h
  exact h

/-- The block `A1` passes a run of negative full twists of the band. -/
private theorem morseReach_twkA1_twists_two (m : ℕ) :
    MorseReach 2 (phaseTwoA1 ++ List.replicate (2 * m) (isoX false 0))
      (List.replicate (2 * m) (isoX false 0) ++ phaseTwoA1) := by
  induction m with
  | zero => exact morseReach_refl 2 _
  | succ m ih =>
    have e : List.replicate (2 * (m + 1)) (isoX false 0) =
        [isoX false 0, isoX false 0] ++ List.replicate (2 * m) (isoX false 0) := by
      rw [show 2 * (m + 1) = 2 + 2 * m by ring, List.replicate_add]
      rfl
    have h1 := morseReach_frame 2 2 0 0 [] (List.replicate (2 * m) (isoX false 0)) _ _
      morseReach_twkA1_twist_two (by decide) rfl
    have h2 := morseReach_frame 2 2 0 0 [isoX false 0, isoX false 0] [] _ _ ih
      (by rw [morseFits_append, show morseOut 2 phaseTwoA1 = 2 from rfl,
        (twkS2Fits_tw 2 le_rfl _).1]; rfl) (by decide)
    simp only [morseShiftWord_zero_iso, List.nil_append, List.append_nil, List.append_assoc]
      at h1 h2
    rw [e]
    simpa only [List.append_assoc] using morseReach_trans h1 h2

/-- Shifting a letter, with the shift written first. -/
private theorem shiftLetter_twKTwoSwing (d : ℕ) (κ : MorseKind) (i : ℕ) :
    shiftLetter d (κ, i) = (κ, d + i) := by
  simp [shiftLetter, Nat.add_comm]

/-- Idle strands on the right. -/
private theorem TwkS2Fits.weaken {n m : ℕ} {w : MorseWord} (h : TwkS2Fits n m w) (e : ℕ) :
    TwkS2Fits (n + e) (m + e) w := by
  have := h.shift 0 e
  rw [morseShiftWord_zero_iso] at this
  exact this.of_eq (by omega) (by omega)

/-- Arity of the band region for `r = 2`. -/
private theorem twkS2Fits_Mid (s : ℕ) (σ : Bool) (e : ℕ) :
    TwkS2Fits (2 + e) (8 + e) (twkMid2 s σ) := by
  have fInc : TwkS2Fits (2 + e) (2 + e) (isoBInc 0) :=
    TwkS2Fits.weaken (n := 2) (m := 2) ⟨by decide, by decide⟩ e
  have fR0 : TwkS2Fits (2 + e) (6 + e) (isoBR0 0 2) :=
    TwkS2Fits.weaken (n := 2) (m := 6) ⟨by decide, by decide⟩ e
  have fH : TwkS2Fits (6 + e) (8 + e) (twkBHopf 0 2 σ) :=
    TwkS2Fits.weaken (n := 6) (m := 8) ⟨by cases σ <;> decide, by cases σ <;> decide⟩ e
  have fRd : TwkS2Fits (8 + e) (8 + e) (isoBRound 0 2) :=
    (TwkS2Fits.weaken (n := 4) (m := 4) ⟨by decide, by decide⟩ (e + 4)).of_eq (by omega)
      (by omega)
  have fD : TwkS2Fits (8 + e) (8 + e) phaseTwoD :=
    (TwkS2Fits.weaken (n := 4) (m := 4) ⟨by decide, by decide⟩ (e + 4)).of_eq (by omega)
      (by omega)
  exact ((((fInc.blk (s - 2)).append fR0).append fH).append (fRd.blk (s - 2))).append fD

/-- The band for `r = 2` with the top-right climb, the twists of the Hopf pair and the last caps
of the Hopf disc. -/
private def twkSwingT2 (s : ℕ) (σ : Bool) : MorseWord :=
  twkMid2 s σ ++ morseShiftWord 2 phaseTwoA1 ++ [isoN 3] ++
    morseShiftWord 4 (twkTw (twkTipTw σ)) ++ [isoU 3, isoX false 4, isoN 3, isoN 3, isoN 2]

/-- Arity of the band with its last caps. -/
private theorem twkS2Fits_SwingT2 (s : ℕ) (σ : Bool) (e : ℕ) :
    TwkS2Fits (2 + e) (2 + e) (twkSwingT2 s σ) := by
  have fA : TwkS2Fits (8 + e) (6 + e) (morseShiftWord 2 phaseTwoA1 ++ [isoN 3]) :=
    (TwkS2Fits.weaken (n := 5) (m := 3) ⟨by decide, by decide⟩ (e + 3)).of_eq (by omega)
      (by omega)
  have fTw : TwkS2Fits (6 + e) (6 + e) (morseShiftWord 4 (twkTw (twkTipTw σ))) :=
    TwkS2Fits.weaken (n := 6) (m := 6) ⟨by cases σ <;> decide, by cases σ <;> decide⟩ e
  have fC : TwkS2Fits (6 + e) (2 + e) [isoU 3, isoX false 4, isoN 3, isoN 3, isoN 2] :=
    TwkS2Fits.weaken (n := 6) (m := 2) ⟨by decide, by decide⟩ e
  have := (((twkS2Fits_Mid s σ e).append fA).append fTw).append fC
  simpa only [twkSwingT2, List.append_assoc] using this

/-- The cap of the return strand passes the block `A1` and the inner cap of the top-right
climb. -/
private theorem morseReach_twkCapA1_two :
    MorseReach 9 ([isoX true 0, isoN 1] ++ morseShiftWord 1 phaseTwoA1 ++ [isoN 2])
      (morseShiftWord 3 phaseTwoA1 ++ [isoN 4] ++ [isoX true 0, isoN 1]) :=
  ⟨[(1, .exch (.cap, 1) (.cross false, 3), false),
    (0, .exch (.cross true, 0) (.cross false, 3), false),
    (2, .exch (.cap, 1) (.cross false, 3), false),
    (1, .exch (.cross true, 0) (.cross false, 3), false),
    (3, .exch (.cap, 1) (.cup, 4), false), (2, .exch (.cross true, 0) (.cup, 4), false),
    (4, .exch (.cap, 1) (.cross false, 5), false),
    (3, .exch (.cross true, 0) (.cross false, 5), false),
    (5, .exch (.cap, 1) (.cap, 4), false), (4, .exch (.cross true, 0) (.cap, 4), false),
    (6, .exch (.cap, 1) (.cap, 4), false), (5, .exch (.cross true, 0) (.cap, 4), false)],
    by decide⟩

/-- The cap of the return strand moves past the top-right climb, the twists and the last caps
(`r = 2`). -/
private theorem morseReach_twkRC2 (σ : Bool) :
    MorseReach 9 ([isoX true 0, isoN 1] ++ morseShiftWord 1 phaseTwoA1 ++ [isoN 2] ++
        morseShiftWord 3 (twkTw (twkTipTw σ)) ++ isoFinalNF)
      (morseShiftWord 1 (morseShiftWord 2 phaseTwoA1 ++ [isoN 3] ++
        morseShiftWord 4 (twkTw (twkTipTw σ)) ++
        [isoU 3, isoX false 4, isoN 3, isoN 3, isoN 2]) ++
        [isoX true 0, isoX true 1, isoX false 1, isoN 1]) := by
  have h1 := morseReach_frame 9 9 0 0 [] (morseShiftWord 3 (twkTw (twkTipTw σ)) ++ isoFinalNF)
    _ _ morseReach_twkCapA1_two (by decide) rfl
  have h2 := morseReach_frame 7 9 0 0 (morseShiftWord 3 phaseTwoA1 ++ [isoN 4]) [] _ _
    (morseReach_twkRC_two σ) (by cases σ <;> decide) (by decide)
  simp only [morseShiftWord_zero_iso, List.nil_append, List.append_nil] at h1 h2
  have e2 : morseShiftWord 3 phaseTwoA1 ++ [isoN 4] ++
      (morseShiftWord 1 (morseShiftWord 4 (twkTw (twkTipTw σ)) ++
        [isoU 3, isoX false 4, isoN 3, isoN 3, isoN 2]) ++
        [isoX true 0, isoX true 1, isoX false 1, isoN 1]) =
      morseShiftWord 1 (morseShiftWord 2 phaseTwoA1 ++ [isoN 3] ++
        morseShiftWord 4 (twkTw (twkTipTw σ)) ++
        [isoU 3, isoX false 4, isoN 3, isoN 3, isoN 2]) ++
        [isoX true 0, isoX true 1, isoX false 1, isoN 1] := by
    cases σ <;> rfl
  rw [e2] at h2
  refine morseReach_trans ?_ h2
  simpa only [List.append_assoc] using h1

set_option linter.unusedVariables false in
/-- Stage S for `r = 2` with `n` negative full twists at the bottom end of the band. -/
theorem morseReach_twkSwing2 {s : ℕ} (h : IsTorusPair 2 s) (σ : Bool) (n : ℕ) :
    MorseReach 1
      ([isoU 1, isoX true 0] ++ morseShiftWord 1 (twTwistWord (-(2 * (n : ℤ)))) ++ twkN2Tail s σ)
      ([isoU 1] ++ twTwistWord (-(2 * (n : ℤ))) ++ phaseTwoA1 ++ twkS2Tail s σ) := by
  rw [twTwistWord_neg_twKTwoSwing]
  generalize htw : List.replicate (2 * n) (isoX false 0) = tw
  have ftw : ∀ N, 2 ≤ N → TwkS2Fits N N tw := fun N hN ↦ htw ▸ twkS2Fits_tw N hN _
  have fB := twkS2Fits_Mid s σ 0
  have fT2 : TwkS2Fits 2 2 (tw ++ twkSwingT2 s σ) :=
    (ftw 2 le_rfl).append (twkS2Fits_SwingT2 s σ 0)
  have fT3 : TwkS2Fits 3 3 (twkSwingT2 s σ) := twkS2Fits_SwingT2 s σ 1
  -- the cap of the return strand moves to the end
  have hu1 : morseOut 1 ([isoU 1, isoX true 0] ++ morseShiftWord 1 tw ++
      morseShiftWord 1 (twkMid2 s σ)) = 0 + 9 + 0 := by
    rw [morseOut_append, morseOut_append,
      show morseOut 1 [isoU 1, isoX true 0] = 1 + 2 + 0 from rfl,
      (morseOut_fits_shift 2 1 0 _ (ftw 2 le_rfl).1).1, (ftw 2 le_rfl).2,
      (morseOut_fits_shift 2 1 0 _ fB.1).1, fB.2]
  have s1 := morseReach_frame 9 1 0 0 _ [] _ _ (morseReach_twkRC2 σ)
    (by cases σ <;> decide) hu1
  -- the walk passes the band
  have s2 := morseReach_symm (morseReach_pass 1 0 2 true [isoU 1, isoX true 0]
    (tw ++ twkSwingT2 s σ) [isoX false 1, isoN 1] fT2.1 (by decide))
  -- macro `SB`
  have s3 := morseReach_frame 1 1 0 0 [] (tw ++ twkSwingT2 s σ ++ [isoX false 1, isoN 1])
    _ _ morseReach_phaseTwoMacroSB phaseTwoMacroSB_fits rfl
  -- the block `A1` passes the twists
  have s4 := morseReach_frame 2 1 0 1 [isoU 1] (twkSwingT2 s σ ++ [isoX false 1, isoN 1])
    _ _ (htw ▸ morseReach_twkA1_twists_two n)
    (by rw [morseFits_append, show morseOut 2 phaseTwoA1 = 2 from rfl, (ftw 2 le_rfl).1]; rfl)
    rfl
  -- macro `TC`
  have fU : TwkS2Fits 1 3 [isoU 1] := ⟨rfl, rfl⟩
  have fA : TwkS2Fits 3 3 phaseTwoA1 := ⟨rfl, rfl⟩
  have hT3 : morseOut 1 ([isoU 1] ++ tw ++ phaseTwoA1 ++ twkSwingT2 s σ) = 0 + 3 + 0 :=
    (((fU.append (ftw 3 (by omega))).append fA).append fT3).2
  have s5 := morseReach_frame 3 1 0 0 ([isoU 1] ++ tw ++ phaseTwoA1 ++ twkSwingT2 s σ) []
    _ _ morseReach_phaseTwoMacroTC phaseTwoMacroTC_fits hT3
  simp only [morseShiftWord_zero_iso, List.append_nil, List.nil_append] at s1 s3 s4 s5
  rw [fT2.2, show morseWalk true 0 2 = [isoX true 0, isoX true 1] from rfl,
    morseShiftWord_zero_iso] at s2
  have a1 : MorseReach 1
      ([isoU 1, isoX true 0] ++ morseShiftWord 1 tw ++ twkN2Tail s σ)
      ([isoU 1, isoX true 0] ++ morseShiftWord 1 (tw ++ twkSwingT2 s σ) ++
        [isoX true 0, isoX true 1] ++ [isoX false 1, isoN 1]) := by
    simpa only [twkN2Tail, twkSwingT2, morseShiftWord_append, List.append_assoc,
      List.cons_append, List.nil_append] using s1
  have a2 := morseReach_trans a1 (by simpa only [Nat.zero_add] using s2)
  have a3 : MorseReach 1
      ([isoU 1, isoX true 0] ++ [isoX true 0, isoX true 1] ++ (tw ++ twkSwingT2 s σ) ++
        [isoX false 1, isoN 1])
      ([isoU 1] ++ phaseTwoA1 ++ tw ++ twkSwingT2 s σ ++ [isoX false 1, isoN 1]) := by
    simpa only [phaseTwoMacroSB_lhs, phaseTwoMacroSB_rhs, phaseTwoA1, isoU, isoX,
      List.append_assoc, List.cons_append, List.nil_append] using s3
  have a4 : MorseReach 1
      ([isoU 1] ++ phaseTwoA1 ++ tw ++ twkSwingT2 s σ ++ [isoX false 1, isoN 1])
      ([isoU 1] ++ tw ++ phaseTwoA1 ++ twkSwingT2 s σ ++ [isoX false 1, isoN 1]) := by
    simpa only [List.append_assoc] using s4
  have a5 : MorseReach 1
      ([isoU 1] ++ tw ++ phaseTwoA1 ++ twkSwingT2 s σ ++ [isoX false 1, isoN 1])
      ([isoU 1] ++ tw ++ phaseTwoA1 ++ twkS2Tail s σ) := by
    simpa only [twkS2Tail, twkSwingT2, phaseTwoMacroTC_lhs, phaseTwoMacroTC_rhs, isoU, isoX,
      isoN, isoXTip, isoCurlL, morseShiftWord, List.map_cons, List.map_nil, shiftLetter,
      List.append_assoc, List.cons_append, List.nil_append] using s5
  exact morseReach_trans a2 (morseReach_trans a3 (morseReach_trans a4 a5))

/-- From the word after stage S to the doubled core with beads, `r = 2`. -/
theorem morseReach_twkSQ2 {s : ℕ} (h : IsTorusPair 2 s) (σ : Bool) (n : ℕ) :
    MorseReach 1 ([isoU 1] ++ twTwistWord (-(2 * (n : ℤ))) ++ phaseTwoA1 ++ twkS2Tail s σ)
      ([isoU 1] ++ twTwistWord (-(2 * (n : ℤ))) ++ twkQ2Body s σ ++ [isoN 1]) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by have := h.2.1; omega⟩
  rw [twTwistWord_neg_twKTwoSwing]
  generalize htw : List.replicate (2 * n) (isoX false 0) = tw
  have ftw : ∀ N, 2 ≤ N → TwkS2Fits N N tw := fun N hN ↦ htw ▸ twkS2Fits_tw N hN _
  have fU : TwkS2Fits 1 3 [isoU 1] := ⟨rfl, rfl⟩
  have fA : TwkS2Fits 3 3 phaseTwoA1 := ⟨rfl, rfl⟩
  have fInc : TwkS2Fits 3 3 (isoBInc 0) := ⟨by decide, by decide⟩
  have fR0 : TwkS2Fits 3 7 (isoBR0 0 2) := ⟨by decide, by decide⟩
  have fH : TwkS2Fits 7 9 (twkBHopf 0 2 σ) := ⟨by cases σ <;> decide, by cases σ <;> decide⟩
  have f0 : TwkS2Fits 1 7 ([isoU 1] ++ tw ++ phaseTwoA1 ++ phaseTwoBlk (isoBInc 0) k ++
      isoBR0 0 2) :=
    ((((fU.append (ftw 3 (by omega))).append fA).append (fInc.blk k)).append fR0)
  have fRd : TwkS2Fits 5 5 (isoBRound 0 2) := ⟨by decide, by decide⟩
  have fD : TwkS2Fits 5 5 phaseTwoD := ⟨by decide, by decide⟩
  have fAc : TwkS2Fits 5 3 (morseShiftWord 2 phaseTwoA1 ++ [isoN 3]) := ⟨by decide, by decide⟩
  have fX : TwkS2Fits 5 3 (phaseTwoBlk (isoBRound 0 2) k ++ phaseTwoD ++
      (morseShiftWord 2 phaseTwoA1 ++ [isoN 3])) := ((fRd.blk k).append fD).append fAc
  -- the tip moves down to the hook
  have h1 := morseReach_interchange_twKTwoSwing 1 0 5 3 1
    ([isoU 1] ++ tw ++ phaseTwoA1 ++ phaseTwoBlk (isoBInc 0) k ++ isoBR0 0 2 ++ twkBHopf 0 2 σ)
    ([isoN 2] ++ isoCurlL true 1 ++ [isoN 1]) _
    (morseShiftWord 1 (twkTw (twkTipTw σ)) ++ isoXTip) fX.1 (by cases σ <;> decide)
    (by rw [(f0.append fH).2])
  rw [fX.2] at h1
  -- hook and tip are the clasp
  have h2 := morseReach_frame 2 1 4 1
    ([isoU 1] ++ tw ++ phaseTwoA1 ++ phaseTwoBlk (isoBInc 0) k ++ isoBR0 0 2)
    (phaseTwoBlk (isoBRound 0 2) k ++ phaseTwoD ++ (morseShiftWord 2 phaseTwoA1 ++ [isoN 3]) ++
      ([isoN 2] ++ isoCurlL true 1 ++ [isoN 1]))
    _ _ (morseReach_twkKRaw σ) (morseFits_twkKRaw σ).1 (by rw [f0.2])
  have eA : phaseTwoBlk phaseTwoA1 (k + 2 - 1) = phaseTwoA1 ++ phaseTwoBlk (isoBInc 0) k := by
    rw [show k + 2 - 1 = k + 1 by omega, show isoBInc 0 = phaseTwoA1 from rfl]
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons]
  rw [twkS2Tail, twkMid2, twkQ2Body, eA, Nat.add_sub_cancel]
  simp only [morseShiftWord_zero_iso, Nat.zero_add] at h1
  cases σ <;>
  · simp only [twkKRaw, twkHook, twkBHopf, twkTw_true_twKTwoSwing, twkTw_false_twKTwoSwing,
      morseShiftWord, List.map_cons, List.map_nil, shiftLetter_twKTwoSwing,
      isoXTip, claspSWord, isoCurlL, isoU, isoX, isoN, morseDouble, morseDoubleLetter,
      List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Bool.not_true,
      Bool.not_false] at h1 h2 ⊢
    exact morseReach_trans h1 h2

end AJConjecture
