import Mathlib
import AJTwist.Knot.TwKPosWords
import AJTwist.Knot.TwKPrefix
import AJHandoff.TorusKnot.PairKIsoSwing
import AJHandoff.TorusKnot.PairKIsoPlumb

/-!
# Stage S and the doubled core with beads (`r ≥ 3`), both clasp signs

* `morseReach_twkSwing`: the return strand swings to the right. The `n` negative full twists
  placed after `u1 +0` stay at the bottom end of the band, in front of the block `A1` created by
  the swing. Route: the proof of `morseReach_pairWN_WS` (`PairKIsoSwing`): the macro `RC'` at the
  end, `morseReach_pass` with the tangle `twists ++ twkBandMid r s σ ++ …` (it is generic in the
  tangle; the Hopf pair with the twists of `twkTipTw σ` is part of it), the macro `SB` after the
  twists (on the strands `0, 1`) are commuted behind the walk, and `TC`.
* `morseReach_twkSQ`: from the word after stage S to the doubled core with beads. It is
  `morseReach_frame` (prefix `u1 · twists`) applied to an isotopy of tangles from three strands
  (the band and the return strand on its right) to one, `A1 · twkSTail ~ twkQBody · n1`:
  1. the tip `isoXTip` and the twists of the Hopf pair in front of it move down the Hopf pair to
     the hook (exchanges, as the first step `morseReach_pairWS_WP1` of stage P);
  2. hook, twists and tip are the raw clasp bead `twkKRaw σ` on the band of the right strand,
     which is the clasp `claspSWord σ` (`morseReach_twkKRaw`, by `morseReach_frame`);
  3. the outer cap `n2` of the top-right climb moves down next to its inner cap
     (`morseReach_pairWP_WPb` of `PairKIsoEndPark` does this for the library word).
  The stages `WP2`, `WP3` and the macro `WIN` of the library are not needed.

Checked outside Lean (`SCR/KP/tools/final_words.py`, `tangle_test.py`): equal Kauffman-bracket
operators (thickness one) of the long knots with `2ℓ` half twists, `|ℓ| ≤ 2`, for `(3,4)`, and
of the two sides of `morseReach_twkSQ` as tangles for `(3,4), (3,5), (4,5)`, both signs.
-/

namespace AJConjecture

/-- Interchange of two tangles side by side: `X` on the strands `d … d + a - 1` and `Y` on the `b`
strands to its right exchange their heights (exchanges, letter by letter). -/
private theorem morseReach_interchange_twKSwing (n₀ d a b e : ℕ) (u v X Y : MorseWord)
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
private def TwkSFits (N M : ℕ) (w : MorseWord) : Prop :=
  morseFits N w = true ∧ morseOut N w = M

/-- Arities of consecutive words compose. -/
private theorem TwkSFits.append {N M K : ℕ} {a b : MorseWord} (ha : TwkSFits N M a)
    (hb : TwkSFits M K b) : TwkSFits N K (a ++ b) := by
  refine ⟨?_, ?_⟩
  · rw [morseFits_append, ha.1, ha.2, hb.1]; rfl
  · rw [morseOut_append, ha.2, hb.2]

/-- Changing the presentation of the arities. -/
private theorem TwkSFits.of_eq {N M N' M' : ℕ} {w : MorseWord} (h : TwkSFits N M w)
    (hN : N = N') (hM : M = M') : TwkSFits N' M' w := by
  subst hN hM
  exact h

/-- A run of equal blocks. -/
private theorem TwkSFits.blk {N : ℕ} {X : MorseWord} (h : TwkSFits N N X) (k : ℕ) :
    TwkSFits N N (phaseTwoBlk X k) := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact h.append ih

/-- A shifted word with idle strands on the right. -/
private theorem TwkSFits.shift {n m : ℕ} {w : MorseWord} (h : TwkSFits n m w) (d e : ℕ) :
    TwkSFits (d + n + e) (d + m + e) (morseShiftWord d w) := by
  have := morseOut_fits_shift n d e w h.1
  exact ⟨this.2, by rw [this.1, h.2]⟩

/-- A doubled left walk is a word of crossings at the positions up to `2 (p + len)`. -/
private theorem mem_double_walk_twKSwing (p len : ℕ) :
    ∀ l ∈ morseDouble (morseWalkL true p len),
      (∃ s, l.1 = MorseKind.cross s) ∧ l.2 ≤ 2 * (p + len) := by
  intro l hl
  simp only [morseDouble, List.mem_flatMap, morseWalkL, List.mem_map, List.mem_reverse,
    List.mem_range] at hl
  obtain ⟨_, ⟨i, hi, rfl⟩, hl⟩ := hl
  simp [morseDoubleLetter, cable, cableGen, morseOfBraid, List.range_succ] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> exact ⟨⟨_, rfl⟩, by simp only; omega⟩

/-- Arity of a doubled left walk. -/
private theorem twkSFits_double_walk (p len N : ℕ) (h : 2 * (p + len) + 2 ≤ N) :
    TwkSFits N N (morseDouble (morseWalkL true p len)) :=
  ⟨morseFits_of_cross _ _ (fun l hl ↦ (mem_double_walk_twKSwing p len l hl).1)
    (fun l hl ↦ by have := (mem_double_walk_twKSwing p len l hl).2; omega),
    morseOut_of_cross _ _ (fun l hl ↦ (mem_double_walk_twKSwing p len l hl).1)⟩

/-- Closes arity goals of explicit words. -/
local macro "twks_pf_tac" : tactic =>
  `(tactic| (simp only [TwkSFits, morseOut_append, morseOut, morseLetterOut, morseFits_cons,
    morseFits_nil, morseFits_append, isoX, isoU, isoN, isoCurlL, phaseTwoA1, morseShiftWord,
    List.map_cons, List.map_nil, List.map_append, shiftLetter, morseDouble, morseDoubleLetter,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
    morseKindIn, morseKindOut, Bool.and_eq_true, decide_eq_true_eq, and_true, true_and] <;>
    omega))

/-- Arity of block `LC`. -/
private theorem twkSFits_LC (k e : ℕ) :
    TwkSFits (4 * k + 2 + e) (4 * k + 6 + e) (isoBLC (k + 1)) := by
  rw [isoBLC, Nat.add_sub_cancel]
  twks_pf_tac

/-- Arity of the left climbs. -/
private theorem twkSFits_LCs (m e : ℕ) :
    TwkSFits (2 + e) (4 * m + 2 + e) ((List.range m).flatMap fun i ↦ isoBLC (i + 1)) := by
  induction m with
  | zero => exact ⟨rfl, by simp [morseOut]⟩
  | succ m ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact (ih.append (twkSFits_LC m e)).of_eq rfl (by ring)

/-- Arity of block `DEC`. -/
private theorem twkSFits_Dec (t e : ℕ) :
    TwkSFits (4 * t + 6 + e) (4 * t + 6 + e) (isoBDec (t + 1)) := by
  rw [isoBDec, Nat.add_sub_cancel]
  twks_pf_tac

/-- Arity of block `INC`. -/
private theorem twkSFits_Inc (t e : ℕ) :
    TwkSFits (4 * t + 6 + e) (4 * t + 6 + e) (isoBInc (t + 1)) := by
  rw [isoBInc]
  twks_pf_tac

/-- Arity of block `R0`. -/
private theorem twkSFits_R0 (t e : ℕ) :
    TwkSFits (4 * t + 6 + e) (4 * t + 10 + e) (isoBR0 (t + 1) (t + 3)) := by
  rw [isoBR0, morseDouble, List.flatMap_append, ← morseDouble,
    show t + 1 + (t + 3) - 1 = 2 * t + 3 by omega, show t + 3 - 1 = t + 2 by omega]
  refine TwkSFits.append (M := 4 * t + 10 + e) (TwkSFits.append (M := 4 * t + 10 + e) ?_
    (twkSFits_double_walk _ _ _ (by omega))) ?_ <;> twks_pf_tac

/-- Arity of the hook. -/
private theorem twkSFits_Hopf (t : ℕ) (σ : Bool) (e : ℕ) :
    TwkSFits (4 * t + 10 + e) (4 * t + 12 + e) (twkBHopf (t + 1) (t + 3) σ) := by
  rw [twkBHopf]
  twks_pf_tac

/-- Arity of block `ROUND`. -/
private theorem twkSFits_Round (t e : ℕ) :
    TwkSFits (4 * t + 8 + e) (4 * t + 8 + e) (isoBRound (t + 1) (t + 3)) := by
  rw [isoBRound, show t + 3 - 1 = t + 2 by omega]
  exact (twkSFits_double_walk _ _ _ (by omega)).append (by twks_pf_tac)

/-- Arity of block `LAST`. -/
private theorem twkSFits_Last (t e : ℕ) :
    TwkSFits (4 * t + 8 + e) (4 * t + 4 + e) (isoBLast (t + 1) (t + 3)) := by
  rw [isoBLast, morseDouble, List.flatMap_append, ← morseDouble, Nat.add_sub_cancel,
    show t + 3 - 1 = t + 2 by omega]
  refine TwkSFits.append (M := 4 * t + 8 + e) (by twks_pf_tac)
    (TwkSFits.append (M := 4 * t + 8 + e) (twkSFits_double_walk _ _ _ (by omega)) ?_)
  twks_pf_tac

/-- Arity of the block `A1` of the top-right climb. -/
private theorem twkSFits_TrcA (t e : ℕ) :
    TwkSFits (4 * t + 4 + e) (4 * t + 4 + e) (morseShiftWord (4 * t + 2) phaseTwoA1) := by
  twks_pf_tac

/-- Arity of block `TRC`. -/
private theorem twkSFits_Trc (t e : ℕ) :
    TwkSFits (4 * t + 5 + e) (4 * t + 3 + e) (isoBTrc (t + 1)) := by
  rw [isoBTrc, show 4 * (t + 1) - 2 = 4 * t + 2 by omega, show 4 * (t + 1) - 1 = 4 * t + 3 by omega]
  twks_pf_tac

/-- Arity of block `RD`. -/
private theorem twkSFits_Rd (k e : ℕ) :
    TwkSFits (4 * k + 6 + e) (4 * k + 2 + e) (isoBRd (k + 1)) := by
  rw [isoBRd, Nat.add_sub_cancel]
  twks_pf_tac

/-- Arity of the right descents. -/
private theorem twkSFits_Rds (m e : ℕ) :
    TwkSFits (4 * m + 2 + e) (2 + e) ((List.range m).reverse.flatMap fun i ↦ isoBRd (i + 1)) := by
  induction m with
  | zero => exact ⟨rfl, by simp [morseOut]⟩
  | succ m ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.flatMap_cons]
    exact ((twkSFits_Rd m e).append ih).of_eq (by ring) rfl

/-- Arity of a run of half twists of the band. -/
private theorem twkSFits_tw (N : ℕ) (hN : 2 ≤ N) (m : ℕ) :
    TwkSFits N N (List.replicate m (isoX false 0)) := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    rw [List.replicate_succ]
    exact TwkSFits.append (a := [isoX false 0]) (by twks_pf_tac) ih

/-- The run of negative half twists as a list. -/
private theorem twTwistWord_neg_twKSwing (n : ℕ) :
    twTwistWord (-(2 * (n : ℤ))) = List.replicate (2 * n) (isoX false 0) := by
  rw [twTwistWord, show (-(2 * (n : ℤ))).natAbs = 2 * n by omega,
    show decide (0 < -(2 * (n : ℤ))) = false from decide_eq_false (by omega)]

/-- The part of the band below round `0`. -/
private def twkSPre (r s : ℕ) : MorseWord :=
  (List.range (r - 2 - 1)).flatMap (fun i ↦ isoBLC (i + 1)) ++ isoBLC (r - 2) ++
    phaseTwoBlk (isoBDec (r - 2)) (pairRunDown r s - 1) ++
    phaseTwoBlk (isoBInc (r - 2)) (pairRunUp r s + 1) ++ isoBR0 (r - 2) r

/-- The right descents. -/
private def twkSRd (r : ℕ) : MorseWord :=
  (List.range (r - 2 - 1)).reverse.flatMap (fun i ↦ isoBRd (i + 1))

/-- The band region: the part below round `0` with round `0`, the hook, the rounds, the
top-right climb, the right descents. -/
private theorem twkBandMid_eq_twKSwing (r s : ℕ) (σ : Bool) :
    twkBandMid r s σ = twkSPre r s ++ twkBHopf (r - 2) r σ ++
      phaseTwoBlk (isoBRound (r - 2) r) (s - 2) ++ isoBLast (r - 2) r ++ isoBTrc (r - 2) ++
      twkSRd r := by
  simp only [twkBandMid, twkSPre, twkSRd, List.append_assoc]

/-- Arity of the part of the band below the hook. -/
private theorem twkSFits_Pre (t s e : ℕ) :
    TwkSFits (2 + e) (4 * t + 10 + e) (twkSPre (t + 3) s) := by
  rw [twkSPre, show t + 3 - 2 = t + 1 by omega, Nat.add_sub_cancel]
  exact ((((twkSFits_LCs t e).append (twkSFits_LC t e)).append
    ((twkSFits_Dec t e).blk _)).append ((twkSFits_Inc t e).blk _)).append (twkSFits_R0 t e)

/-- Arity of the words between the hook and the last caps of the band. -/
private theorem twkSFits_Post (t s e : ℕ) :
    TwkSFits (4 * t + 9 + e) (3 + e) (phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++
      isoBLast (t + 1) (t + 3) ++ isoBTrc (t + 1) ++ twkSRd (t + 3)) := by
  rw [twkSRd, show t + 3 - 2 - 1 = t by omega]
  have h4 : TwkSFits (4 * t + 5 + e) (3 + e) (isoBTrc (t + 1) ++
      (List.range t).reverse.flatMap fun i ↦ isoBRd (i + 1)) :=
    (twkSFits_Trc t e).append ((twkSFits_Rds t (e + 1)).of_eq (by ring) (by ring))
  have := ((((twkSFits_Round t (e + 1)).blk (s - 2)).append (twkSFits_Last t (e + 1))).append
    (h4.of_eq (by ring) rfl))
  simpa only [List.append_assoc] using this.of_eq (by ring) rfl

/-- Arity of the band region. -/
private theorem twkSFits_Mid (t s : ℕ) (σ : Bool) (e : ℕ) :
    TwkSFits (2 + e) (6 + e) (twkBandMid (t + 3) s σ) := by
  rw [twkBandMid_eq_twKSwing, show t + 3 - 2 = t + 1 by omega]
  have := ((twkSFits_Pre t s e).append (twkSFits_Hopf t σ e)).append
    ((twkSFits_Post t s (e + 3)).of_eq (by ring) rfl)
  simpa only [List.append_assoc] using this.of_eq rfl (by ring)

/-- The twists of the Hopf pair for the negative clasp: none. -/
private theorem twkTw_true_twKSwing : twkTw (twkTipTw true) = [] := rfl

/-- The twists of the Hopf pair for the positive clasp: one negative full twist. -/
private theorem twkTw_false_twKSwing : twkTw (twkTipTw false) = [isoX false 0, isoX false 0] := rfl

/-- The band with the twists of the Hopf pair and the last caps of the Hopf disc. -/
private def twkSwingT (r s : ℕ) (σ : Bool) : MorseWord :=
  twkBandMid r s σ ++ morseShiftWord 4 (twkTw (twkTipTw σ)) ++
    [isoU 3, isoX false 4, isoN 3, isoN 3, isoN 2]

/-- Arity of the band with its last caps. -/
private theorem twkSFits_SwingT (t s : ℕ) (σ : Bool) (e : ℕ) :
    TwkSFits (2 + e) (2 + e) (twkSwingT (t + 3) s σ) := by
  have hTw : TwkSFits (6 + e) (6 + e) (morseShiftWord 4 (twkTw (twkTipTw σ))) := by
    cases σ
    · rw [twkTw_false_twKSwing]; twks_pf_tac
    · rw [twkTw_true_twKSwing]; exact ⟨rfl, rfl⟩
  exact ((twkSFits_Mid t s σ e).append hTw).append (by twks_pf_tac)

/-- Macro `RC'` with the twists of the Hopf pair: the cap of the return strand moves past the
twists and the last caps. -/
private theorem morseReach_twkRC (σ : Bool) :
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
private theorem morseReach_twkA1_twist :
    MorseReach 2 (phaseTwoA1 ++ [isoX false 0, isoX false 0])
      ([isoX false 0, isoX false 0] ++ phaseTwoA1) := by
  have h := morseReach_frame 2 2 0 0 [isoX false 0, isoX false 0] [] _ _ morseReach_isoPark_NT
    (by decide) (by decide)
  rw [morseShiftWord_zero_iso, morseShiftWord_zero_iso] at h
  exact h

/-- The block `A1` passes a run of negative full twists of the band. -/
private theorem morseReach_twkA1_twists (m : ℕ) :
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
      morseReach_twkA1_twist (by decide) rfl
    have h2 := morseReach_frame 2 2 0 0 [isoX false 0, isoX false 0] [] _ _ ih
      (by rw [morseFits_append, show morseOut 2 phaseTwoA1 = 2 from rfl,
        (twkSFits_tw 2 le_rfl _).1]; rfl) (by decide)
    simp only [morseShiftWord_zero_iso, List.nil_append, List.append_nil, List.append_assoc]
      at h1 h2
    rw [e]
    simpa only [List.append_assoc] using morseReach_trans h1 h2

set_option linter.unusedVariables false in
/-- Stage S with `n` negative full twists at the bottom end of the band. -/
theorem morseReach_twkSwing {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) (σ : Bool) (n : ℕ) :
    MorseReach 1
      ([isoU 1, isoX true 0] ++ morseShiftWord 1 (twTwistWord (-(2 * (n : ℤ)))) ++ twkNTail r s σ)
      ([isoU 1] ++ twTwistWord (-(2 * (n : ℤ))) ++ phaseTwoA1 ++ twkSTail r s σ) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 3 := ⟨r - 3, by omega⟩
  rw [twTwistWord_neg_twKSwing]
  generalize htw : List.replicate (2 * n) (isoX false 0) = tw
  have ftw : ∀ N, 2 ≤ N → TwkSFits N N tw := fun N hN ↦ htw ▸ twkSFits_tw N hN _
  have fB := twkSFits_Mid t s σ 0
  have fT2 : TwkSFits 2 2 (tw ++ twkSwingT (t + 3) s σ) :=
    (ftw 2 le_rfl).append (twkSFits_SwingT t s σ 0)
  have fT3 : TwkSFits 3 3 (twkSwingT (t + 3) s σ) := twkSFits_SwingT t s σ 1
  -- macro `RC'`
  have hu1 : morseOut 1 ([isoU 1, isoX true 0] ++ morseShiftWord 1 tw ++
      morseShiftWord 1 (twkBandMid (t + 3) s σ)) = 0 + 7 + 0 := by
    rw [morseOut_append, morseOut_append,
      show morseOut 1 [isoU 1, isoX true 0] = 1 + 2 + 0 from rfl,
      (morseOut_fits_shift 2 1 0 _ (ftw 2 le_rfl).1).1, (ftw 2 le_rfl).2,
      (morseOut_fits_shift 2 1 0 _ fB.1).1, fB.2]
  have s1 := morseReach_frame 7 1 0 0 _ [] _ _ (morseReach_twkRC σ)
    (by cases σ <;> decide) hu1
  -- the walk passes the band
  have s2 := morseReach_symm (morseReach_pass 1 0 2 true [isoU 1, isoX true 0]
    (tw ++ twkSwingT (t + 3) s σ) [isoX false 1, isoN 1] fT2.1 (by decide))
  -- macro `SB`
  have s3 := morseReach_frame 1 1 0 0 [] (tw ++ twkSwingT (t + 3) s σ ++ [isoX false 1, isoN 1])
    _ _ morseReach_phaseTwoMacroSB phaseTwoMacroSB_fits rfl
  -- the block `A1` passes the twists
  have s4 := morseReach_frame 2 1 0 1 [isoU 1] (twkSwingT (t + 3) s σ ++ [isoX false 1, isoN 1])
    _ _ (htw ▸ morseReach_twkA1_twists n)
    (by rw [morseFits_append, show morseOut 2 phaseTwoA1 = 2 from rfl, (ftw 2 le_rfl).1]; rfl)
    rfl
  -- macro `TC`
  have fU : TwkSFits 1 3 [isoU 1] := ⟨rfl, rfl⟩
  have fA : TwkSFits 3 3 phaseTwoA1 := ⟨rfl, rfl⟩
  have hT3 : morseOut 1 ([isoU 1] ++ tw ++ phaseTwoA1 ++ twkSwingT (t + 3) s σ) = 0 + 3 + 0 :=
    (((fU.append (ftw 3 (by omega))).append fA).append fT3).2
  have s5 := morseReach_frame 3 1 0 0 ([isoU 1] ++ tw ++ phaseTwoA1 ++ twkSwingT (t + 3) s σ) []
    _ _ morseReach_phaseTwoMacroTC phaseTwoMacroTC_fits hT3
  simp only [morseShiftWord_zero_iso, List.append_nil, List.nil_append] at s1 s3 s4 s5
  rw [fT2.2, show morseWalk true 0 2 = [isoX true 0, isoX true 1] from rfl,
    morseShiftWord_zero_iso] at s2
  have a1 : MorseReach 1
      ([isoU 1, isoX true 0] ++ morseShiftWord 1 tw ++ twkNTail (t + 3) s σ)
      ([isoU 1, isoX true 0] ++ morseShiftWord 1 (tw ++ twkSwingT (t + 3) s σ) ++
        [isoX true 0, isoX true 1] ++ [isoX false 1, isoN 1]) := by
    simpa only [twkNTail, twkSwingT, morseShiftWord_append, List.append_assoc,
      List.cons_append, List.nil_append] using s1
  have a2 := morseReach_trans a1 (by simpa only [Nat.zero_add] using s2)
  have a3 : MorseReach 1
      ([isoU 1, isoX true 0] ++ [isoX true 0, isoX true 1] ++ (tw ++ twkSwingT (t + 3) s σ) ++
        [isoX false 1, isoN 1])
      ([isoU 1] ++ phaseTwoA1 ++ tw ++ twkSwingT (t + 3) s σ ++ [isoX false 1, isoN 1]) := by
    simpa only [phaseTwoMacroSB_lhs, phaseTwoMacroSB_rhs, phaseTwoA1, isoU, isoX,
      List.append_assoc, List.cons_append, List.nil_append] using s3
  have a4 : MorseReach 1
      ([isoU 1] ++ phaseTwoA1 ++ tw ++ twkSwingT (t + 3) s σ ++ [isoX false 1, isoN 1])
      ([isoU 1] ++ tw ++ phaseTwoA1 ++ twkSwingT (t + 3) s σ ++ [isoX false 1, isoN 1]) := by
    simpa only [List.append_assoc] using s4
  have a5 : MorseReach 1
      ([isoU 1] ++ tw ++ phaseTwoA1 ++ twkSwingT (t + 3) s σ ++ [isoX false 1, isoN 1])
      ([isoU 1] ++ tw ++ phaseTwoA1 ++ twkSTail (t + 3) s σ) := by
    simpa only [twkSTail, twkSwingT, phaseTwoMacroTC_lhs, phaseTwoMacroTC_rhs, isoU, isoX, isoN,
      isoXTip, isoCurlL, morseShiftWord, List.map_cons, List.map_nil, shiftLetter,
      List.append_assoc, List.cons_append, List.nil_append] using s5
  exact morseReach_trans a2 (morseReach_trans a3 (morseReach_trans a4 a5))

/-- Shifting a letter, with the shift written first. -/
private theorem shiftLetter_twKSwing (d : ℕ) (κ : MorseKind) (i : ℕ) :
    shiftLetter d (κ, i) = (κ, d + i) := by
  simp [shiftLetter, Nat.add_comm]

set_option linter.unusedVariables false in
/-- From the word after stage S to the doubled core with beads (the first cup and the twists are
a frame). -/
theorem morseReach_twkSQ {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) (σ : Bool) (n : ℕ) :
    MorseReach 1 ([isoU 1] ++ twTwistWord (-(2 * (n : ℤ))) ++ phaseTwoA1 ++ twkSTail r s σ)
      ([isoU 1] ++ twTwistWord (-(2 * (n : ℤ))) ++ twkQBody r s σ ++ [isoN 1]) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 3 := ⟨r - 3, by omega⟩
  rw [twTwistWord_neg_twKSwing]
  generalize htw : List.replicate (2 * n) (isoX false 0) = tw
  have ftw : ∀ N, 2 ≤ N → TwkSFits N N tw := fun N hN ↦ htw ▸ twkSFits_tw N hN _
  have fU : TwkSFits 1 3 [isoU 1] := ⟨rfl, rfl⟩
  have fA : TwkSFits 3 3 phaseTwoA1 := ⟨rfl, rfl⟩
  have f0 : TwkSFits 1 (4 * t + 11) ([isoU 1] ++ tw ++ phaseTwoA1 ++ twkSPre (t + 3) s) :=
    ((fU.append (ftw 3 (by omega))).append fA).append
      ((twkSFits_Pre t s 1).of_eq rfl (by ring))
  have fH : TwkSFits (4 * t + 11) (4 * t + 13) (twkBHopf (t + 1) (t + 3) σ) :=
    (twkSFits_Hopf t σ 1).of_eq rfl rfl
  have fX := twkSFits_Post t s 0
  have fRd : TwkSFits (4 * t + 2) 2 (twkSRd (t + 3)) := by
    rw [twkSRd, show t + 3 - 2 - 1 = t by omega]
    exact twkSFits_Rds t 0
  -- the tip moves down to the hook
  have h1 := morseReach_interchange_twKSwing 1 0 (4 * t + 9) 3 1
    ([isoU 1] ++ tw ++ phaseTwoA1 ++ twkSPre (t + 3) s ++ twkBHopf (t + 1) (t + 3) σ)
    ([isoN 2] ++ isoCurlL true 1 ++ [isoN 1]) _
    (morseShiftWord 1 (twkTw (twkTipTw σ)) ++ isoXTip) fX.1 (by cases σ <;> decide)
    (by rw [(f0.append fH).2]; ring)
  rw [fX.2] at h1
  -- hook and tip are the clasp
  have h2 := morseReach_frame 2 1 (4 * t + 8) 1
    ([isoU 1] ++ tw ++ phaseTwoA1 ++ twkSPre (t + 3) s)
    (phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3) ++
      isoBTrc (t + 1) ++ twkSRd (t + 3) ++ ([isoN 2] ++ isoCurlL true 1 ++ [isoN 1]))
    _ _ (morseReach_twkKRaw σ) (morseFits_twkKRaw σ).1 (by rw [f0.2])
  -- the outer cap of the top-right climb moves down
  have fC : TwkSFits (4 * t + 11) (4 * t + 11) (morseShiftWord (4 * t + 8) (claspSWord σ)) :=
    TwkSFits.shift (n := 2) (m := 2) ⟨by cases σ <;> decide, by cases σ <;> decide⟩ (4 * t + 8) 1
  have fcap : TwkSFits (4 * t + 7) (4 * t + 5) [isoN (4 * t + 3)] := by twks_pf_tac
  have f3 := ((((f0.append fC).append (((twkSFits_Round t 3).blk (s - 2)).of_eq rfl rfl)).append
    ((twkSFits_Last t 3).of_eq rfl rfl)).append ((twkSFits_TrcA t 3).of_eq rfl rfl)).append fcap
  have h3 := morseReach_interchange_twKSwing 1 0 (4 * t + 2) 2 1 _
    (isoCurlL true 1 ++ [isoN 1]) (twkSRd (t + 3)) [isoN 0] fRd.1 (by decide)
    (by rw [f3.2]; ring)
  rw [fRd.2] at h3
  rw [twkSTail, twkBandMid_eq_twKSwing, twkQBody]
  simp only [morseShiftWord_zero_iso, Nat.zero_add, Nat.add_zero] at h1 h3
  cases σ <;>
  · simp only [twkSPre, twkSRd, twkKRaw, twkHook, twkBHopf, isoBTrc,
      show t + 3 - 2 = t + 1 by omega, show 2 * (t + 1) + 2 * (t + 3) = 4 * t + 8 by omega,
      show 4 * (t + 1) - 2 = 4 * t + 2 by omega, show 4 * (t + 1) - 1 = 4 * t + 3 by omega,
      show 2 * (t + 3) - 5 = 2 * t + 1 by omega, show 2 * (2 * t + 1) = 4 * t + 2 by omega,
      twkTw_true_twKSwing, twkTw_false_twKSwing, morseShiftWord, List.map_cons, List.map_nil,
      shiftLetter_twKSwing, isoXTip, claspSWord, phaseTwoA1, isoCurlL, isoU, isoX, isoN,
      morseDouble, morseDoubleLetter, List.flatMap_cons, List.flatMap_nil, List.append_assoc,
      List.cons_append, List.nil_append, List.append_nil, Nat.add_assoc, Nat.reduceAdd,
      Bool.not_true, Bool.not_false]
      at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)

end AJConjecture
