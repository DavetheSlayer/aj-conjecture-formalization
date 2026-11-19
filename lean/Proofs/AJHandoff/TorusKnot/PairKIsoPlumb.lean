import Mathlib
import AJHandoff.TorusKnot.PairKIsoPlumbMacros

/-!
# Stage P: the clasp is formed

The four steps described in `PairKIsoPlumbDefs`. Steps 1 and 2 use the interchange of words on
disjoint strands (as `morseReach_interchange_curls` of the library, restated generically), macro
`CAPM` at the shift `4q - 1`; step 3 moves a one-strand curl through `r - 2` doubled crossings
(induction on `r`) and commutes the hook material; step 4 is macro `WIN` at the shift `4q` with
`morseReach_frame` (prefix on `4q + 3` strands, `e = 0`).
-/

namespace AJConjecture

/-- Shifting by zero does nothing. -/
private theorem morseShiftWord_zero_plumb (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- Interchange of two tangles side by side: `X` on the strands `d … d + a - 1` and `Y` on the `b`
strands to its right exchange their heights (exchanges, letter by letter). -/
private theorem morseReach_interchange_plumb (n₀ d a b e : ℕ) (u v X Y : MorseWord)
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
private def PlumbFits (N M : ℕ) (w : MorseWord) : Prop :=
  morseFits N w = true ∧ morseOut N w = M

/-- Arities of consecutive words compose. -/
private theorem PlumbFits.append {N M K : ℕ} {a b : MorseWord} (ha : PlumbFits N M a)
    (hb : PlumbFits M K b) : PlumbFits N K (a ++ b) := by
  refine ⟨?_, ?_⟩
  · rw [morseFits_append, ha.1, ha.2, hb.1]; rfl
  · rw [morseOut_append, ha.2, hb.2]

/-- Idle strands on the right. -/
private theorem PlumbFits.weaken {n m : ℕ} {w : MorseWord} (h : PlumbFits n m w) (e : ℕ) :
    PlumbFits (n + e) (m + e) w := by
  have := morseOut_fits_shift n 0 e w h.1
  rw [morseShiftWord_zero_plumb, Nat.zero_add, Nat.zero_add, h.2] at this
  exact ⟨this.2, this.1⟩

/-- Changing the presentation of the arities. -/
private theorem PlumbFits.of_eq {N M N' M' : ℕ} {w : MorseWord} (h : PlumbFits N M w)
    (hN : N = N') (hM : M = M') : PlumbFits N' M' w := by
  subst hN hM
  exact h

/-- A run of equal blocks. -/
private theorem PlumbFits.blk {N : ℕ} {X : MorseWord} (h : PlumbFits N N X) (k : ℕ) :
    PlumbFits N N (phaseTwoBlk X k) := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact h.append ih

/-- A doubled left walk is a word of crossings at the positions up to `2 (p + len)`. -/
private theorem mem_double_walk_plumb (p len : ℕ) :
    ∀ l ∈ morseDouble (morseWalkL true p len),
      (∃ s, l.1 = MorseKind.cross s) ∧ l.2 ≤ 2 * (p + len) := by
  intro l hl
  simp only [morseDouble, List.mem_flatMap, morseWalkL, List.mem_map, List.mem_reverse,
    List.mem_range] at hl
  obtain ⟨_, ⟨i, hi, rfl⟩, hl⟩ := hl
  simp [morseDoubleLetter, cable, cableGen, morseOfBraid, List.range_succ] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> exact ⟨⟨_, rfl⟩, by simp only; omega⟩

/-- Arity of a doubled left walk. -/
private theorem plumbFits_double_walk (p len N : ℕ) (h : 2 * (p + len) + 2 ≤ N) :
    PlumbFits N N (morseDouble (morseWalkL true p len)) :=
  ⟨morseFits_of_cross _ _ (fun l hl ↦ (mem_double_walk_plumb p len l hl).1)
    (fun l hl ↦ by have := (mem_double_walk_plumb p len l hl).2; omega),
    morseOut_of_cross _ _ (fun l hl ↦ (mem_double_walk_plumb p len l hl).1)⟩

/-- Closes arity goals of explicit words. -/
local macro "pf_tac" : tactic =>
  `(tactic| (simp only [PlumbFits, morseOut_append, morseOut, morseLetterOut, morseFits_cons,
    morseFits_nil, morseFits_append, isoX, isoU, isoN, isoCurlL, phaseTwoA1, morseShiftWord,
    List.map_cons, List.map_nil, List.map_append, shiftLetter, morseDouble, morseDoubleLetter,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
    morseKindIn, morseKindOut, Bool.and_eq_true, decide_eq_true_eq, and_true, true_and] <;>
    omega))

/-- Arity of block `LC`. -/
private theorem plumbFits_LC (k : ℕ) : PlumbFits (4 * k + 3) (4 * k + 7) (isoBLC (k + 1)) := by
  rw [isoBLC, Nat.add_sub_cancel]
  pf_tac

/-- Arity of the left climbs. -/
private theorem plumbFits_LCs (m : ℕ) :
    PlumbFits 3 (4 * m + 3) ((List.range m).flatMap fun i ↦ isoBLC (i + 1)) := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact (ih.append (plumbFits_LC m)).of_eq rfl (by ring)

/-- Arity of block `DEC`. -/
private theorem plumbFits_Dec (t : ℕ) : PlumbFits (4 * t + 7) (4 * t + 7) (isoBDec (t + 1)) := by
  rw [isoBDec, Nat.add_sub_cancel]
  pf_tac

/-- Arity of block `INC`. -/
private theorem plumbFits_Inc (t : ℕ) : PlumbFits (4 * t + 7) (4 * t + 7) (isoBInc (t + 1)) := by
  rw [isoBInc]
  pf_tac

/-- Arity of block `R0`. -/
private theorem plumbFits_R0 (t : ℕ) :
    PlumbFits (4 * t + 7) (4 * t + 11) (isoBR0 (t + 1) (t + 3)) := by
  rw [isoBR0, morseDouble, List.flatMap_append, ← morseDouble,
    show t + 1 + (t + 3) - 1 = 2 * t + 3 by omega, show t + 3 - 1 = t + 2 by omega]
  refine PlumbFits.append (M := 4 * t + 11) (PlumbFits.append (M := 4 * t + 11) ?_
    (plumbFits_double_walk _ _ _ (by omega))) ?_ <;> pf_tac

/-- Arity of the first Hopf letter. -/
private theorem plumbFits_Hopf (t : ℕ) :
    PlumbFits (4 * t + 11) (4 * t + 13) (isoBHopf (t + 1) (t + 3)) := by
  rw [isoBHopf]
  pf_tac

/-- Arity of block `ROUND`. -/
private theorem plumbFits_Round (t : ℕ) :
    PlumbFits (4 * t + 8) (4 * t + 8) (isoBRound (t + 1) (t + 3)) := by
  rw [isoBRound, show t + 3 - 1 = t + 2 by omega]
  exact (plumbFits_double_walk _ _ _ (by omega)).append (by pf_tac)

/-- Arity of block `LAST`. -/
private theorem plumbFits_Last (t : ℕ) :
    PlumbFits (4 * t + 8) (4 * t + 4) (isoBLast (t + 1) (t + 3)) := by
  rw [isoBLast, morseDouble, List.flatMap_append, ← morseDouble, Nat.add_sub_cancel,
    show t + 3 - 1 = t + 2 by omega]
  refine PlumbFits.append (M := 4 * t + 8) (by pf_tac) (PlumbFits.append (M := 4 * t + 8)
    (plumbFits_double_walk _ _ _ (by omega)) ?_)
  pf_tac

/-- Arity of block `TRC`. -/
private theorem plumbFits_Trc (t : ℕ) : PlumbFits (4 * t + 5) (4 * t + 3) (isoBTrc (t + 1)) := by
  rw [isoBTrc, show 4 * (t + 1) - 2 = 4 * t + 2 by omega, show 4 * (t + 1) - 1 = 4 * t + 3 by omega]
  pf_tac

/-- Arity of block `RD`. -/
private theorem plumbFits_Rd (k : ℕ) : PlumbFits (4 * k + 7) (4 * k + 3) (isoBRd (k + 1)) := by
  rw [isoBRd, Nat.add_sub_cancel]
  pf_tac

/-- Arity of the right descents. -/
private theorem plumbFits_Rds (m : ℕ) :
    PlumbFits (4 * m + 3) 3 ((List.range m).reverse.flatMap fun i ↦ isoBRd (i + 1)) := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.flatMap_cons]
    exact ((plumbFits_Rd m).append ih).of_eq (by ring) rfl

/-- Arity of the part below round `0`. -/
private theorem plumbFits_Pre (t s : ℕ) : PlumbFits 1 (4 * t + 7) (pairPlumbPre (t + 3) s) := by
  rw [pairPlumbPre, show t + 3 - 2 = t + 1 by omega, Nat.add_sub_cancel]
  have hA : PlumbFits 1 3 ([isoU 1] ++ phaseTwoA1) := ⟨rfl, rfl⟩
  exact (((hA.append (plumbFits_LCs t)).append
    (plumbFits_LC t)).append ((plumbFits_Dec t).blk _)).append ((plumbFits_Inc t).blk _)

/-- Arity of the words between round `0` and the last caps of the band. -/
private theorem plumbFits_Mid (t s : ℕ) :
    PlumbFits (4 * t + 9) 3 (phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++
      isoBLast (t + 1) (t + 3) ++ isoBTrc (t + 1) ++ pairPlumbRd (t + 3)) := by
  rw [pairPlumbRd, show t + 3 - 2 - 1 = t by omega]
  have := ((((plumbFits_Round t).blk (s - 2)).weaken 1).append
    ((plumbFits_Last t).weaken 1)).append ((plumbFits_Trc t).append (plumbFits_Rds t))
  simpa only [List.append_assoc] using this.of_eq (by ring) rfl

/-- Shifting a letter, with the shift written first. -/
private theorem shiftLetter_plumb (d : ℕ) (κ : MorseKind) (i : ℕ) :
    shiftLetter d (κ, i) = (κ, d + i) := by
  simp [shiftLetter, Nat.add_comm]

/-- Closes the word bookkeeping of stage P. -/
local macro "plumb_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (
    (try simp only [morseShiftWord_zero_plumb, Nat.zero_add] $[$loc]?)
    simp only [morseShiftWord, List.map_cons, List.map_nil,
    shiftLetter_plumb, isoXTip, phaseTwoA1, isoU, isoX, isoN, List.append_assoc, List.cons_append,
    List.nil_append,
    List.append_nil, Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] $[$loc]?))

/-- Step 1 (tip down), for `r = t + 3`. -/
private theorem morseReach_pairWS_WP1_aux (t s : ℕ) :
    MorseReach 1 (pairWS (t + 3) s) (pairWP1 (t + 3) s) := by
  have hP := plumbFits_Pre t s
  have hu := ((hP.append (plumbFits_R0 t)).append (plumbFits_Hopf t)).2
  have hM := plumbFits_Mid t s
  have h := morseReach_interchange_plumb 1 0 (4 * t + 9) 2 2
    (pairPlumbPre (t + 3) s ++ isoBR0 (t + 1) (t + 3) ++ isoBHopf (t + 1) (t + 3))
    [isoN 2, isoU 1, isoX true 2, isoN 1, isoN 1] _ isoXTip hM.1 (by decide) (by rw [hu]; ring)
  rw [hM.2] at h
  rw [pairWS, pairWP1, pairSwingT, pairBandMid, pairPlumbPre, pairPlumbRd, pairPlumbTail,
    show t + 3 - 2 = t + 1 by omega, Nat.add_sub_cancel] at *
  rw [show 2 * (t + 1) + 2 * (t + 3) + 1 = 0 + (4 * t + 9) by ring]
  plumb_simp at h ⊢
  exact h

/-- Closes arity goals of small shifted words. -/
local macro "out_tac" : tactic =>
  `(tactic| (simp only [morseShiftWord, List.map_cons, List.map_nil, shiftLetter, morseOut,
    morseLetterOut, isoX, isoU, isoN, morseKindOut, morseKindIn] <;> omega))

/-- Step 2 (fold curl), for `r = t + 3`. -/
private theorem morseReach_pairWP1_WP2_aux (t s : ℕ) :
    MorseReach 1 (pairWP1 (t + 3) s) (pairWP2 (t + 3) s) := by
  have fP := plumbFits_Pre t s
  have fR0 := plumbFits_R0 t
  have fRn := (plumbFits_Round t).blk (s - 2)
  have fL := plumbFits_Last t
  have fH := plumbFits_Hopf t
  have fT : PlumbFits (4 * t + 13) (4 * t + 11) (morseShiftWord (4 * t + 9) isoXTip) := by
    have := morseOut_fits_shift 2 (4 * t + 9) 2 isoXTip (by decide)
    exact ⟨this.2, this.1⟩
  have f1 := (fP.append fR0).append fH
  have f2 := f1.append fT
  have f3 := f2.append ((fRn.weaken 3).of_eq (N' := 4 * t + 11) (M' := 4 * t + 11) (by ring)
    (by ring))
  have f4 := f3.append ((fL.weaken 3).of_eq (N' := 4 * t + 11) (M' := 4 * t + 7) (by ring)
    (by ring))
  -- (a) macro `CAPM` on the curl and cap of the top-right climb
  have a := morseReach_frame 2 1 (4 * t + 3) 2
    (pairPlumbPre (t + 3) s ++ isoBR0 (t + 1) (t + 3) ++ isoBHopf (t + 1) (t + 3) ++
      morseShiftWord (4 * t + 9) isoXTip ++ phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++
      isoBLast (t + 1) (t + 3) ++ morseShiftWord (4 * t + 2) [isoX false 0, isoX false 0])
    (pairPlumbRd (t + 3) ++ pairPlumbTail) _ _ morseReach_isoCAPM
    (by decide) (by rw [morseOut_append, f4.2]; out_tac)
  -- (b) the curl passes the two crossings of the climb
  have b := morseReach_interchange_plumb 1 (4 * t + 2) 2 1 2
    (pairPlumbPre (t + 3) s ++ isoBR0 (t + 1) (t + 3) ++ isoBHopf (t + 1) (t + 3) ++
      morseShiftWord (4 * t + 9) isoXTip ++ phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++
      isoBLast (t + 1) (t + 3))
    ([isoN (4 * t + 3)] ++ pairPlumbRd (t + 3) ++ pairPlumbTail) [isoX false 0, isoX false 0]
    [isoU 1, isoX false 0, isoN 1] (by decide) (by decide) (by rw [f4.2])
  -- (c) the curl passes the last round
  have c := morseReach_interchange_plumb 1 0 (4 * t + 8) 1 2
    (pairPlumbPre (t + 3) s ++ isoBR0 (t + 1) (t + 3) ++ isoBHopf (t + 1) (t + 3) ++
      morseShiftWord (4 * t + 9) isoXTip ++ phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2))
    (morseShiftWord (4 * t + 2) [isoX false 0, isoX false 0] ++ [isoN (4 * t + 3)] ++
      pairPlumbRd (t + 3) ++ pairPlumbTail) (isoBLast (t + 1) (t + 3))
    [isoU 1, isoX false 0, isoN 1] fL.1 (by decide) (by rw [f3.2]; ring)
  -- (d) the curl passes the rounds
  have d := morseReach_interchange_plumb 1 0 (4 * t + 8) 1 2
    (pairPlumbPre (t + 3) s ++ isoBR0 (t + 1) (t + 3) ++ isoBHopf (t + 1) (t + 3) ++
      morseShiftWord (4 * t + 9) isoXTip)
    (isoBLast (t + 1) (t + 3) ++ morseShiftWord (4 * t + 2) [isoX false 0, isoX false 0] ++
      [isoN (4 * t + 3)] ++ pairPlumbRd (t + 3) ++ pairPlumbTail)
    (phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2))
    [isoU 1, isoX false 0, isoN 1] fRn.1 (by decide) (by rw [f2.2]; ring)
  -- (e) the curl passes the X tip
  have e := morseReach_symm (morseReach_interchange_plumb 1 (4 * t + 8) 1 2 2
    (pairPlumbPre (t + 3) s ++ isoBR0 (t + 1) (t + 3) ++ isoBHopf (t + 1) (t + 3))
    (phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3) ++
      morseShiftWord (4 * t + 2) [isoX false 0, isoX false 0] ++ [isoN (4 * t + 3)] ++
      pairPlumbRd (t + 3) ++ pairPlumbTail)
    [isoU 1, isoX false 0, isoN 1] isoXTip (by decide) (by decide) (by rw [f1.2]))
  -- (f) the curl enters the hook
  have f := morseReach_symm (morseReach_interchange_plumb 1 (4 * t + 8) 1 2 2
    (pairPlumbPre (t + 3) s ++ isoBR0 (t + 1) (t + 3) ++
      morseShiftWord (4 * t + 7) [isoU 3, isoX true 2, isoX false 1])
    (morseShiftWord (4 * t + 9) isoXTip ++ phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++
      isoBLast (t + 1) (t + 3) ++ morseShiftWord (4 * t + 2) [isoX false 0, isoX false 0] ++
      [isoN (4 * t + 3)] ++ pairPlumbRd (t + 3) ++ pairPlumbTail)
    [isoU 1, isoX false 0, isoN 1] [isoX false 0] (by decide) (by decide)
    (by rw [morseOut_append, (fP.append fR0).2]; out_tac))
  rw [pairWP1, pairWP2, isoBTrc, isoBHopf, isoBR0, show t + 3 - 2 = t + 1 by omega]
  rw [fL.2] at c
  rw [fRn.2] at d
  rw [show morseOut 2 [isoX false 0, isoX false 0] = 2 from rfl] at b
  rw [show morseOut 1 [isoU 1, isoX false 0, isoN 1] = 1 from rfl] at e f
  rw [isoBHopf] at a b c d e
  rw [isoBR0] at a b c d e f
  simp only [show 2 * (t + 3) - 3 = 2 * t + 3 by omega,
    show t + 1 + (t + 3) - 1 = 2 * t + 3 by omega, show t + 3 - 1 = t + 2 by omega,
    show 4 * (t + 1) - 2 = 4 * t + 2 by omega, show 4 * (t + 1) - 1 = 4 * t + 3 by omega,
    show 2 * (t + 1) + 2 * (t + 3) - 1 = 4 * t + 7 by omega,
    show 2 * (t + 1) + 2 * (t + 3) + 1 = 4 * t + 9 by omega,
    show 4 * (t + 3) - 5 = 4 * t + 7 by omega, show 4 * (t + 3) - 4 = 4 * t + 8 by omega,
    show 4 * (t + 3) - 3 = 4 * t + 9 by omega] at a b c d e f ⊢
  plumb_simp at a b c d e f ⊢
  exact morseReach_trans a (morseReach_trans b (morseReach_trans c (morseReach_trans d
    (morseReach_trans e f))))

/-- A positive curl passes a doubled positive crossing (24 moves). -/
private theorem morseReach_curlDbl_plumb :
    MorseReach 4 [isoX true 1, isoX true 2, isoX true 0, isoX true 1, isoU 1, isoX true 2, isoN 1]
      [isoU 3, isoX true 4, isoN 3, isoX true 1, isoX true 2, isoX true 0, isoX true 1] :=
  ⟨[(3, .exch (.cup, 1) (.cross true, 1), true), (4, .r2 1 false, true),
    (5, .exch (.cross true, 1) (.cross true, 3), false), (6, .capSlide 1 true true, false),
    (5, .r2 2 false, true), (6, .capSlide 2 true true, false), (6, .r2 1 false, true),
    (4, .r3 1 false, false), (3, .cupSlide 1 false false, false),
    (2, .exch (.cross true, 0) (.cup, 2), false), (1, .exch (.cup, 2) (.cross true, 2), true),
    (3, .exch (.cross true, 0) (.cross false, 2), false), (3, .r2 3 true, true),
    (7, .exch (.cross true, 1) (.cap, 3), false), (6, .exch (.cross true, 0) (.cap, 3), false),
    (4, .capSlide 2 false false, false), (1, .cupSlide 2 true true, true),
    (3, .r3 3 true, false), (5, .exch (.cap, 2) (.cross true, 4), true),
    (2, .exch (.cross true, 2) (.cross true, 4), false), (3, .capSlide 2 true true, false),
    (0, .exch (.cross true, 1) (.cup, 3), false),
    (1, .exch (.cross true, 1) (.cross true, 4), false),
    (2, .exch (.cross true, 1) (.cap, 3), false)], by decide⟩

/-- A left walk, peeled at its last letter. -/
private theorem morseWalkL_succ_plumb (s : Bool) (q k : ℕ) :
    morseWalkL s q (k + 1) = morseWalkL s (q + 1) k ++ [(MorseKind.cross s, q)] := by
  simp only [morseWalkL, List.range_succ_eq_map, List.reverse_cons, List.map_append,
    List.map_reverse, List.map_map, List.map_cons, List.map_nil, Nat.add_zero]
  congr 2
  refine List.map_congr_left fun i _ ↦ ?_
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  omega

/-- The double of a positive crossing. -/
private theorem morseDouble_cross_plumb (q : ℕ) :
    morseDouble [(MorseKind.cross true, q)] =
      morseShiftWord (2 * q) [isoX true 1, isoX true 2, isoX true 0, isoX true 1] := by
  simp [morseDouble, morseDoubleLetter, cable, cableGen, morseOfBraid, morseShiftWord,
    shiftLetter, isoX, List.range_succ]
  omega

/-- The curl of round `0` moves back through `k` doubled crossings of its walk. -/
private theorem morseReach_curl_walk_plumb (n₀ : ℕ) (k : ℕ) :
    ∀ (q : ℕ) (u v : MorseWord), 2 * (q + k) + 2 ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ morseDouble (morseWalkL true q k) ++
          morseShiftWord (2 * q) (isoCurlL true 1) ++ v)
        (u ++ morseShiftWord (2 * (q + k)) (isoCurlL true 1) ++
          morseDouble (morseWalkL true q k) ++ v) := by
  induction k with
  | zero =>
    intro q u v _
    simpa [morseWalkL, morseDouble] using morseReach_refl n₀
      (u ++ morseShiftWord (2 * q) (isoCurlL true 1) ++ v)
  | succ k ih =>
    intro q u v hu
    have hW : ∀ n, morseOut n (morseDouble (morseWalkL true (q + 1) k)) = n := fun n ↦
      morseOut_of_cross _ _ fun l hl ↦ (mem_double_walk_plumb _ _ l hl).1
    have h1 := morseReach_frame 4 n₀ (2 * q) (morseOut n₀ u - 2 * q - 4)
      (u ++ morseDouble (morseWalkL true (q + 1) k)) v _ _ morseReach_curlDbl_plumb (by decide)
      (by rw [morseOut_append, hW]; omega)
    have h2 := ih (q + 1) u
      (morseShiftWord (2 * q) [isoX true 1, isoX true 2, isoX true 0, isoX true 1] ++ v)
      (by omega)
    rw [morseWalkL_succ_plumb, morseDouble, List.flatMap_append, ← morseDouble,
      ← morseDouble, morseDouble_cross_plumb]
    rw [show 2 * (q + 1 + k) = 2 * (q + (k + 1)) by ring] at h2
    simp only [morseShiftWord, List.map_cons, List.map_nil, isoCurlL, List.append_assoc,
      List.cons_append, List.nil_append] at h1 h2 ⊢
    simp only [shiftLetter_plumb, isoU, isoX, isoN, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero,
      Nat.mul_add, Nat.mul_one] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- One more step of a left walk. -/
private theorem morseWalkL_succ_roundNF_plumb (s : Bool) (p j : ℕ) :
    morseWalkL s p (j + 1) = (MorseKind.cross s, p + j) :: morseWalkL s p j := by
  simp [morseWalkL, List.range_succ]

/-- Step 3 (curl back, hook left), for `r = t + 3`. -/
private theorem morseReach_pairWP2_WP3_aux (t s : ℕ) :
    MorseReach 1 (pairWP2 (t + 3) s) (pairWP3 (t + 3) s) := by
  have fP := plumbFits_Pre t s
  have hcups : morseOut 1 (pairPlumbPre (t + 3) s ++ [isoU (4 * t + 6), isoU (4 * t + 7)] ++
      morseShiftWord (4 * t + 4) [isoX true 1, isoX true 2, isoX true 0, isoX true 1]) =
      4 * t + 11 := by
    rw [morseOut_append, morseOut_append, fP.2]
    out_tac
  have a := morseReach_curl_walk_plumb 1 (t + 1) (t + 1)
    (pairPlumbPre (t + 3) s ++ [isoU (4 * t + 6), isoU (4 * t + 7)] ++
      morseShiftWord (4 * t + 4) [isoX true 1, isoX true 2, isoX true 0, isoX true 1])
    (morseShiftWord (4 * t + 7) [isoU 3, isoX true 2, isoX false 1] ++
      morseShiftWord (4 * t + 8) [isoU 1, isoX false 0, isoN 1] ++
      morseShiftWord (4 * t + 7) [isoX false 2] ++ morseShiftWord (4 * t + 9) isoXTip ++
      phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3) ++
      morseShiftWord (4 * t + 2) [isoX false 0, isoX false 0, isoN 1] ++ pairPlumbRd (t + 3) ++
      pairPlumbTail) (by rw [hcups]; omega)
  have hx := mem_double_walk_plumb (t + 1) (t + 1)
  have b := morseReach_symm (morseReach_comm 1
    (pairPlumbPre (t + 3) s ++ [isoU (4 * t + 6), isoU (4 * t + 7)] ++
      morseShiftWord (4 * t + 4) [isoX true 1, isoX true 2, isoX true 0, isoX true 1] ++
      morseShiftWord (2 * (t + 1 + (t + 1))) (isoCurlL true 1))
    (morseDouble (morseWalkL true (t + 1) (t + 1)))
    (morseShiftWord (4 * t + 7) [isoU 3, isoX true 2, isoX false 1] ++
      morseShiftWord (4 * t + 8) [isoU 1, isoX false 0, isoN 1] ++
      morseShiftWord (4 * t + 7) [isoX false 2] ++ morseShiftWord (4 * t + 9) isoXTip)
    (phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3) ++
      morseShiftWord (4 * t + 2) [isoX false 0, isoX false 0, isoN 1] ++ pairPlumbRd (t + 3) ++
      pairPlumbTail) (fun l hl ↦ (hx l hl).1)
    (fun l hl a ha ↦ by
      have := (hx l hl).2
      simp only [morseShiftWord, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.mem_cons, List.mem_nil_iff, or_false, shiftLetter, isoXTip, isoU, isoX, isoN] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only <;> omega)
    (by
      have hy : PlumbFits (4 * t + 11) (4 * t + 11)
          (morseShiftWord (4 * t + 7) [isoU 3, isoX true 2, isoX false 1] ++
            morseShiftWord (4 * t + 8) [isoU 1, isoX false 0, isoN 1] ++
            morseShiftWord (4 * t + 7) [isoX false 2] ++ morseShiftWord (4 * t + 9) isoXTip) := by
        simp only [isoXTip]
        pf_tac
      rw [morseOut_append, hcups]
      exact (hy.append (plumbFits_double_walk (t + 1) (t + 1) (4 * t + 11) (by omega))).1))
  rw [pairWP2, pairWP3, isoWinL, show t + 3 - 2 = t + 1 by omega,
    show 2 * (t + 3) - 3 = 2 * t + 3 by omega, show t + 3 - 1 = t + 1 + 1 by omega,
    morseWalkL_succ_roundNF_plumb, show t + 1 + (t + 1) = 2 * t + 2 by ring]
  have hD : morseDouble ([isoU (2 * t + 3)] ++
      (MorseKind.cross true, 2 * t + 2) :: morseWalkL true (t + 1) (t + 1)) =
      [isoU (4 * t + 6), isoU (4 * t + 7)] ++
        morseShiftWord (4 * t + 4) [isoX true 1, isoX true 2, isoX true 0, isoX true 1] ++
        morseDouble (morseWalkL true (t + 1) (t + 1)) := by
    rw [show [isoU (2 * t + 3)] ++ (MorseKind.cross true, 2 * t + 2) ::
        morseWalkL true (t + 1) (t + 1) = [isoU (2 * t + 3)] ++
          [(MorseKind.cross true, 2 * t + 2)] ++ morseWalkL true (t + 1) (t + 1) from rfl,
      morseDouble, List.flatMap_append, List.flatMap_append, ← morseDouble, ← morseDouble,
      ← morseDouble, morseDouble_cross_plumb, show 2 * (2 * t + 2) = 4 * t + 4 by ring]
    congr 2
    simp only [morseDouble, morseDoubleLetter, isoU, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  rw [hD, show 2 * (t + 1 + (t + 1)) = 4 * (t + 1) by ring] at *
  simp only [show 4 * (t + 3) - 5 = 4 * t + 7 by omega, show 4 * (t + 3) - 4 = 4 * t + 8 by omega,
    show 4 * (t + 3) - 3 = 4 * t + 9 by omega, show 4 * (t + 1) = 4 * t + 4 by ring,
    show 2 * (t + 1) = 2 * t + 2 by ring] at a b ⊢
  simp only [isoCurlL, phaseTwoD] at a b ⊢
  plumb_simp at a b ⊢
  exact morseReach_trans a b

/-- Step 4 (macro `WIN`), for `r = t + 3`. -/
private theorem morseReach_pairWP3_WP_aux (t s : ℕ) :
    MorseReach 1 (pairWP3 (t + 3) s) (pairWP (t + 3) s) := by
  have h := morseReach_frame 3 1 (4 * (t + 1)) 0 (pairPlumbPre (t + 3) s)
    (morseDouble (morseWalkL true (t + 1) (t + 1)) ++
      phaseTwoBlk (isoBRound (t + 1) (t + 3)) (s - 2) ++ isoBLast (t + 1) (t + 3) ++
      morseShiftWord (4 * (t + 1) - 2) [isoX false 0, isoX false 0, isoN 1] ++
      pairPlumbRd (t + 3) ++ pairPlumbTail) _ _ morseReach_isoWIN
    morseFits_isoWinL (by rw [(plumbFits_Pre t s).2]; ring)
  rw [pairWP3, pairWP, show t + 3 - 2 = t + 1 by omega]
  simpa only [List.append_assoc] using h


set_option linter.unusedVariables false in
/-- Step 1 (tip down). -/
theorem morseReach_pairWS_WP1 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWS r s) (pairWP1 r s) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 3 := ⟨r - 3, by omega⟩
  exact morseReach_pairWS_WP1_aux t s

set_option linter.unusedVariables false in
/-- Step 2 (fold curl). -/
theorem morseReach_pairWP1_WP2 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWP1 r s) (pairWP2 r s) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 3 := ⟨r - 3, by omega⟩
  exact morseReach_pairWP1_WP2_aux t s

set_option linter.unusedVariables false in
/-- Step 3 (curl back, hook left). -/
theorem morseReach_pairWP2_WP3 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWP2 r s) (pairWP3 r s) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 3 := ⟨r - 3, by omega⟩
  exact morseReach_pairWP2_WP3_aux t s

set_option linter.unusedVariables false in
/-- Step 4 (macro `WIN`). -/
theorem morseReach_pairWP3_WP {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairWP3 r s) (pairWP r s) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 3 := ⟨r - 3, by omega⟩
  exact morseReach_pairWP3_WP_aux t s

end AJConjecture
