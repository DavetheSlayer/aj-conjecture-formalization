import Mathlib
import AJFamily.Skein.MorseFrame
import AJFamily.Skein.TorusPhaseOneShared

/-!
# Phase I: the staircase level steps

The level steps `l = 4k-2, …, 2k+1` (`k ≥ 2`). The step of the level `l` takes
`phaseOneStair k (l+1)` to `phaseOneStair k l` (to `phaseOneX k` for `l = 2k + 1`) through the stage
words `phaseOneStairMid1`, `phaseOneStairMid2`, `phaseOneStairMid3`. The walk passes all retracted
blocks at once by `morseReach_pass`, and the dead cup passes them by `morseReach_sweep`.
-/

namespace AJConjecture

/-! ### Private helpers -/

/-- Closes the arity side goals of the local moves. -/
local macro "stair_fits" : tactic =>
  `(tactic| ((try simp only [morseRuleLhs, morseRuleRhs, morseRuleOk, morseOut_append,
    morseOut, morseLetterOut, morseFits_cons, morseFits_nil, morseKindIn,
    morseKindOut, and_true, ↓reduceIte, Bool.false_eq_true, Bool.not_false, List.nil_append,
    List.cons_append,
    List.append_nil]) <;> omega))

/-- Macro `TG` at the shift `l - 1`, by generic moves: the crossing `σ_l` commutes in front of
the walk, an `r2` pair extends the walk, the walk passes `σ_{l+1}⁻¹ σ_{l+2}⁻¹ n(l+3)`, three
crossings commute in front of the rest of the walk, a second `r2` pair extends it, and the walk
passes the cap `n(l+1)`. -/
private theorem morseReach_macroTG_stair (l : ℕ) (P v : MorseWord)
    (hP : l + 10 ≤ morseOut 1 P) :
    MorseReach 1
      (P ++ [(.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4),
        (.cross true, l + 5), (.cross true, l + 6), (.cross true, l + 7), (.cross true, l + 8),
        (.cross true, l), (.cross false, l + 1), (.cross false, l + 2), (.cap, l + 3),
        (.cross true, l), (.cross true, l - 1), (.cross false, l), (.cap, l + 1)] ++ v)
      (P ++ [(.cross true, l), (.cross false, l + 1), (.cross false, l + 2),
        (.cross false, l + 3), (.cap, l + 4), (.cross true, l + 1), (.cross true, l),
        (.cross true, l - 1), (.cross false, l), (.cross false, l + 1), (.cap, l + 2),
        (.cross true, l + 1), (.cross true, l + 2), (.cross true, l + 3),
        (.cross true, l + 4)] ++ v) := by
  generalize hN : morseOut 1 P = N at hP
  have s1 := morseReach_comm 1 P [(.cross true, l)]
    [(.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4),
      (.cross true, l + 5), (.cross true, l + 6), (.cross true, l + 7), (.cross true, l + 8)]
    ([(.cross false, l + 1), (.cross false, l + 2), (.cap, l + 3),
      (.cross true, l), (.cross true, l - 1), (.cross false, l), (.cap, l + 1)] ++ v)
    (fun b hb ↦ by
      rw [List.mem_singleton] at hb
      exact ⟨true, by rw [hb]⟩)
    (fun b hb a ha ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ha
      subst hb
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega)
    (by rw [hN]; stair_fits)
  have s2 := morseReach_rule 1 P [(.cross true, l)] []
    ([(.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4),
      (.cross true, l + 5), (.cross true, l + 6), (.cross true, l + 7), (.cross true, l + 8),
      (.cross false, l + 1), (.cross false, l + 2), (.cap, l + 3),
      (.cross true, l), (.cross true, l - 1), (.cross false, l), (.cap, l + 1)] ++ v)
    [(.cross true, l)] [(.cross true, l), (.cross false, l + 1), (.cross true, l + 1)]
    (.r2 (l + 1) false) true rfl
    (by simp only [morseOut_append, hN]; stair_fits)
    (by simp only [morseOut_append, hN]; stair_fits) rfl rfl
  have s3 := morseReach_pass 1 (l + 1) 8 true (P ++ [(.cross true, l), (.cross false, l + 1)])
    [(.cross false, 0), (.cross false, 1), (.cap, 2)]
    ([(.cross true, l), (.cross true, l - 1), (.cross false, l), (.cap, l + 1)] ++ v)
    rfl (by simp only [morseOut_append, hN]; stair_fits)
  have e3a : morseShiftWord (l + 1) [(.cross false, 0), (.cross false, 1), (.cap, 2)] =
      [(.cross false, l + 1), (.cross false, l + 2), (.cap, l + 3)] := by
    simp only [morseShiftWord, List.map_cons, List.map_nil, shiftLetter, List.cons.injEq,
      Prod.mk.injEq, true_and, and_true]
    omega
  have e3b : morseShiftWord (l + 1 + 1) [(.cross false, 0), (.cross false, 1), (.cap, 2)] =
      [(.cross false, l + 2), (.cross false, l + 3), (.cap, l + 4)] := by
    simp only [morseShiftWord, List.map_cons, List.map_nil, shiftLetter, List.cons.injEq,
      Prod.mk.injEq, true_and, and_true]
    omega
  rw [e3a, e3b, show morseOut 8 [(.cross false, 0), (.cross false, 1), (.cap, 2)] = 6 from rfl,
    show morseWalk true (l + 1) 8 = [(.cross true, l + 1), (.cross true, l + 2),
      (.cross true, l + 3), (.cross true, l + 4), (.cross true, l + 5), (.cross true, l + 6),
      (.cross true, l + 7), (.cross true, l + 8)] from rfl,
    show morseWalk true (l + 1) 6 = [(.cross true, l + 1), (.cross true, l + 2),
      (.cross true, l + 3), (.cross true, l + 4), (.cross true, l + 5), (.cross true, l + 6)]
      from rfl] at s3
  have s4 := morseReach_comm 1
    (P ++ [(.cross true, l), (.cross false, l + 1), (.cross false, l + 2),
      (.cross false, l + 3), (.cap, l + 4), (.cross true, l + 1)])
    [(.cross true, l), (.cross true, l - 1), (.cross false, l)]
    [(.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4), (.cross true, l + 5),
      (.cross true, l + 6)]
    ([(.cap, l + 1)] ++ v)
    (fun b hb ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
    (fun b hb a ha ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ha
      rcases hb with rfl | rfl | rfl <;>
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega)
    (by simp only [morseOut_append, hN]; stair_fits)
  have s5 := morseReach_rule 1
    (P ++ [(.cross true, l), (.cross false, l + 1), (.cross false, l + 2),
      (.cross false, l + 3), (.cap, l + 4), (.cross true, l + 1), (.cross true, l),
      (.cross true, l - 1), (.cross false, l)]) [] []
    ([(.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4), (.cross true, l + 5),
      (.cross true, l + 6), (.cap, l + 1)] ++ v)
    [] [(.cross false, l + 1), (.cross true, l + 1)]
    (.r2 (l + 1) false) true rfl
    (by simp only [morseOut_append, hN]; stair_fits)
    (by simp only [morseOut_append, hN]; stair_fits) rfl rfl
  have s6 := morseReach_pass 1 (l + 1) 6 true
    (P ++ [(.cross true, l), (.cross false, l + 1), (.cross false, l + 2),
      (.cross false, l + 3), (.cap, l + 4), (.cross true, l + 1), (.cross true, l),
      (.cross true, l - 1), (.cross false, l), (.cross false, l + 1)])
    [(.cap, 0)] v rfl (by simp only [morseOut_append, hN]; stair_fits)
  rw [show morseShiftWord (l + 1) [(MorseKind.cap, 0)] = [(.cap, l + 1)] by
      simp [morseShiftWord, shiftLetter],
    show morseShiftWord (l + 1 + 1) [(MorseKind.cap, 0)] = [(.cap, l + 2)] by
      simp [morseShiftWord, shiftLetter],
    show morseOut 6 [(MorseKind.cap, 0)] = 4 from rfl,
    show morseWalk true (l + 1) 6 = [(.cross true, l + 1), (.cross true, l + 2),
      (.cross true, l + 3), (.cross true, l + 4), (.cross true, l + 5), (.cross true, l + 6)]
      from rfl,
    show morseWalk true (l + 1) 4 = [(.cross true, l + 1), (.cross true, l + 2),
      (.cross true, l + 3), (.cross true, l + 4)] from rfl] at s6
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
    at s1 s2 s3 s4 s5 s6 ⊢
  exact morseReach_trans s1 <| morseReach_trans s2 <| morseReach_trans s3 <|
    morseReach_trans s4 <| morseReach_trans s5 s6

/-- Macro `TG` in the word families: the last seven walk letters pass the T-part. -/
private theorem morseReach_TG_stair (l : ℕ) (hl : 1 ≤ l) (P v : MorseWord)
    (hP : l + 10 ≤ morseOut 1 P) :
    MorseReach 1 (P ++ morseWalk true (l + 2) 7 ++ morseShiftWord (l - 1) phaseOneTp ++ v)
      (P ++ morseShiftWord (l - 1) phaseOneR4 ++ morseWalk true (l + 1) 4 ++ v) := by
  have eT : morseShiftWord (l - 1) phaseOneTp =
      [(.cross true, l), (.cross false, l + 1), (.cross false, l + 2), (.cap, l + 3),
        (.cross true, l), (.cross true, l - 1), (.cross false, l), (.cap, l + 1)] := by
    simp only [morseShiftWord, phaseOneTp, List.map_cons, List.map_nil, shiftLetter,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have eR : morseShiftWord (l - 1) phaseOneR4 =
      [(.cross true, l), (.cross false, l + 1), (.cross false, l + 2), (.cross false, l + 3),
        (.cap, l + 4), (.cross true, l + 1), (.cross true, l), (.cross true, l - 1),
        (.cross false, l), (.cross false, l + 1), (.cap, l + 2)] := by
    simp only [morseShiftWord, phaseOneR4, List.map_cons, List.map_nil, shiftLetter,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have h := morseReach_macroTG_stair l P v hP
  rw [eT, eR]
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h ⊢
  exact h

/-- Extra strands on the right pass through a word unchanged. -/
theorem morseOut_add (n e : ℕ) (w : MorseWord) (h : morseFits n w = true) :
    morseOut (n + e) w = morseOut n w + e := by
  induction w generalizing n with
  | nil => rfl
  | cons a w ih =>
    rw [morseFits_cons] at h
    simp only [morseOut]
    rw [show morseLetterOut (n + e) a = morseLetterOut n a + e by
      simp only [morseLetterOut]
      omega]
    exact ih _ h.2

/-- The arity of a shifted word with extra strands on both sides. -/
theorem morseOut_shift (n d e : ℕ) (w : MorseWord) (h : morseFits n w = true) :
    morseOut (n + d + e) (morseShiftWord d w) = morseOut n w + d + e := by
  rw [morseOut_add _ e _ (by simpa using morseFits_morseShiftWord n d 0 w h),
    morseOut_morseShiftWord n d w h]

/-- The unshifted retracted blocks `M' B'^r`. -/
private def stairBlockWord (r : ℕ) : MorseWord := stripMOne ++ (List.replicate r stripBOne).flatten

/-- The retracted blocks are the shifted unshifted blocks. -/
private theorem phaseOneStairBlocks_eq_stair (s r : ℕ) :
    phaseOneStairBlocks s r = morseShiftWord (s + 1) (stairBlockWord r) := by
  have hc : shiftLetter s ∘ shiftLetter 1 = shiftLetter (s + 1) := by
    funext x
    simp only [Function.comp, shiftLetter, Nat.add_assoc, Nat.add_comm 1 s]
  rw [phaseOneStairBlocks, stairBlockWord, ← morseShiftWord_one_stripMOne,
    ← morseShiftWord_one_stripBOne]
  simp only [morseShiftWord, List.map_append, List.map_flatten, List.map_replicate, List.map_map,
    hc]

/-- The blocks `B'^r` fit on eight strands and keep them. -/
theorem stripBOne_flatten (r : ℕ) :
    morseFits 8 (List.replicate r stripBOne).flatten = true ∧
      morseOut 8 (List.replicate r stripBOne).flatten = 8 := by
  induction r with
  | zero => exact ⟨rfl, rfl⟩
  | succ r ih =>
    rw [List.replicate_succ, List.flatten_cons, morseFits_append, morseOut_append,
      show morseOut 8 stripBOne = 8 by decide, show morseFits 8 stripBOne = true by decide, ih.1,
      ih.2]
    exact ⟨rfl, rfl⟩

/-- The unshifted blocks fit on two strands. -/
private theorem morseFits_stairBlockWord (r : ℕ) : morseFits 2 (stairBlockWord r) = true := by
  rw [stairBlockWord, morseFits_append, show morseFits 2 stripMOne = true by decide,
    show morseOut 2 stripMOne = 8 by decide, (stripBOne_flatten r).1]
  rfl

/-- The unshifted blocks end on eight strands. -/
private theorem morseOut_stairBlockWord (r : ℕ) : morseOut 2 (stairBlockWord r) = 8 := by
  rw [stairBlockWord, morseOut_append, show morseOut 2 stripMOne = 8 by decide,
    (stripBOne_flatten r).2]

/-- The arity of the retracted blocks. -/
private theorem morseOut_blocks_stair (s r n : ℕ) (h : s + 3 ≤ n) :
    morseOut n (phaseOneStairBlocks s r) = n + 6 := by
  rw [phaseOneStairBlocks_eq_stair, show n = 2 + (s + 1) + (n - s - 3) by omega,
    morseOut_shift _ _ _ _ (morseFits_stairBlockWord r), morseOut_stairBlockWord]
  omega

/-- The retracted blocks fit. -/
private theorem morseFits_blocks_stair (s r n : ℕ) (h : s + 3 ≤ n) :
    morseFits n (phaseOneStairBlocks s r) = true := by
  rw [phaseOneStairBlocks_eq_stair, show n = 2 + (s + 1) + (n - s - 3) by omega]
  exact morseFits_morseShiftWord _ _ _ _ (morseFits_stairBlockWord r)

/-- Moving the retracted blocks by `j` strands. -/
private theorem phaseOneStairBlocks_map_stair (s r j : ℕ) :
    (phaseOneStairBlocks s r).map (fun b ↦ (b.1, b.2 + j)) = phaseOneStairBlocks (s + j) r := by
  simp only [phaseOneStairBlocks, morseShiftWord, List.map_map]
  exact List.map_congr_left fun b _ ↦ by
    simp only [Function.comp, shiftLetter, Nat.add_assoc]

/-- The letters of the retracted blocks sit right of their shift. -/
private theorem le_of_mem_blocks_stair {s r : ℕ} {b : MorseLetter}
    (hb : b ∈ phaseOneStairBlocks s r) : s + 1 ≤ b.2 := by
  rw [phaseOneStairBlocks_eq_stair, morseShiftWord, List.mem_map] at hb
  obtain ⟨a, -, rfl⟩ := hb
  simp only [shiftLetter]
  omega

/-- One more retracted block `B`. -/
theorem phaseOneStairBlocks_succ (s r : ℕ) :
    phaseOneStairBlocks s (r + 1) = phaseOneStairBlocks s r ++ morseShiftWord s stripB := by
  simp only [phaseOneStairBlocks, List.replicate_succ', List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.append_assoc, morseShiftWord_append]

/-- The arity of the staircase prefix up to the blocks. -/
private theorem morseOut_stairMid_stair (k l : ℕ) (hk : 1 ≤ k) (hl : 2 * k + 1 ≤ l) :
    morseOut 1 (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l ++
      [(.cup, l + 2), (.cross true, l + 1)] ++ morseBand (2 * k - 1) (l + 1) ++
      [(.cross false, l + 1)] ++ phaseOneStairBlocks (l + 1) (4 * k - 2 - l)) = 2 * l + 9 := by
  have hH := morseOut_head_cups k l hk (by omega)
  generalize morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l = H at hH ⊢
  have h1 : morseOut 1 (H ++ [(.cup, l + 2), (.cross true, l + 1)]) = 2 * l + 3 := by
    rw [morseOut_append, hH]
    stair_fits
  rw [morseOut_append, morseOut_append, morseOut_append, h1, morseOut_band _ _ (by omega)]
  rw [show morseOut (2 * l + 3) [(.cross false, l + 1)] = 2 * l + 3 by stair_fits,
    morseOut_blocks_stair _ _ _ (by omega)]

/-- The arity of the staircase prefix `u` of a tail. -/
private theorem morseOut_stairPre_stair (k l : ℕ) (hk : 1 ≤ k) (hl : 2 * k + 1 ≤ l) :
    morseOut 1 (phaseOneStairPre k l) = 2 * l + 5 := by
  have hR : morseOut (2 * l + 9) (morseShiftWord (l - 1) phaseOneR4) = 2 * l + 5 := by
    rw [show 2 * l + 9 = 7 + (l - 1) + (l + 3) by omega,
      morseOut_shift _ _ _ _ (by decide), show morseOut 7 phaseOneR4 = 3 by decide]
    omega
  unfold phaseOneStairPre
  rw [morseOut_append, morseOut_append, morseOut_stairMid_stair k l hk hl,
    show morseOut (2 * l + 9) [(.cross true, l + 1)] = 2 * l + 9 by stair_fits, hR]

/-- The retraction of the dead cup: `phaseOne_retractHead`, then the cup sweeps through the blocks
and closes a new block `B`. -/
private theorem stairRetract_cup_stair (k l : ℕ) (hk : 1 ≤ k) (hl : 2 * k + 1 ≤ l)
    (hl' : l ≤ 4 * k - 2) (v : MorseWord) :
    MorseReach 1 (phaseOneStairPre k l ++ v)
      (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l ++ morseBand (2 * k - 1) l ++
        phaseOneStairBlocks (l - 1) (4 * k - 1 - l) ++
        [(.cross true, l - 1), (.cross false, l), (.cross false, l + 1), (.cap, l + 2)] ++ v) := by
  have eR : morseShiftWord (l - 1) phaseOneR4 =
      [(.cross true, l), (.cross false, l + 1), (.cross false, l + 2), (.cross false, l + 3),
        (.cap, l + 4), (.cross true, l + 1), (.cross true, l), (.cross true, l - 1),
        (.cross false, l), (.cross false, l + 1), (.cap, l + 2)] := by
    simp only [morseShiftWord, phaseOneR4, List.map_cons, List.map_nil, shiftLetter,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have eB : morseShiftWord (l - 1) stripB =
      [(.cup, l + 1), (.cross false, l + 1), (.cross false, l + 2), (.cross false, l + 3),
        (.cap, l + 4), (.cross true, l + 1), (.cross true, l)] := by
    simp only [morseShiftWord, stripB, List.map_cons, List.map_nil, shiftLetter,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have hblk : phaseOneStairBlocks (l - 1) (4 * k - 1 - l) =
      phaseOneStairBlocks (l - 1) (4 * k - 2 - l) ++ morseShiftWord (l - 1) stripB := by
    rw [← phaseOneStairBlocks_succ, show 4 * k - 2 - l + 1 = 4 * k - 1 - l by omega]
  have hmap := phaseOneStairBlocks_map_stair (l - 1) (4 * k - 2 - l) 2
  rw [show l - 1 + 2 = l + 1 by omega] at hmap
  have hH := morseOut_head_cups k l hk (by omega)
  have hBo := morseOut_band (2 * k - 1) l (by omega)
  have h1 := phaseOne_retractHead k l hk hl
    (phaseOneStairBlocks (l + 1) (4 * k - 2 - l) ++ [(.cross true, l + 1)] ++
      morseShiftWord (l - 1) phaseOneR4 ++ v)
  have h2 := morseReach_sweep 1 (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l ++
      morseBand (2 * k - 1) l) (phaseOneStairBlocks (l - 1) (4 * k - 2 - l))
    ([(.cross true, l + 1)] ++ morseShiftWord (l - 1) phaseOneR4 ++ v) (.cup, l)
    (fun b hb ↦ by
      have := le_of_mem_blocks_stair hb
      simp only [morseKindIn]
      omega)
    (by
      rw [morseOut_append, hH, hBo, morseFits_append, Bool.and_eq_true,
        morseOut_blocks_stair _ _ _ (by omega)]
      exact ⟨morseFits_blocks_stair _ _ _ (by omega), by stair_fits⟩)
  simp only [morseKindOut, morseKindIn, Nat.sub_zero, hmap] at h2
  have h3 := morseReach_rule 1 (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l ++
      morseBand (2 * k - 1) l ++ phaseOneStairBlocks (l - 1) (4 * k - 2 - l)) []
    [(.cross false, l + 1), (.cross false, l + 2), (.cross false, l + 3),
      (.cap, l + 4), (.cross true, l + 1), (.cross true, l), (.cross true, l - 1),
      (.cross false, l), (.cross false, l + 1), (.cap, l + 2)] v
    [(.cup, l), (.cross true, l + 1), (.cross true, l), (.cross false, l + 1),
      (.cross false, l + 2), (.cross false, l + 3),
      (.cap, l + 4), (.cross true, l + 1), (.cross true, l), (.cross true, l - 1),
      (.cross false, l), (.cross false, l + 1), (.cap, l + 2)]
    [(.cup, l + 1), (.cross false, l + 1), (.cross false, l + 2), (.cross false, l + 3),
      (.cap, l + 4), (.cross true, l + 1), (.cross true, l), (.cross true, l - 1),
      (.cross false, l), (.cross false, l + 1), (.cap, l + 2)]
    (.cupSlide l true false) false rfl
    (by
      rw [List.append_nil, morseOut_append, morseOut_append, hH, hBo,
        morseOut_blocks_stair _ _ _ (by omega)]
      stair_fits)
    (by
      rw [List.append_nil, morseOut_append, morseOut_append, hH, hBo,
        morseOut_blocks_stair _ _ _ (by omega)]
      stair_fits) rfl rfl
  unfold phaseOneStairPre
  rw [hblk, eB, eR]
  rw [eR] at h1 h2
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
  exact morseReach_trans h1 <| morseReach_trans h2 h3

/-! ### The steps -/

set_option linter.unusedVariables false in
/-- Staircase level `l`: the flip up to the T-part. -/
theorem phaseOne_stairFlipA (k l : ℕ) (hk : 2 ≤ k) (hl : 2 * k + 1 ≤ l) (hl' : l ≤ 4 * k - 2) :
    MorseReach 1 (phaseOneStair k (l + 1)) (phaseOneStairMid1 k l) := by
  have hH := morseOut_head_cups k l (by omega) (by omega)
  obtain ⟨V, hV⟩ : ∃ V : MorseWord, V = morseShiftWord (l - 1) phaseOneTp ++
      morseStairRun (2 * k) (l - 2) ++ morseBand 0 (2 * k + 1) ++ morseBand (2 * k) (l + 1) ++
      [(.cross true, l + 2)] ++ morseCapRun (l + 2) := ⟨_, rfl⟩
  have hsrc : phaseOneStair k (l + 1) = morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l ++
      [(.cup, l + 1)] ++ morseBand (2 * k - 1) (l + 1) ++
      (phaseOneStairBlocks l (4 * k - 2 - l) ++ V) := by
    rw [phaseOneStair, morseCupRun_succ (2 * k) l (by omega), show l + 1 - 1 = l by omega,
      show 4 * k - 1 - (l + 1) = 4 * k - 2 - l by omega, show l + 1 - 2 = l - 1 by omega,
      show l + 1 - 3 = l - 2 by omega, hV]
    simp only [List.append_assoc]
  have h1 := phaseOne_flipHead k l (by omega) hl (phaseOneStairBlocks l (4 * k - 2 - l) ++ V)
  rw [hsrc]
  unfold phaseOneStairMid1
  generalize morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l = H at hH h1 ⊢
  have hP : morseOut 1 (H ++ [(.cup, l + 2), (.cross true, l + 1)] ++
      morseBand (2 * k - 1) (l + 1)) = 2 * l + 3 := by
    rw [morseOut_append, morseOut_band _ _ (by omega), morseOut_append, hH]
    stair_fits
  have h2 := morseReach_rule 1 (H ++ [(.cup, l + 2), (.cross true, l + 1)] ++
      morseBand (2 * k - 1) (l + 1)) [] [(.cross true, l + 2)]
    (phaseOneStairBlocks l (4 * k - 2 - l) ++ V) [(.cross true, l + 2)]
    [(.cross false, l + 1), (.cross true, l + 1), (.cross true, l + 2)]
    (.r2 (l + 1) false) true rfl
    (by rw [List.append_nil, hP]; stair_fits) (by rw [List.append_nil, hP]; stair_fits) rfl rfl
  have h3 := morseReach_pass 1 (l + 1) 2 true (H ++ [(.cup, l + 2), (.cross true, l + 1)] ++
      morseBand (2 * k - 1) (l + 1) ++ [(.cross false, l + 1)]) (stairBlockWord (4 * k - 2 - l)) V
    (morseFits_stairBlockWord _) (by rw [morseOut_append, hP]; stair_fits)
  rw [← phaseOneStairBlocks_eq_stair, ← phaseOneStairBlocks_eq_stair,
    morseOut_stairBlockWord,
    show morseWalk true (l + 1) 2 = [(.cross true, l + 1), (.cross true, l + 2)] from rfl] at h3
  subst hV
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
  exact morseReach_trans h1 <| morseReach_trans h2 h3

set_option linter.unusedVariables false in
/-- Staircase level `l`: the rest of the flip. -/
theorem phaseOne_stairFlipB (k l : ℕ) (hk : 2 ≤ k) (hl : 2 * k + 1 ≤ l) (hl' : l ≤ 4 * k - 2) :
    MorseReach 1 (phaseOneStairMid1 k l) (phaseOneStairMid2 k l) := by
  have hP := morseOut_stairMid_stair k l (by omega) hl
  have h1 := morseReach_TG_stair l (by omega)
    (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l ++
      [(.cup, l + 2), (.cross true, l + 1)] ++ morseBand (2 * k - 1) (l + 1) ++
      [(.cross false, l + 1)] ++ phaseOneStairBlocks (l + 1) (4 * k - 2 - l) ++
      [(.cross true, l + 1)])
    (morseStairRun (2 * k) (l - 2) ++ morseBand 0 (2 * k + 1) ++ morseBand (2 * k) (l + 1) ++
      [(.cross true, l + 2)] ++ morseCapRun (l + 2))
    (by rw [morseOut_append, hP]; stair_fits)
  have h2 := phaseOne_flipTail k l (by omega) hl (phaseOneStairPre k l)
    (morseOut_stairPre_stair k l (by omega) hl)
  unfold phaseOneStairMid1 phaseOneStairMid2 phaseOneStairPre
  unfold phaseOneStairPre phaseOneTailWalk at h2
  rw [show morseWalk true (l + 1) 8 = (.cross true, l + 1) :: morseWalk true (l + 2) 7 from rfl]
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
  exact morseReach_trans h1 h2

set_option linter.unusedVariables false in
/-- Staircase level `l ≥ 2k + 2`: the retraction of the cap. -/
theorem phaseOne_stairRetractA (k l : ℕ) (hk : 2 ≤ k) (hl : 2 * k + 2 ≤ l) (hl' : l ≤ 4 * k - 2) :
    MorseReach 1 (phaseOneStairMid2 k l) (phaseOneStairMid3 k l) :=
  phaseOne_capRetract k l (by omega) hl _ (morseOut_stairPre_stair k l (by omega) (by omega))

/-- Staircase level `l ≥ 2k + 2`: the retraction of the dead cup through the blocks. -/
theorem phaseOne_stairRetractB (k l : ℕ) (hk : 2 ≤ k) (hl : 2 * k + 2 ≤ l) (hl' : l ≤ 4 * k - 2) :
    MorseReach 1 (phaseOneStairMid3 k l) (phaseOneStair k l) := by
  have h := stairRetract_cup_stair k l (by omega) (by omega) hl' (phaseOneTailRetracted k l)
  have eT : morseShiftWord (l - 2) phaseOneTp =
      [(.cross true, l - 1), (.cross false, l), (.cross false, l + 1), (.cap, l + 2),
        (.cross true, l - 1), (.cross true, l - 2), (.cross false, l - 1), (.cap, l)] := by
    simp only [morseShiftWord, phaseOneTp, List.map_cons, List.map_nil, shiftLetter,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have eB : morseBand (l - 2) l =
      [(.cross true, l - 1), (.cross true, l - 2), (.cross false, l - 1)] := by
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 2 := ⟨l - 2, by omega⟩
    simp [morseBand, morseOfBraid, surfaceBand]
  unfold phaseOneStairMid3 phaseOneTailRetracted phaseOneStair
  unfold phaseOneTailRetracted at h
  rw [eT, eB]
  rw [eB] at h
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h ⊢
  exact h

/-- Staircase level `2k + 1`: the retraction. -/
theorem phaseOne_stairRetractX (k : ℕ) (hk : 2 ≤ k) :
    MorseReach 1 (phaseOneStairMid2 k (2 * k + 1)) (phaseOneX k) := by
  have h1 := phaseOne_capRetractX k (by omega) (phaseOneStairPre k (2 * k + 1))
    (by rw [morseOut_stairPre_stair k _ (by omega) le_rfl]; omega)
  have h2 := stairRetract_cup_stair k (2 * k + 1) (by omega) le_rfl (by omega) (phaseOneTailX k)
  have eT : morseShiftWord (2 * k - 1) phaseOneTpHead =
      [(.cross true, 2 * k), (.cross false, 2 * k + 1), (.cross false, 2 * k + 2),
        (.cap, 2 * k + 3)] := by
    simp only [morseShiftWord, phaseOneTpHead, List.map_cons, List.map_nil, shiftLetter,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  rw [show 2 * k + 1 - 1 = 2 * k by omega, show 4 * k - 1 - (2 * k + 1) = 2 * k - 2 by omega]
    at h2
  unfold phaseOneStairMid2
  unfold phaseOneX
  unfold phaseOneTailX at h1 h2
  rw [eT]
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
  exact morseReach_trans h1 h2

/-- One staircase level step (composition). -/
theorem phaseOne_stairStep (k l : ℕ) (hk : 2 ≤ k) (hl : 2 * k + 2 ≤ l) (hl' : l ≤ 4 * k - 2) :
    MorseReach 1 (phaseOneStair k (l + 1)) (phaseOneStair k l) :=
  morseReach_trans (phaseOne_stairFlipA k l hk (by omega) hl')
    (morseReach_trans (phaseOne_stairFlipB k l hk (by omega) hl')
      (morseReach_trans (phaseOne_stairRetractA k l hk hl hl') (phaseOne_stairRetractB k l hk hl hl')))

/-- The staircase phase, levels `4k-2` down to `L` (induction on the number of levels). -/
theorem phaseOne_stairChain (k : ℕ) (hk : 2 ≤ k) (L : ℕ) (hL : 2 * k + 2 ≤ L)
    (hL' : L ≤ 4 * k - 1) :
    MorseReach 1 (phaseOneStair k (4 * k - 1)) (phaseOneStair k L) := by
  obtain ⟨m, rfl⟩ : ∃ m, L = 4 * k - 1 - m := ⟨4 * k - 1 - L, by omega⟩
  induction m with
  | zero => exact morseReach_refl 1 _
  | succ m ih =>
    have h2 := phaseOne_stairStep k (4 * k - 1 - (m + 1)) hk (by omega) (by omega)
    rw [show 4 * k - 1 - (m + 1) + 1 = 4 * k - 1 - m by omega] at h2
    exact morseReach_trans (ih (by omega) (by omega)) h2

/-- The staircase level `2k + 1` (composition). -/
theorem phaseOne_stairToX (k : ℕ) (hk : 2 ≤ k) :
    MorseReach 1 (phaseOneStair k (2 * k + 2)) (phaseOneX k) := by
  have h1 := phaseOne_stairFlipA k (2 * k + 1) hk le_rfl (by omega)
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega] at h1
  exact morseReach_trans h1
    (morseReach_trans (phaseOne_stairFlipB k (2 * k + 1) hk le_rfl (by omega))
      (phaseOne_stairRetractX k hk))

end AJConjecture
