import Mathlib
import AJFamily.Skein.TorusPhaseOneStair
import AJFamily.Skein.MorseFrame
import AJFamily.Skein.TorusPhaseOneShared
import AJFamily.Skein.TorusPhaseOneWords

/-!
# Phase I: the level `2k` and the small-climb level steps

The last `2k` level steps of phase I. The level `2k` takes `phaseOneX k` to
`phaseOneClimb k (2k)`, and each small-climb level `l ≤ 2k - 1` takes `phaseOneClimb k (l+1)` to
`phaseOneClimb k l`; finally `phaseOneClimb k 1 = stripWord k`. In each step the closing arc of the
level passes the retracted blocks at once (`morseReach_pass`) and the dead ends are retracted; the
local macros are proved here by generic moves.
-/

namespace AJConjecture

/-! ### Private helpers -/

/-- Closes the arity side goals of the local moves. -/
local macro "climb_fits" : tactic =>
  `(tactic| ((try simp only [morseRuleLhs, morseRuleRhs, morseRuleOk, morseOut_append,
    morseOut, morseLetterOut, morseFits_cons, morseFits_nil, morseKindIn,
    morseKindOut, and_true, ↓reduceIte, Bool.false_eq_true, Bool.not_false, Bool.not_true,
    List.nil_append, List.cons_append, List.append_nil]) <;> omega))

/-- The head grows at the end. -/
private theorem morseHeadRun_succ_climb (n : ℕ) :
    morseHeadRun (n + 1) =
      morseHeadRun n ++ [(MorseKind.cup, n + 1), (MorseKind.cross true, n)] := by
  simp [morseHeadRun, List.range_succ, List.flatMap_append]

/-- The unshifted blocks `A'^a M' B'^b`. -/
private def climbBlockWord (a b : ℕ) : MorseWord :=
  (List.replicate a stripAOne).flatten ++ stripMOne ++ (List.replicate b stripBOne).flatten

/-- The unshifted blocks `M' B'^b`. -/
private def stairBlockWordClimb (b : ℕ) : MorseWord := stripMOne ++ (List.replicate b stripBOne).flatten

/-- Composition of shifts of letters. -/
private theorem shiftLetter_comp_climb (s : ℕ) :
    shiftLetter s ∘ shiftLetter 1 = shiftLetter (s + 1) := by
  funext x
  simp only [Function.comp, shiftLetter, Nat.add_assoc, Nat.add_comm 1 s]

/-- The small-climb blocks are the shifted unshifted blocks. -/
private theorem phaseOneClimbBlocks_eq_climb (s a b : ℕ) :
    phaseOneClimbBlocks s a b = morseShiftWord (s + 1) (climbBlockWord a b) := by
  rw [phaseOneClimbBlocks, climbBlockWord, ← morseShiftWord_one_stripAOne,
    ← morseShiftWord_one_stripMOne, ← morseShiftWord_one_stripBOne]
  simp only [morseShiftWord, List.map_append, List.map_flatten, List.map_replicate, List.map_map,
    shiftLetter_comp_climb]

/-- The staircase blocks are the shifted unshifted blocks. -/
private theorem phaseOneStairBlocks_eq_climb (s r : ℕ) :
    phaseOneStairBlocks s r = morseShiftWord (s + 1) (stairBlockWordClimb r) := by
  rw [phaseOneStairBlocks, stairBlockWordClimb, ← morseShiftWord_one_stripMOne,
    ← morseShiftWord_one_stripBOne]
  simp only [morseShiftWord, List.map_append, List.map_flatten, List.map_replicate, List.map_map,
    shiftLetter_comp_climb]

/-- The blocks `A'^r` fit on two strands and keep them. -/
private theorem stripAOne_flatten_climb (r : ℕ) :
    morseFits 2 (List.replicate r stripAOne).flatten = true ∧
      morseOut 2 (List.replicate r stripAOne).flatten = 2 := by
  induction r with
  | zero => exact ⟨rfl, rfl⟩
  | succ r ih =>
    rw [List.replicate_succ, List.flatten_cons, morseFits_append, morseOut_append,
      show morseOut 2 stripAOne = 2 by decide, show morseFits 2 stripAOne = true by decide, ih.1,
      ih.2]
    exact ⟨rfl, rfl⟩

/-- The unshifted staircase blocks fit on two strands and end on eight. -/
private theorem stairBlockWordClimb_fits_out (r : ℕ) :
    morseFits 2 (stairBlockWordClimb r) = true ∧ morseOut 2 (stairBlockWordClimb r) = 8 := by
  rw [stairBlockWordClimb, morseFits_append, morseOut_append,
    show morseFits 2 stripMOne = true by decide, show morseOut 2 stripMOne = 8 by decide,
    (stripBOne_flatten r).1, (stripBOne_flatten r).2]
  exact ⟨rfl, rfl⟩

/-- The unshifted small-climb blocks fit on two strands and end on eight. -/
private theorem climbBlockWord_fits_out (a b : ℕ) :
    morseFits 2 (climbBlockWord a b) = true ∧ morseOut 2 (climbBlockWord a b) = 8 := by
  rw [climbBlockWord, List.append_assoc, morseFits_append, morseOut_append,
    (stripAOne_flatten_climb a).1, (stripAOne_flatten_climb a).2]
  exact stairBlockWordClimb_fits_out b

/-- The arity of the small-climb blocks. -/
private theorem morseOut_climbBlocks_climb (s a b n : ℕ) (h : s + 3 ≤ n) :
    morseOut n (phaseOneClimbBlocks s a b) = n + 6 := by
  rw [phaseOneClimbBlocks_eq_climb, show n = 2 + (s + 1) + (n - s - 3) by omega,
    morseOut_shift _ _ _ _ (climbBlockWord_fits_out a b).1,
    (climbBlockWord_fits_out a b).2]
  omega

/-- The small-climb blocks fit. -/
private theorem morseFits_climbBlocks_climb (s a b n : ℕ) (h : s + 3 ≤ n) :
    morseFits n (phaseOneClimbBlocks s a b) = true := by
  rw [phaseOneClimbBlocks_eq_climb, show n = 2 + (s + 1) + (n - s - 3) by omega]
  exact morseFits_morseShiftWord _ _ _ _ (climbBlockWord_fits_out a b).1

/-- The arity of the staircase blocks. -/
private theorem morseOut_stairBlocks_climb (s r n : ℕ) (h : s + 3 ≤ n) :
    morseOut n (phaseOneStairBlocks s r) = n + 6 := by
  rw [phaseOneStairBlocks_eq_climb, show n = 2 + (s + 1) + (n - s - 3) by omega,
    morseOut_shift _ _ _ _ (stairBlockWordClimb_fits_out r).1,
    (stairBlockWordClimb_fits_out r).2]
  omega

/-- The staircase blocks fit. -/
private theorem morseFits_stairBlocks_climb (s r n : ℕ) (h : s + 3 ≤ n) :
    morseFits n (phaseOneStairBlocks s r) = true := by
  rw [phaseOneStairBlocks_eq_climb, show n = 2 + (s + 1) + (n - s - 3) by omega]
  exact morseFits_morseShiftWord _ _ _ _ (stairBlockWordClimb_fits_out r).1

/-- The letters of the small-climb blocks sit right of their shift. -/
private theorem le_of_mem_climbBlocks_climb {s a b : ℕ} {x : MorseLetter}
    (hx : x ∈ phaseOneClimbBlocks s a b) : s + 1 ≤ x.2 := by
  rw [phaseOneClimbBlocks_eq_climb, morseShiftWord, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  simp only [shiftLetter]
  omega

/-- The letters of the staircase blocks sit right of their shift. -/
private theorem le_of_mem_stairBlocks_climb {s r : ℕ} {x : MorseLetter}
    (hx : x ∈ phaseOneStairBlocks s r) : s + 1 ≤ x.2 := by
  rw [phaseOneStairBlocks_eq_climb, morseShiftWord, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  simp only [shiftLetter]
  omega

/-- Moving the small-climb blocks two strands to the left. -/
private theorem phaseOneClimbBlocks_map_climb (s a b : ℕ) :
    (phaseOneClimbBlocks (s + 2) a b).map (fun x ↦ (x.1, x.2 + 0 - 2)) =
      phaseOneClimbBlocks s a b := by
  simp only [phaseOneClimbBlocks, morseShiftWord, List.map_map]
  exact List.map_congr_left fun x _ ↦ by
    simp only [Function.comp, shiftLetter, Prod.mk.injEq, true_and]
    omega

/-- Moving the staircase blocks two strands to the right. -/
private theorem phaseOneStairBlocks_map_climb (s r : ℕ) :
    (phaseOneStairBlocks s r).map (fun x ↦ (x.1, x.2 + 2 - 0)) = phaseOneStairBlocks (s + 2) r := by
  simp only [phaseOneStairBlocks, morseShiftWord, List.map_map]
  exact List.map_congr_left fun x _ ↦ by
    simp only [Function.comp, shiftLetter, Prod.mk.injEq, true_and]
    omega

/-- One more small-climb block `A` in front. -/
private theorem phaseOneClimbBlocks_succ_climb (s a b : ℕ) :
    phaseOneClimbBlocks s (a + 1) b = morseShiftWord s stripA ++ phaseOneClimbBlocks s a b := by
  simp only [phaseOneClimbBlocks, List.replicate_succ, List.flatten_cons, List.append_assoc,
    morseShiftWord_append]

/-- Without blocks `A`, the small-climb blocks are the staircase blocks. -/
private theorem phaseOneClimbBlocks_zero_climb (s b : ℕ) :
    phaseOneClimbBlocks s 0 b = phaseOneStairBlocks s b := by
  simp only [phaseOneClimbBlocks, phaseOneStairBlocks, List.replicate_zero, List.flatten_nil,
    List.nil_append]

/-! ### The macros, by generic moves -/

/-- Macro `SCa` at the shift `l`: the closing arc passes the last head pair. -/
private theorem morseReach_macroSCa_climb (l : ℕ) (P v : MorseWord)
    (hP : l + 2 ≤ morseOut 1 P) :
    MorseReach 1 (P ++ [(.cup, l + 1), (.cross true, l)] ++ v)
      (P ++ [(.cup, l + 2), (.cross true, l + 1), (.cross true, l), (.cross false, l + 1),
        (.cross true, l + 1), (.cross true, l + 2)] ++ v) := by
  generalize hN : morseOut 1 P = N at hP
  have s1 := morseReach_rule 1 P [] [(.cross true, l)] v [(.cup, l + 1), (.cross true, l)]
    [(.cup, l + 2), (.cross true, l + 1), (.cross true, l + 2), (.cross true, l)]
    (.cupSlide (l + 1) true true) true rfl
    (by simp only [List.append_nil, hN]; climb_fits)
    (by simp only [List.append_nil, hN]; climb_fits) rfl rfl
  have s2 := morseReach_rule 1 (P ++ [(.cup, l + 2), (.cross true, l + 1)]) [] [] v
    [(.cross true, l + 2), (.cross true, l)] [(.cross true, l), (.cross true, l + 2)]
    (.exch (.cross true, l) (.cross true, l + 2)) true
    (decide_eq_true (by dsimp only [morseKindIn]; omega))
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits)
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits) rfl rfl
  have s3 := morseReach_rule 1 (P ++ [(.cup, l + 2), (.cross true, l + 1), (.cross true, l)])
    [] [(.cross true, l + 2)] v [(.cross true, l + 2)]
    [(.cross false, l + 1), (.cross true, l + 1), (.cross true, l + 2)]
    (.r2 (l + 1) false) true rfl
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits)
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits) rfl rfl
  simp only [List.append_assoc, List.cons_append, List.nil_append] at s1 s2 s3 ⊢
  exact morseReach_trans s1 <| morseReach_trans s2 s3

/-- Macro `STa` at the shift `d`: the closing arc passes the cup `u (d+2)` and the big climb. -/
private theorem morseReach_macroSTa_climb (d : ℕ) (P v : MorseWord)
    (hP : d + 3 ≤ morseOut 1 P) :
    MorseReach 1 (P ++ [(.cup, d + 2), (.cross true, d + 1), (.cross true, d),
        (.cross false, d + 1)] ++ v)
      (P ++ [(.cup, d + 3), (.cross true, d + 2), (.cross true, d + 1), (.cross true, d),
        (.cross false, d + 1), (.cross false, d + 2), (.cross true, d + 2),
        (.cross true, d + 3)] ++ v) := by
  generalize hN : morseOut 1 P = N at hP
  have s1 := morseReach_rule 1 P [] [(.cross true, d + 1), (.cross true, d),
      (.cross false, d + 1)] v
    [(.cup, d + 2), (.cross true, d + 1), (.cross true, d), (.cross false, d + 1)]
    [(.cup, d + 3), (.cross true, d + 2), (.cross true, d + 3), (.cross true, d + 1),
      (.cross true, d), (.cross false, d + 1)]
    (.cupSlide (d + 2) true true) true rfl
    (by simp only [List.append_nil, hN]; climb_fits)
    (by simp only [List.append_nil, hN]; climb_fits) rfl rfl
  have s2 := morseReach_comm 1 (P ++ [(.cup, d + 3), (.cross true, d + 2)])
    [(.cross true, d + 1), (.cross true, d), (.cross false, d + 1)] [(.cross true, d + 3)] v
    (fun b hb ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
    (fun b hb a ha ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ha
      subst ha
      rcases hb with rfl | rfl | rfl <;> dsimp only <;> omega)
    (by simp only [morseOut_append, hN]; climb_fits)
  have s3 := morseReach_rule 1 (P ++ [(.cup, d + 3), (.cross true, d + 2),
      (.cross true, d + 1), (.cross true, d), (.cross false, d + 1)])
    [] [(.cross true, d + 3)] v [(.cross true, d + 3)]
    [(.cross false, d + 2), (.cross true, d + 2), (.cross true, d + 3)]
    (.r2 (d + 2) false) true rfl
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits)
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits) rfl rfl
  simp only [List.append_assoc, List.cons_append, List.nil_append] at s1 s2 s3 ⊢
  exact morseReach_trans s1 <| morseReach_trans s2 s3

/-- Macro `STd` at the shift `d`: the head cups of the level `2k` are retracted. -/
private theorem morseReach_macroSTd_climb (d : ℕ) (P v : MorseWord)
    (hP : d + 1 ≤ morseOut 1 P) :
    MorseReach 1 (P ++ [(.cup, d + 1), (.cup, d + 3), (.cross true, d + 2), (.cross true, d + 1),
        (.cross true, d), (.cross false, d + 1), (.cross false, d + 2)] ++ v)
      (P ++ [(.cup, d + 1), (.cross true, d), (.cup, d + 1)] ++ v) := by
  generalize hN : morseOut 1 P = N at hP
  have s1 := morseReach_rule 1 P [] [(.cross true, d + 2), (.cross true, d + 1),
      (.cross true, d), (.cross false, d + 1), (.cross false, d + 2)] v
    [(.cup, d + 1), (.cup, d + 3), (.cross true, d + 2), (.cross true, d + 1),
      (.cross true, d), (.cross false, d + 1), (.cross false, d + 2)]
    [(.cup, d + 1), (.cup, d + 1), (.cross true, d + 2), (.cross true, d + 1),
      (.cross true, d), (.cross false, d + 1), (.cross false, d + 2)]
    (.exch (.cup, d + 1) (.cup, d + 1)) false
    (decide_eq_true (by dsimp only [morseKindIn]; omega))
    (by simp only [List.append_nil, hN]; climb_fits)
    (by simp only [List.append_nil, hN]; climb_fits) rfl rfl
  have s2 := morseReach_rule 1 (P ++ [(.cup, d + 1)]) []
    [(.cross true, d), (.cross false, d + 1), (.cross false, d + 2)] v
    [(.cup, d + 1), (.cross true, d + 2), (.cross true, d + 1),
      (.cross true, d), (.cross false, d + 1), (.cross false, d + 2)]
    [(.cup, d + 2), (.cross true, d), (.cross false, d + 1), (.cross false, d + 2)]
    (.cupSlide (d + 1) true false) false rfl
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits)
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits) rfl rfl
  have s3 := morseReach_rule 1 (P ++ [(.cup, d + 1)]) []
    [(.cross false, d + 1), (.cross false, d + 2)] v
    [(.cup, d + 2), (.cross true, d), (.cross false, d + 1), (.cross false, d + 2)]
    [(.cross true, d), (.cup, d + 2), (.cross false, d + 1), (.cross false, d + 2)]
    (.exch (.cross true, d) (.cup, d + 2)) true
    (decide_eq_true (by dsimp only [morseKindIn]; omega))
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits)
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits) rfl rfl
  have s4 := morseReach_rule 1 (P ++ [(.cup, d + 1), (.cross true, d)]) [] [] v
    [(.cup, d + 2), (.cross false, d + 1), (.cross false, d + 2)] [(.cup, d + 1)]
    (.cupSlide (d + 1) false true) false rfl
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits)
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits) rfl rfl
  simp only [List.append_assoc, List.cons_append, List.nil_append] at s1 s2 s3 s4 ⊢
  exact morseReach_trans s1 <| morseReach_trans s2 <| morseReach_trans s3 s4

/-- Macro `STb` at the shift `l`, by generic moves: the crossing `σ_l` commutes in front of the
walk, an `r2` pair extends the walk, and the walk passes `σ_{l+1}⁻¹ σ_{l+2}⁻¹ n(l+3)`. -/
private theorem morseReach_macroSTb_climb (l : ℕ) (P v : MorseWord)
    (hP : l + 10 ≤ morseOut 1 P) :
    MorseReach 1
      (P ++ morseWalk true (l + 2) 7 ++ [(.cross true, l), (.cross false, l + 1),
        (.cross false, l + 2), (.cap, l + 3)] ++ v)
      (P ++ [(.cross true, l), (.cross false, l + 1), (.cross false, l + 2),
        (.cross false, l + 3), (.cap, l + 4)] ++ morseWalk true (l + 1) 6 ++ v) := by
  generalize hN : morseOut 1 P = N at hP
  have hW : morseWalk true (l + 2) 7 = [(.cross true, l + 2), (.cross true, l + 3),
      (.cross true, l + 4), (.cross true, l + 5), (.cross true, l + 6), (.cross true, l + 7),
      (.cross true, l + 8)] := rfl
  have s1 := morseReach_comm 1 P [(.cross true, l)] (morseWalk true (l + 2) 7)
    ([(.cross false, l + 1), (.cross false, l + 2), (.cap, l + 3)] ++ v)
    (fun b hb ↦ by
      rw [List.mem_singleton] at hb
      exact ⟨true, by rw [hb]⟩)
    (fun b hb a ha ↦ by
      rw [List.mem_singleton] at hb
      subst hb
      have := (mem_morseWalk ha).2.1
      dsimp only
      omega)
    (by rw [hN, hW]; climb_fits)
  have s2 := morseReach_rule 1 P [(.cross true, l)] []
    (morseWalk true (l + 2) 7 ++ [(.cross false, l + 1), (.cross false, l + 2), (.cap, l + 3)] ++
      v)
    [(.cross true, l)] [(.cross true, l), (.cross false, l + 1), (.cross true, l + 1)]
    (.r2 (l + 1) false) true rfl
    (by simp only [morseOut_append, hN]; climb_fits)
    (by simp only [morseOut_append, hN]; climb_fits) rfl rfl
  have s3 := morseReach_pass 1 (l + 1) 8 true (P ++ [(.cross true, l), (.cross false, l + 1)])
    [(.cross false, 0), (.cross false, 1), (.cap, 2)] v
    rfl (by simp only [morseOut_append, hN]; climb_fits)
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
    show morseWalk true (l + 1) 8 = (.cross true, l + 1) :: morseWalk true (l + 2) 7 from rfl]
    at s3
  simp only [List.append_assoc, List.cons_append, List.nil_append] at s1 s2 s3 ⊢
  exact morseReach_trans s1 <| morseReach_trans s2 s3

/-- Macro `STc` at the shift `l`, by generic moves: the end of the walk passes the cap `n(l+1)`,
the crossing `σ_l` and the closing caps; the last cap moves to the left. -/
private theorem morseReach_macroSTc_climb (l : ℕ) (P v : MorseWord)
    (hP : l + 8 ≤ morseOut 1 P) :
    MorseReach 1
      (P ++ morseWalk true (l + 2) 5 ++ [(.cap, l + 1), (.cross true, l), (.cross true, l + 2),
        (.cap, l + 2), (.cap, l + 1), (.cap, l)] ++ v)
      (P ++ [(.cross false, l + 1), (.cap, l + 2), (.cross true, l + 1), (.cross true, l),
        (.cross false, l + 1), (.cap, l), (.cross true, l + 1), (.cap, l + 1), (.cap, l)] ++
        v) := by
  generalize hN : morseOut 1 P = N at hP
  have s1 := morseReach_rule 1 P [] (morseWalk true (l + 2) 5 ++ [(.cap, l + 1),
      (.cross true, l), (.cross true, l + 2), (.cap, l + 2), (.cap, l + 1), (.cap, l)]) v
    (morseWalk true (l + 2) 5 ++ [(.cap, l + 1),
      (.cross true, l), (.cross true, l + 2), (.cap, l + 2), (.cap, l + 1), (.cap, l)])
    ([(.cross false, l + 1), (.cross true, l + 1)] ++ morseWalk true (l + 2) 5 ++ [(.cap, l + 1),
      (.cross true, l), (.cross true, l + 2), (.cap, l + 2), (.cap, l + 1), (.cap, l)])
    (.r2 (l + 1) false) true rfl
    (by simp only [List.append_nil, hN]; climb_fits)
    (by simp only [List.append_nil, hN]; climb_fits) rfl rfl
  have s2 := morseReach_pass 1 (l + 1) 6 true (P ++ [(.cross false, l + 1)]) [(.cap, 0)]
    ([(.cross true, l), (.cross true, l + 2), (.cap, l + 2), (.cap, l + 1), (.cap, l)] ++ v)
    rfl (by simp only [morseOut_append, hN]; climb_fits)
  rw [show morseShiftWord (l + 1) [(MorseKind.cap, 0)] = [(.cap, l + 1)] by
      simp [morseShiftWord, shiftLetter],
    show morseShiftWord (l + 1 + 1) [(MorseKind.cap, 0)] = [(.cap, l + 2)] by
      simp [morseShiftWord, shiftLetter],
    show morseOut 6 [(MorseKind.cap, 0)] = 4 from rfl,
    show morseWalk true (l + 1) 6 = (.cross true, l + 1) :: morseWalk true (l + 2) 5 from rfl,
    show morseWalk true (l + 1) 4 = [(.cross true, l + 1), (.cross true, l + 2),
      (.cross true, l + 3), (.cross true, l + 4)] from rfl] at s2
  have s3 := morseReach_comm 1 (P ++ [(.cross false, l + 1), (.cap, l + 2), (.cross true, l + 1)])
    [(.cross true, l)] [(.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4)]
    ([(.cross true, l + 2), (.cap, l + 2), (.cap, l + 1), (.cap, l)] ++ v)
    (fun b hb ↦ by
      rw [List.mem_singleton] at hb
      exact ⟨true, by rw [hb]⟩)
    (fun b hb a ha ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ha
      subst hb
      rcases ha with rfl | rfl | rfl <;> dsimp only <;> omega)
    (by simp only [morseOut_append, hN]; climb_fits)
  have s4 := morseReach_rule 1 (P ++ [(.cross false, l + 1), (.cap, l + 2),
      (.cross true, l + 1), (.cross true, l)]) [] []
    ([(.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4), (.cross true, l + 2),
      (.cap, l + 2), (.cap, l + 1), (.cap, l)] ++ v)
    [] [(.cross false, l + 1), (.cross true, l + 1)]
    (.r2 (l + 1) false) true rfl
    (by simp only [morseOut_append, hN]; climb_fits)
    (by simp only [morseOut_append, hN]; climb_fits) rfl rfl
  have s5 := morseReach_pass 1 (l + 1) 4 true (P ++ [(.cross false, l + 1), (.cap, l + 2),
      (.cross true, l + 1), (.cross true, l), (.cross false, l + 1)])
    [(.cross true, 1), (.cap, 1), (.cap, 0)] ([(.cap, l)] ++ v)
    rfl (by simp only [morseOut_append, hN]; climb_fits)
  have e5a : morseShiftWord (l + 1) [(.cross true, 1), (.cap, 1), (.cap, 0)] =
      [(.cross true, l + 2), (.cap, l + 2), (.cap, l + 1)] := by
    simp only [morseShiftWord, List.map_cons, List.map_nil, shiftLetter, List.cons.injEq,
      Prod.mk.injEq, true_and, and_true]
    omega
  have e5b : morseShiftWord (l + 1 + 1) [(.cross true, 1), (.cap, 1), (.cap, 0)] =
      [(.cross true, l + 3), (.cap, l + 3), (.cap, l + 2)] := by
    simp only [morseShiftWord, List.map_cons, List.map_nil, shiftLetter, List.cons.injEq,
      Prod.mk.injEq, true_and, and_true]
    omega
  rw [e5a, e5b, show morseOut 4 [(.cross true, 1), (.cap, 1), (.cap, 0)] = 0 from rfl,
    show morseWalk true (l + 1) 4 = [(.cross true, l + 1), (.cross true, l + 2),
      (.cross true, l + 3), (.cross true, l + 4)] from rfl,
    show morseWalk true (l + 1) 0 = [] from rfl] at s5
  have s6 := morseReach_symm <| morseReach_sweep 1 (P ++ [(.cross false, l + 1), (.cap, l + 2),
      (.cross true, l + 1), (.cross true, l), (.cross false, l + 1)])
    [(.cross true, l + 3), (.cap, l + 3), (.cap, l + 2)] v (.cap, l)
    (fun b hb ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> dsimp only [morseKindIn] <;> omega)
    (by simp only [morseOut_append, hN]; climb_fits)
  have e6 : List.map (fun b : MorseLetter ↦ (b.1, b.2 + morseKindOut (MorseKind.cap, l).1 -
      morseKindIn (MorseKind.cap, l).1)) [(.cross true, l + 3), (.cap, l + 3), (.cap, l + 2)] =
      [(.cross true, l + 1), (.cap, l + 1), (.cap, l)] := by
    simp only [List.map_cons, List.map_nil, morseKindOut, morseKindIn, List.cons.injEq,
      Prod.mk.injEq, true_and, and_true]
    omega
  rw [e6] at s6
  rw [show morseWalk true (l + 2) 5 = [(.cross true, l + 2), (.cross true, l + 3),
      (.cross true, l + 4), (.cross true, l + 5), (.cross true, l + 6)] from rfl] at s1 s2 ⊢
  simp only [List.append_assoc, List.cons_append, List.nil_append]
    at s1 s2 s3 s4 s5 s6 ⊢
  exact morseReach_trans s1 <| morseReach_trans s2 <| morseReach_trans s3 <|
    morseReach_trans s4 <| morseReach_trans s5 s6

/-- The tangle passed by the walk in macro `SCb` (unshifted). -/
private def scbTangle : MorseWord :=
  [(.cross false, 0), (.cross false, 1), (.cap, 2), (.cross true, 1), (.cross true, 0),
    (.cross false, 1), (.cap, 0), (.cross true, 1), (.cap, 1), (.cap, 0)]

/-- The tangle of macro `SCb`, shifted. -/
private theorem morseShiftWord_scbTangle (d : ℕ) :
    morseShiftWord d scbTangle =
      [(.cross false, d), (.cross false, d + 1), (.cap, d + 2), (.cross true, d + 1),
        (.cross true, d), (.cross false, d + 1), (.cap, d), (.cross true, d + 1),
        (.cap, d + 1), (.cap, d)] := by
  simp only [morseShiftWord, scbTangle, List.map_cons, List.map_nil, shiftLetter,
    List.cons.injEq, Prod.mk.injEq, true_and, and_true]
  omega

/-- Macro `SCb` at the shift `l`, by generic moves: an `r2` pair extends the walk, the walk passes
the rest of the tail and the closing caps, the last cap moves to the left and slides. -/
private theorem morseReach_macroSCb_climb (l : ℕ) (P v : MorseWord)
    (hP : l + 10 ≤ morseOut 1 P) :
    MorseReach 1
      (P ++ [(.cross false, l)] ++ morseWalk true (l + 2) 7 ++ morseShiftWord (l + 1) scbTangle ++
        [(.cap, l)] ++ v)
      (P ++ [(.cap, l + 1)] ++ morseShiftWord l scbTangle ++ v) := by
  generalize hN : morseOut 1 P = N at hP
  have s1 := morseReach_rule 1 (P ++ [(.cross false, l)]) []
    (morseWalk true (l + 2) 7 ++ morseShiftWord (l + 1) scbTangle ++ [(.cap, l)]) v
    (morseWalk true (l + 2) 7 ++ morseShiftWord (l + 1) scbTangle ++ [(.cap, l)])
    ([(.cross false, l + 1), (.cross true, l + 1)] ++ morseWalk true (l + 2) 7 ++
      morseShiftWord (l + 1) scbTangle ++ [(.cap, l)])
    (.r2 (l + 1) false) true rfl
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits)
    (by simp only [List.append_nil, morseOut_append, hN]; climb_fits) rfl rfl
  have s2 := morseReach_pass 1 (l + 1) 8 true (P ++ [(.cross false, l), (.cross false, l + 1)])
    scbTangle ([(.cap, l)] ++ v) (by decide) (by simp only [morseOut_append, hN]; climb_fits)
  rw [show morseOut 8 scbTangle = 0 by decide, show morseWalk true (l + 1) 0 = [] from rfl,
    show morseWalk true (l + 1) 8 = (.cross true, l + 1) :: morseWalk true (l + 2) 7 from rfl]
    at s2
  have s3 := morseReach_symm <| morseReach_sweep 1 (P ++ [(.cross false, l), (.cross false, l + 1)])
    (morseShiftWord (l + 2) scbTangle) v (.cap, l)
    (fun b hb ↦ by
      rw [morseShiftWord_scbTangle] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only [morseKindIn] <;> omega)
    (by rw [morseShiftWord_scbTangle]; simp only [morseOut_append, hN]; climb_fits)
  have e3 : List.map (fun b : MorseLetter ↦ (b.1, b.2 + morseKindOut (MorseKind.cap, l).1 -
      morseKindIn (MorseKind.cap, l).1)) (morseShiftWord (l + 2) scbTangle) =
      morseShiftWord l scbTangle := by
    rw [morseShiftWord_scbTangle, morseShiftWord_scbTangle]
    simp only [List.map_cons, List.map_nil, morseKindOut, morseKindIn, List.cons.injEq,
      Prod.mk.injEq, true_and, and_true]
    omega
  rw [e3] at s3
  have s4 := morseReach_rule 1 P [] (morseShiftWord l scbTangle) v
    ([(.cross false, l), (.cross false, l + 1), (.cap, l)] ++ morseShiftWord l scbTangle)
    ([(.cap, l + 1)] ++ morseShiftWord l scbTangle)
    (.capSlide l false true) false rfl
    (by simp only [List.append_nil, hN]; climb_fits)
    (by simp only [List.append_nil, hN]; climb_fits) rfl rfl
  simp only [List.append_assoc, List.cons_append, List.nil_append] at s1 s2 s3 s4 ⊢
  exact morseReach_trans s1 <| morseReach_trans s2 <| morseReach_trans s3 s4

/-! ### The steps -/

/-- Level `2k`: the flip. -/
theorem phaseOne_stepT_flip (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1 (phaseOneX k) (phaseOneTMid k) := by
  have hH : morseOut 1 (morseHeadRun (2 * k - 1)) = 4 * k - 1 := by
    rw [morseOut_morseHeadRun 1 _ le_rfl]
    omega
  have hcups : morseCupRun (2 * k) (2 * k + 1) = [(.cup, 2 * k), (.cup, 2 * k + 1)] := by
    rw [morseCupRun, show 2 * k + 1 + 1 - 2 * k = 2 by omega]
    simp [List.range_succ]
  have hband : morseBand (2 * k - 1) (2 * k + 1) =
      [(.cross true, 2 * k), (.cross true, 2 * k - 1), (.cross false, 2 * k)] := by
    obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 1 := ⟨2 * k - 1, by omega⟩
    rw [hm, show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by omega]
    simp [morseBand, morseOfBraid, surfaceBand]
  have hband1 : morseBand (2 * k) (2 * k + 1) = [(.cross true, 2 * k)] := by
    simp [morseBand, morseOfBraid, surfaceBand]
  have hTp : morseShiftWord (2 * k - 1) phaseOneTpHead =
      [(.cross true, 2 * k), (.cross false, 2 * k + 1), (.cross false, 2 * k + 2),
        (.cap, 2 * k + 3)] := by
    simp only [morseShiftWord, phaseOneTpHead, List.map_cons, List.map_nil, shiftLetter,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have hRT : morseShiftWord (2 * k) phaseOneRT =
      [(.cross true, 2 * k), (.cross false, 2 * k + 1), (.cross false, 2 * k + 2),
        (.cross false, 2 * k + 3), (.cap, 2 * k + 4)] := by
    simp only [morseShiftWord, phaseOneRT, List.map_cons, List.map_nil, shiftLetter,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  obtain ⟨H, hHd⟩ : ∃ H : MorseWord, H = morseHeadRun (2 * k - 1) := ⟨_, rfl⟩
  rw [← hHd] at hH
  obtain ⟨Z, hZ⟩ : ∃ Z : MorseWord, Z = [(.cap, 2 * k + 1), (.cross true, 2 * k),
      (.cross true, 2 * k + 2)] ++ morseCapRun (2 * k + 2) := ⟨_, rfl⟩
  have h1 := morseReach_macroSTa_climb (2 * k - 1) (H ++ [(.cup, 2 * k)])
    (phaseOneStairBlocks (2 * k) (2 * k - 2) ++ [(.cross true, 2 * k), (.cross false, 2 * k + 1),
      (.cross false, 2 * k + 2), (.cap, 2 * k + 3)] ++ morseBand 0 (2 * k + 1) ++ Z)
    (by simp only [morseOut_append, hH]; climb_fits)
  rw [show 2 * k - 1 + 1 = 2 * k by omega, show 2 * k - 1 + 2 = 2 * k + 1 by omega,
    show 2 * k - 1 + 3 = 2 * k + 2 by omega] at h1
  obtain ⟨U, hU⟩ : ∃ U : MorseWord, U = H ++ [(.cup, 2 * k), (.cup, 2 * k + 2),
      (.cross true, 2 * k + 1), (.cross true, 2 * k), (.cross true, 2 * k - 1),
      (.cross false, 2 * k), (.cross false, 2 * k + 1)] := ⟨_, rfl⟩
  have hUo : morseOut 1 U = 4 * k + 3 := by
    rw [hU, morseOut_append, hH]
    climb_fits
  have h2 := morseReach_pass 1 (2 * k + 1) 2 true U (stairBlockWordClimb (2 * k - 2))
    ([(.cross true, 2 * k), (.cross false, 2 * k + 1), (.cross false, 2 * k + 2),
      (.cap, 2 * k + 3)] ++ morseBand 0 (2 * k + 1) ++ Z)
    (stairBlockWordClimb_fits_out _).1 (by rw [hUo]; omega)
  rw [← phaseOneStairBlocks_eq_climb, ← phaseOneStairBlocks_eq_climb,
    (stairBlockWordClimb_fits_out _).2,
    show morseWalk true (2 * k + 1) 2 = [(.cross true, 2 * k + 1), (.cross true, 2 * k + 2)]
      from rfl,
    show morseWalk true (2 * k + 1) 8 = (.cross true, 2 * k + 1) :: morseWalk true (2 * k + 2) 7
      from rfl] at h2
  have hP3 : morseOut 1 (U ++ phaseOneStairBlocks (2 * k + 1) (2 * k - 2) ++
      [(.cross true, 2 * k + 1)]) = 4 * k + 9 := by
    rw [morseOut_append, morseOut_append, hUo, morseOut_stairBlocks_climb _ _ _ (by omega)]
    climb_fits
  have h3 := morseReach_macroSTb_climb (2 * k) (U ++ phaseOneStairBlocks (2 * k + 1) (2 * k - 2) ++
      [(.cross true, 2 * k + 1)]) (morseBand 0 (2 * k + 1) ++ Z) (by rw [hP3]; omega)
  rw [show morseWalk true (2 * k + 1) 6 = (.cross true, 2 * k + 1) :: morseWalk true (2 * k + 2) 5
      from rfl] at h3
  have h4 := morseReach_comm 1 (U ++ phaseOneStairBlocks (2 * k + 1) (2 * k - 2) ++
      [(.cross true, 2 * k + 1)] ++ [(.cross true, 2 * k), (.cross false, 2 * k + 1),
        (.cross false, 2 * k + 2), (.cross false, 2 * k + 3), (.cap, 2 * k + 4)] ++
      [(.cross true, 2 * k + 1)])
    (morseBand 0 (2 * k + 1)) (morseWalk true (2 * k + 2) 5) Z
    (fun b hb ↦ (mem_morseBand (by omega) hb).1)
    (fun b hb a ha ↦ by
      have := (mem_morseBand (by omega) hb).2.2
      have := (mem_morseWalk ha).2.1
      omega)
    (by
      rw [morseOut_append, morseOut_append, hP3]
      refine morseFits_of_cross _ _ (fun b hb ↦ ?_) (fun b hb ↦ ?_)
      · rcases List.mem_append.mp hb with h | h
        · exact ⟨true, (mem_morseWalk h).1⟩
        · exact (mem_morseBand (by omega) h).1
      · simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut]
        rcases List.mem_append.mp hb with h | h
        · have := (mem_morseWalk h).2.2
          omega
        · have := (mem_morseBand (by omega) h).2.2
          omega)
  unfold phaseOneX phaseOneTMid
  rw [hcups, hband, hband1, hTp, hRT, ← hHd]
  subst hU hZ
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 ⊢
  exact morseReach_trans h1 <| morseReach_trans h2 <| morseReach_trans h3 h4

/-- Level `2k`: the end of the flip and the retraction. -/
theorem phaseOne_stepT_retract (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1 (phaseOneTMid k) (phaseOneClimb k (2 * k)) := by
  have hH : morseOut 1 (morseHeadRun (2 * k - 1)) = 4 * k - 1 := by
    rw [morseOut_morseHeadRun 1 _ le_rfl]
    omega
  have hcaps : morseCapRun (2 * k + 1) =
      (.cap, 2 * k + 1) :: (.cap, 2 * k) :: morseCapRun (2 * k - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 1 := ⟨2 * k - 1, by omega⟩
    rw [hm, morseCapRun_succ, morseCapRun_succ, Nat.add_sub_cancel]
  have hRT : morseShiftWord (2 * k) phaseOneRT =
      [(.cross true, 2 * k), (.cross false, 2 * k + 1), (.cross false, 2 * k + 2),
        (.cross false, 2 * k + 3), (.cap, 2 * k + 4)] := by
    simp only [morseShiftWord, phaseOneRT, List.map_cons, List.map_nil, shiftLetter,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have hTq : morseShiftWord (2 * k - 1) phaseOneTq =
      [(.cap, 2 * k + 2), (.cross true, 2 * k + 1), (.cross true, 2 * k),
        (.cross false, 2 * k + 1), (.cap, 2 * k), (.cross true, 2 * k + 1)] := by
    simp only [morseShiftWord, phaseOneTq, List.map_cons, List.map_nil, shiftLetter,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have hB : morseShiftWord (2 * k - 1) stripB =
      [(.cup, 2 * k + 1), (.cross false, 2 * k + 1), (.cross false, 2 * k + 2),
        (.cross false, 2 * k + 3), (.cap, 2 * k + 4), (.cross true, 2 * k + 1),
        (.cross true, 2 * k)] := by
    simp only [morseShiftWord, stripB, List.map_cons, List.map_nil, shiftLetter,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have hblk : phaseOneClimbBlocks (2 * k - 1) (2 * k - 2 * k) (2 * k - 1) =
      phaseOneStairBlocks (2 * k - 1) (2 * k - 2) ++ morseShiftWord (2 * k - 1) stripB := by
    rw [Nat.sub_self, phaseOneClimbBlocks_zero_climb, ← phaseOneStairBlocks_succ,
      show 2 * k - 2 + 1 = 2 * k - 1 by omega]
  have hhead : morseHeadRun (2 * k) =
      morseHeadRun (2 * k - 1) ++ [(.cup, 2 * k), (.cross true, 2 * k - 1)] := by
    have := morseHeadRun_succ_climb (2 * k - 1)
    rwa [show 2 * k - 1 + 1 = 2 * k by omega] at this
  have hmap := phaseOneStairBlocks_map_climb (2 * k - 1) (2 * k - 2)
  rw [show 2 * k - 1 + 2 = 2 * k + 1 by omega] at hmap
  obtain ⟨H, hHd⟩ : ∃ H : MorseWord, H = morseHeadRun (2 * k - 1) := ⟨_, rfl⟩
  rw [← hHd] at hH hhead
  obtain ⟨Y, hY⟩ : ∃ Y : MorseWord, Y = [(.cross true, 2 * k + 1), (.cross true, 2 * k),
      (.cross false, 2 * k + 1), (.cross false, 2 * k + 2), (.cross false, 2 * k + 3),
      (.cap, 2 * k + 4), (.cross true, 2 * k + 1)] := ⟨_, rfl⟩
  have hU3 : morseOut 1 (H ++ [(.cup, 2 * k), (.cup, 2 * k + 2), (.cross true, 2 * k + 1),
      (.cross true, 2 * k), (.cross true, 2 * k - 1), (.cross false, 2 * k),
      (.cross false, 2 * k + 1)] ++ phaseOneStairBlocks (2 * k + 1) (2 * k - 2) ++ Y ++
      morseBand 0 (2 * k + 1)) = 4 * k + 7 := by
    have h0 : morseOut 1 (H ++ [(.cup, 2 * k), (.cup, 2 * k + 2), (.cross true, 2 * k + 1),
        (.cross true, 2 * k), (.cross true, 2 * k - 1), (.cross false, 2 * k),
        (.cross false, 2 * k + 1)]) = 4 * k + 3 := by
      rw [morseOut_append, hH]
      climb_fits
    rw [morseOut_append, morseOut_append, morseOut_append, h0,
      morseOut_stairBlocks_climb _ _ _ (by omega), morseOut_band _ _ (by omega), hY]
    climb_fits
  have h1 := morseReach_macroSTc_climb (2 * k) (H ++ [(.cup, 2 * k), (.cup, 2 * k + 2),
      (.cross true, 2 * k + 1), (.cross true, 2 * k), (.cross true, 2 * k - 1),
      (.cross false, 2 * k), (.cross false, 2 * k + 1)] ++
      phaseOneStairBlocks (2 * k + 1) (2 * k - 2) ++ Y ++ morseBand 0 (2 * k + 1))
    (morseCapRun (2 * k - 1)) (by rw [hU3]; omega)
  have h2 := morseReach_macroSTd_climb (2 * k - 1) H
    (phaseOneStairBlocks (2 * k + 1) (2 * k - 2) ++ Y ++ morseBand 0 (2 * k + 1) ++
      [(.cross false, 2 * k + 1), (.cap, 2 * k + 2), (.cross true, 2 * k + 1),
        (.cross true, 2 * k), (.cross false, 2 * k + 1), (.cap, 2 * k),
        (.cross true, 2 * k + 1), (.cap, 2 * k + 1), (.cap, 2 * k)] ++
      morseCapRun (2 * k - 1)) (by rw [hH]; omega)
  rw [show 2 * k - 1 + 1 = 2 * k by omega, show 2 * k - 1 + 2 = 2 * k + 1 by omega,
    show 2 * k - 1 + 3 = 2 * k + 2 by omega] at h2
  have hH2 : morseOut 1 (H ++ [(.cup, 2 * k), (.cross true, 2 * k - 1)]) = 4 * k + 1 := by
    rw [morseOut_append, hH]
    climb_fits
  have h3 := morseReach_sweep 1 (H ++ [(.cup, 2 * k), (.cross true, 2 * k - 1)])
    (phaseOneStairBlocks (2 * k - 1) (2 * k - 2))
    (Y ++ morseBand 0 (2 * k + 1) ++
      [(.cross false, 2 * k + 1), (.cap, 2 * k + 2), (.cross true, 2 * k + 1),
        (.cross true, 2 * k), (.cross false, 2 * k + 1), (.cap, 2 * k),
        (.cross true, 2 * k + 1), (.cap, 2 * k + 1), (.cap, 2 * k)] ++
      morseCapRun (2 * k - 1)) (.cup, 2 * k)
    (fun b hb ↦ by
      have := le_of_mem_stairBlocks_climb hb
      simp only [morseKindIn]
      omega)
    (by
      rw [hH2, morseFits_append, Bool.and_eq_true, morseOut_stairBlocks_climb _ _ _ (by omega)]
      exact ⟨morseFits_stairBlocks_climb _ _ _ (by omega), by climb_fits⟩)
  simp only [morseKindOut, morseKindIn, hmap] at h3
  have h4 := morseReach_rule 1 (H ++ [(.cup, 2 * k), (.cross true, 2 * k - 1)] ++
      phaseOneStairBlocks (2 * k - 1) (2 * k - 2)) []
    [(.cross false, 2 * k + 1), (.cross false, 2 * k + 2), (.cross false, 2 * k + 3),
      (.cap, 2 * k + 4), (.cross true, 2 * k + 1), (.cross true, 2 * k)]
    (morseBand 0 (2 * k) ++ [(.cross false, 2 * k)] ++
      [(.cross false, 2 * k + 1), (.cap, 2 * k + 2), (.cross true, 2 * k + 1),
        (.cross true, 2 * k), (.cross false, 2 * k + 1), (.cap, 2 * k),
        (.cross true, 2 * k + 1), (.cap, 2 * k + 1), (.cap, 2 * k)] ++
      morseCapRun (2 * k - 1))
    [(.cup, 2 * k), (.cross true, 2 * k + 1), (.cross true, 2 * k), (.cross false, 2 * k + 1),
      (.cross false, 2 * k + 2), (.cross false, 2 * k + 3),
      (.cap, 2 * k + 4), (.cross true, 2 * k + 1), (.cross true, 2 * k)]
    [(.cup, 2 * k + 1), (.cross false, 2 * k + 1), (.cross false, 2 * k + 2),
      (.cross false, 2 * k + 3), (.cap, 2 * k + 4), (.cross true, 2 * k + 1),
      (.cross true, 2 * k)]
    (.cupSlide (2 * k) true false) false rfl
    (by
      rw [List.append_nil, morseOut_append, hH2, morseOut_stairBlocks_climb _ _ _ (by omega)]
      climb_fits)
    (by
      rw [List.append_nil, morseOut_append, hH2, morseOut_stairBlocks_climb _ _ _ (by omega)]
      climb_fits) rfl rfl
  unfold phaseOneTMid phaseOneClimb
  rw [hRT, hTq, hblk, hB, hhead, ← hHd, morseCapRun_succ (2 * k + 1), hcaps]
  rw [morseBand_succ 0 (2 * k) (by omega)] at h1 h2 h3
  rw [morseBand_succ 0 (2 * k) (by omega)]
  subst hY
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 ⊢
  exact morseReach_trans h1 <| morseReach_trans h2 <| morseReach_trans h3 h4

set_option linter.unusedVariables false in
/-- Small-climb level `l`: the flip. -/
theorem phaseOne_climbFlip (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hl' : l ≤ 2 * k - 1) :
    MorseReach 1 (phaseOneClimb k (l + 1)) (phaseOneClimbMid k l) := by
  have hH : morseOut 1 (morseHeadRun l) = 2 * l + 1 := by
    rw [morseOut_morseHeadRun 1 _ le_rfl]
    omega
  obtain ⟨V, hV⟩ : ∃ V : MorseWord, V = morseBand 0 (l + 1) ++
      [(.cross false, l + 1), (.cross false, l + 2)] ++ morseShiftWord l phaseOneTq ++
      morseCapRun (l + 2) := ⟨_, rfl⟩
  have hsrc : phaseOneClimb k (l + 1) = morseHeadRun l ++ [(.cup, l + 1), (.cross true, l)] ++
      (phaseOneClimbBlocks l (2 * k - l - 1) (2 * k - 1) ++ V) := by
    rw [phaseOneClimb, morseHeadRun_succ_climb, show l + 1 - 1 = l by omega,
      show 2 * k - (l + 1) = 2 * k - l - 1 by omega, hV]
    simp only [List.append_assoc]
  have h1 := morseReach_macroSCa_climb l (morseHeadRun l)
    (phaseOneClimbBlocks l (2 * k - l - 1) (2 * k - 1) ++ V) (by rw [hH]; omega)
  have hu : morseOut 1 (morseHeadRun l ++ [(.cup, l + 2), (.cross true, l + 1), (.cross true, l),
      (.cross false, l + 1)]) = 2 * l + 3 := by
    rw [morseOut_append, hH]
    climb_fits
  have h2 := morseReach_pass 1 (l + 1) 2 true (morseHeadRun l ++ [(.cup, l + 2),
      (.cross true, l + 1), (.cross true, l), (.cross false, l + 1)])
    (climbBlockWord (2 * k - l - 1) (2 * k - 1)) V (climbBlockWord_fits_out _ _).1
    (by rw [hu]; omega)
  rw [← phaseOneClimbBlocks_eq_climb, ← phaseOneClimbBlocks_eq_climb,
    (climbBlockWord_fits_out _ _).2,
    show morseWalk true (l + 1) 2 = [(.cross true, l + 1), (.cross true, l + 2)] from rfl,
    show morseWalk true (l + 1) 8 = (.cross true, l + 1) :: morseWalk true (l + 2) 7 from rfl]
    at h2
  have hu' : morseOut 1 (morseHeadRun l ++ [(.cup, l + 2), (.cross true, l + 1), (.cross true, l),
      (.cross false, l + 1)] ++ phaseOneClimbBlocks (l + 1) (2 * k - l - 1) (2 * k - 1) ++
      [(.cross true, l + 1)]) = 2 * l + 9 := by
    rw [morseOut_append, morseOut_append, hu, morseOut_climbBlocks_climb _ _ _ _ (by omega)]
    climb_fits
  have h3 := morseReach_comm 1 (morseHeadRun l ++ [(.cup, l + 2), (.cross true, l + 1),
      (.cross true, l), (.cross false, l + 1)] ++
      phaseOneClimbBlocks (l + 1) (2 * k - l - 1) (2 * k - 1) ++ [(.cross true, l + 1)])
    (morseBand 0 (l + 1)) (morseWalk true (l + 2) 7)
    ([(.cross false, l + 1), (.cross false, l + 2)] ++ morseShiftWord l phaseOneTq ++
      morseCapRun (l + 2))
    (fun b hb ↦ (mem_morseBand (by omega) hb).1)
    (fun b hb a ha ↦ by
      have := (mem_morseBand (by omega) hb).2.2
      have := (mem_morseWalk ha).2.1
      omega)
    (by
      rw [hu']
      refine morseFits_of_cross _ _ (fun b hb ↦ ?_) (fun b hb ↦ ?_)
      · rcases List.mem_append.mp hb with h | h
        · exact ⟨true, (mem_morseWalk h).1⟩
        · exact (mem_morseBand (by omega) h).1
      · rcases List.mem_append.mp hb with h | h
        · have := (mem_morseWalk h).2.2
          omega
        · have := (mem_morseBand (by omega) h).2.2
          omega)
  rw [hsrc]
  unfold phaseOneClimbMid
  subst hV
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
  exact morseReach_trans h1 <| morseReach_trans h2 h3

/-- Small-climb level `l`: the end of the flip and the retraction. -/
theorem phaseOne_climbRetract (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hl' : l ≤ 2 * k - 1) :
    MorseReach 1 (phaseOneClimbMid k l) (phaseOneClimb k l) := by
  have hcaps : morseCapRun (l + 1) = (.cap, l + 1) :: (.cap, l) :: morseCapRun (l - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    rw [morseCapRun_succ, morseCapRun_succ, Nat.add_sub_cancel]
  have hT1 : [(.cross false, l + 1), (.cross false, l + 2)] ++ morseShiftWord l phaseOneTq ++
      morseCapRun (l + 2) = morseShiftWord (l + 1) scbTangle ++ [(.cap, l)] ++
      morseCapRun (l - 1) := by
    rw [morseShiftWord_scbTangle, morseCapRun_succ, hcaps]
    simp only [morseShiftWord, phaseOneTq, List.map_cons, List.map_nil, shiftLetter,
      List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have hT2 : [(.cross false, l), (.cross false, l + 1)] ++ morseShiftWord (l - 1) phaseOneTq ++
      morseCapRun (l + 1) = morseShiftWord l scbTangle ++ morseCapRun (l - 1) := by
    rw [morseShiftWord_scbTangle, hcaps]
    simp only [morseShiftWord, phaseOneTq, List.map_cons, List.map_nil, shiftLetter,
      List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have hA : morseShiftWord (l - 1) stripA =
      [(.cup, l + 2), (.cross true, l + 1), (.cross true, l), (.cross false, l + 1),
        (.cap, l)] := by
    simp only [morseShiftWord, stripA, List.map_cons, List.map_nil, shiftLetter,
      List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  have hblk : phaseOneClimbBlocks (l - 1) (2 * k - l) (2 * k - 1) =
      morseShiftWord (l - 1) stripA ++ phaseOneClimbBlocks (l - 1) (2 * k - l - 1) (2 * k - 1) := by
    rw [← phaseOneClimbBlocks_succ_climb, show 2 * k - l - 1 + 1 = 2 * k - l by omega]
  have hmap := phaseOneClimbBlocks_map_climb (l - 1) (2 * k - l - 1) (2 * k - 1)
  rw [show l - 1 + 2 = l + 1 by omega] at hmap
  have hH : morseOut 1 (morseHeadRun l) = 2 * l + 1 := by
    rw [morseOut_morseHeadRun 1 _ le_rfl]
    omega
  obtain ⟨U, hU⟩ : ∃ U : MorseWord, U = morseHeadRun l ++ [(.cup, l + 2), (.cross true, l + 1),
      (.cross true, l), (.cross false, l + 1)] := ⟨_, rfl⟩
  have hUo : morseOut 1 U = 2 * l + 3 := by
    rw [hU, morseOut_append, hH]
    climb_fits
  obtain ⟨B, hB⟩ : ∃ B : MorseWord, B = phaseOneClimbBlocks (l + 1) (2 * k - l - 1) (2 * k - 1) :=
    ⟨_, rfl⟩
  have hUB : morseOut 1 (U ++ B) = 2 * l + 9 := by
    rw [morseOut_append, hUo, hB, morseOut_climbBlocks_climb _ _ _ _ (by omega)]
  have hBo := morseOut_band 0 l (by omega)
  have h1 := morseReach_macroSCb_climb l
    (U ++ B ++ [(.cross true, l + 1), (.cross true, l)] ++ morseBand 0 l) (morseCapRun (l - 1))
    (by simp only [morseOut_append, hUB, hBo]; climb_fits)
  have h2 := morseReach_symm <| morseReach_comm 1
    (U ++ B ++ [(.cross true, l + 1), (.cross true, l)]) (morseBand 0 l) [(.cap, l + 1)]
    (morseShiftWord l scbTangle ++ morseCapRun (l - 1))
    (fun b hb ↦ (mem_morseBand (by omega) hb).1)
    (fun b hb a ha ↦ by
      have := (mem_morseBand (by omega) hb).2.2
      rw [List.mem_singleton] at ha
      subst ha
      dsimp only
      omega)
    (by
      rw [morseFits_append, Bool.and_eq_true]
      refine ⟨by simp only [morseOut_append, hUB]; climb_fits,
        morseFits_of_cross _ _ (fun b hb ↦ (mem_morseBand (by omega) hb).1) fun b hb ↦ ?_⟩
      have := (mem_morseBand (by omega) hb).2.2
      simp only [morseOut_append, hUB, morseOut, morseLetterOut, morseKindIn, morseKindOut]
      omega)
  have h3 := morseReach_rule 1 (U ++ B) [] []
    (morseBand 0 l ++ morseShiftWord l scbTangle ++ morseCapRun (l - 1))
    [(.cross true, l + 1), (.cross true, l), (.cap, l + 1)] [(.cap, l)]
    (.capSlide l true false) false rfl
    (by simp only [List.append_nil, hUB]; climb_fits)
    (by simp only [List.append_nil, hUB]; climb_fits) rfl rfl
  have h4 := morseReach_symm <| morseReach_sweep 1 U B
    (morseBand 0 l ++ morseShiftWord l scbTangle ++ morseCapRun (l - 1)) (.cap, l)
    (fun b hb ↦ by
      rw [hB] at hb
      have := le_of_mem_climbBlocks_climb hb
      simp only [morseKindIn]
      omega)
    (by
      rw [hUo, morseFits_append, Bool.and_eq_true, hB,
        morseOut_climbBlocks_climb _ _ _ _ (by omega)]
      exact ⟨morseFits_climbBlocks_climb _ _ _ _ (by omega), by climb_fits⟩)
  simp only [morseKindOut, morseKindIn] at h4
  rw [hB, hmap] at h4
  unfold phaseOneClimbMid phaseOneClimb
  rw [morseBand_succ 0 l (by omega), hblk, hA]
  simp only [List.append_assoc] at hT1 hT2 ⊢
  rw [hT1, hT2]
  subst hU hB
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 ⊢
  exact morseReach_trans h1 <| morseReach_trans h2 <| morseReach_trans h3 h4

set_option linter.unusedVariables false in
/-- The last word of phase I is the strip word. -/
theorem phaseOneClimb_one (k : ℕ) (hk : 1 ≤ k) : phaseOneClimb k 1 = stripWord k := by
  have h0 : ∀ w : MorseWord, morseShiftWord 0 w = w := fun w ↦ by
    simp only [morseShiftWord]
    exact List.map_id'' (fun x ↦ by simp [shiftLetter]) w
  rw [phaseOneClimb, stripWord, Nat.sub_self, phaseOneClimbBlocks, h0, h0]
  simp [morseHeadRun, morseBand, morseOfBraid, surfaceBand, morseCapRun, stripP, stripQ,
    phaseOneTq, List.range_succ]

/-- One small-climb level step (composition). -/
theorem phaseOne_climbStep (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hl' : l ≤ 2 * k - 1) :
    MorseReach 1 (phaseOneClimb k (l + 1)) (phaseOneClimb k l) :=
  morseReach_trans (phaseOne_climbFlip k l hk hl hl') (phaseOne_climbRetract k l hk hl hl')

/-- The small-climb phase, levels `2k-1` down to `L` (induction on the number of levels). -/
theorem phaseOne_climbChain (k : ℕ) (hk : 1 ≤ k) (L : ℕ) (hL : 1 ≤ L) (hL' : L ≤ 2 * k) :
    MorseReach 1 (phaseOneClimb k (2 * k)) (phaseOneClimb k L) := by
  obtain ⟨m, rfl⟩ : ∃ m, L = 2 * k - m := ⟨2 * k - L, by omega⟩
  induction m with
  | zero => exact morseReach_refl 1 _
  | succ m ih =>
    have h2 := phaseOne_climbStep k (2 * k - (m + 1)) hk (by omega) (by omega)
    rw [show 2 * k - (m + 1) + 1 = 2 * k - m by omega] at h2
    exact morseReach_trans (ih (by omega) (by omega)) h2

end AJConjecture
