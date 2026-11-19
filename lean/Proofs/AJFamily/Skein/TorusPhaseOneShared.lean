import Mathlib
import AJFamily.Skein.MorseFrame
import AJFamily.Skein.TorusPhaseOneWords

/-!
# Phase I: the pieces shared by several level steps

Frame-generic lemmas used by several level steps of phase I, each a short chain of generic moves
and fixed macros: the start of a flip, where the closing arc passes the last head cup
(`phaseOne_flipHead`); the end of a flip, where the walk passes the staircase and the final climb
(`phaseOne_flipTail`); the retraction of the cap of a level (`phaseOne_capRetract`,
`phaseOne_capRetractX`); and the retraction of the dead cup through the big climb
(`phaseOne_retractHead`).
-/

namespace AJConjecture

/-! ### Private helpers -/

/-- A rule applied, in either direction, at a junction inside a word. -/
theorem morseReach_rule (n₀ : ℕ) (P pre post v w w' : MorseWord) (r : MorseRule)
    (bk : Bool) (hok : morseRuleOk r = true)
    (hl : morseFits (morseOut n₀ (P ++ pre)) (morseRuleLhs r) = true)
    (hr : morseFits (morseOut n₀ (P ++ pre)) (morseRuleRhs r) = true)
    (hw : w = pre ++ (if bk then morseRuleRhs r else morseRuleLhs r) ++ post)
    (hw' : w' = pre ++ (if bk then morseRuleLhs r else morseRuleRhs r) ++ post) :
    MorseReach n₀ (P ++ w ++ v) (P ++ w' ++ v) := by
  subst hw hw'
  have hs : morseFits (morseOut n₀ (P ++ pre))
      (if bk then morseRuleRhs r else morseRuleLhs r) = true := by
    cases bk <;> simpa
  have hd : morseFits (morseOut n₀ (P ++ pre))
      (if bk then morseRuleLhs r else morseRuleRhs r) = true := by
    cases bk <;> simpa
  refine ⟨[((P ++ pre).length, r, bk)], ?_⟩
  have e : ∀ x : MorseWord, P ++ (pre ++ x ++ post) ++ v = P ++ pre ++ x ++ (post ++ v) := by
    intro x
    simp only [List.append_assoc]
  rw [e, e]
  generalize P ++ pre = a at hs hd ⊢
  simp only [morseApplyAll, morseApply]
  simp [hok, hs, hd]

/-- A cup run grows at the end. -/
theorem morseCupRun_succ (a b : ℕ) (h : a ≤ b + 1) :
    morseCupRun a (b + 1) = morseCupRun a b ++ [(MorseKind.cup, b + 1)] := by
  simp only [morseCupRun]
  rw [show b + 1 + 1 - a = (b + 1 - a) + 1 by omega, List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  congr 3
  omega

/-- A staircase grows at the front. -/
private theorem morseStairRun_succ_shared (a b : ℕ) (h : a ≤ b + 1) :
    morseStairRun a (b + 1) = morseBand (b + 1) (b + 3) ++ morseStairRun a b := by
  simp only [morseStairRun]
  rw [show b + 1 + 1 - a = (b + 1 - a) + 1 by omega, List.range_succ, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.flatMap_cons]
  rw [show a + (b + 1 - a) = b + 1 by omega]

/-- A cap run grows at the front. -/
theorem morseCapRun_succ (m : ℕ) :
    morseCapRun (m + 1) = (MorseKind.cap, m + 1) :: morseCapRun m := by
  simp [morseCapRun, List.range_succ, List.reverse_append]

/-- The arity of the head and the cups in front of a level. -/
theorem morseOut_head_cups (k l : ℕ) (hk : 1 ≤ k) (hl : 2 * k ≤ l + 1) :
    morseOut 1 (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l) = 2 * l + 1 := by
  rw [morseOut_append, morseOut_morseHeadRun 1 _ le_rfl,
    morseOut_morseCupRun _ _ _ (by omega)]
  omega

/-- A band does not change the number of strands. -/
theorem morseOut_band (i j : ℕ) (hij : i < j) (n : ℕ) :
    morseOut n (morseBand i j) = n :=
  morseOut_of_cross n _ fun _ hb ↦ (mem_morseBand hij hb).1

/-- The letters of the staircase followed by the last crossing. -/
private theorem mem_stairLast_shared {k c : ℕ} {b : MorseLetter}
    (hb : b ∈ morseStairRun (2 * k) c ++ morseBand 0 (2 * k + 1)) :
    (∃ s, b.1 = MorseKind.cross s) ∧ (b.2 ≤ c + 1 ∨ b.2 ≤ 2 * k) := by
  rcases List.mem_append.mp hb with h | h
  · exact ⟨(mem_morseStairRun h).1, Or.inl (mem_morseStairRun h).2.2⟩
  · have := mem_morseBand (by omega) h
    exact ⟨this.1, Or.inr (by omega)⟩

/-- Closes the arity side goals of the local moves. -/
local macro "shared_fits" : tactic =>
  `(tactic| ((try simp only [morseRuleLhs, morseRuleRhs, morseRuleOk, morseOut_append,
    morseOut, morseLetterOut, morseFits_cons, morseFits_nil, morseKindIn,
    morseKindOut, and_true, ↓reduceIte, Bool.false_eq_true, List.nil_append,
    List.append_nil]) <;> omega))

/-- Macro `TL` at the shift `l`, as twelve explicit moves. -/
private theorem morseReach_macroTL_shared (l : ℕ) (hl : 1 ≤ l) (P v : MorseWord)
    (hP : morseOut 1 P = 2 * l + 5) :
    MorseReach 1
      (P ++ [(.cross false, l), (.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4),
        (.cross true, l + 2), (.cap, l + 2), (.cap, l + 1), (.cap, l)] ++ v)
      (P ++ [(.cap, l + 1), (.cross true, l + 1), (.cap, l + 1), (.cap, l)] ++ v) := by
  have s1 := morseReach_rule 1 P
    [(.cross false, l)]
    [(.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4), (.cross true, l + 2),
      (.cap, l + 2), (.cap, l + 1), (.cap, l)] v
    [(.cross false, l), (.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4),
      (.cross true, l + 2), (.cap, l + 2), (.cap, l + 1), (.cap, l)]
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 1), (.cross true, l + 2),
      (.cross true, l + 3), (.cross true, l + 4), (.cross true, l + 2), (.cap, l + 2),
      (.cap, l + 1), (.cap, l)]
    (.r2 (l + 1) false) true rfl
    (by simp only [morseOut_append, hP]; shared_fits)
    (by simp only [morseOut_append, hP]; shared_fits) rfl rfl
  have s2 := morseReach_rule 1 P
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 1), (.cross true, l + 2),
      (.cross true, l + 3)]
    [(.cap, l + 2), (.cap, l + 1), (.cap, l)] v
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 1), (.cross true, l + 2),
      (.cross true, l + 3), (.cross true, l + 4), (.cross true, l + 2), (.cap, l + 2),
      (.cap, l + 1), (.cap, l)]
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 1), (.cross true, l + 2),
      (.cross true, l + 3), (.cross true, l + 2), (.cross true, l + 4), (.cap, l + 2),
      (.cap, l + 1), (.cap, l)]
    (.exch (.cross true, l + 2) (.cross true, l + 4)) true
    (decide_eq_true (by dsimp only [morseKindIn]; omega))
    (by simp only [morseOut_append, hP]; shared_fits)
    (by simp only [morseOut_append, hP]; shared_fits) rfl rfl
  have s3 := morseReach_rule 1 P
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 1)]
    [(.cross true, l + 4), (.cap, l + 2), (.cap, l + 1), (.cap, l)] v
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 1), (.cross true, l + 2),
      (.cross true, l + 3), (.cross true, l + 2), (.cross true, l + 4), (.cap, l + 2),
      (.cap, l + 1), (.cap, l)]
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 1), (.cross true, l + 3),
      (.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4), (.cap, l + 2),
      (.cap, l + 1), (.cap, l)]
    (.r3 (l + 2) true) false rfl
    (by simp only [morseOut_append, hP]; shared_fits)
    (by simp only [morseOut_append, hP]; shared_fits) rfl rfl
  have s4 := morseReach_rule 1 P
    [(.cross false, l), (.cross false, l + 1)]
    [(.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4), (.cap, l + 2), (.cap, l + 1),
      (.cap, l)] v
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 1), (.cross true, l + 3),
      (.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4), (.cap, l + 2),
      (.cap, l + 1), (.cap, l)]
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cross true, l + 1),
      (.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4), (.cap, l + 2),
      (.cap, l + 1), (.cap, l)]
    (.exch (.cross true, l + 1) (.cross true, l + 3)) false
    (decide_eq_true (by dsimp only [morseKindIn]; omega))
    (by simp only [morseOut_append, hP]; shared_fits)
    (by simp only [morseOut_append, hP]; shared_fits) rfl rfl
  have s5 := morseReach_rule 1 P
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cross true, l + 1),
      (.cross true, l + 2), (.cross true, l + 3)]
    [(.cap, l + 1), (.cap, l)] v
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cross true, l + 1),
      (.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4), (.cap, l + 2),
      (.cap, l + 1), (.cap, l)]
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cross true, l + 1),
      (.cross true, l + 2), (.cross true, l + 3), (.cap, l + 2), (.cross true, l + 2),
      (.cap, l + 1), (.cap, l)]
    (.exch (.cap, l + 2) (.cross true, l + 4)) true
    (decide_eq_true (by dsimp only [morseKindIn]; omega))
    (by simp only [morseOut_append, hP]; shared_fits)
    (by simp only [morseOut_append, hP]; shared_fits) rfl rfl
  have s6 := morseReach_rule 1 P
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cross true, l + 1)]
    [(.cross true, l + 2), (.cap, l + 1), (.cap, l)] v
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cross true, l + 1),
      (.cross true, l + 2), (.cross true, l + 3), (.cap, l + 2), (.cross true, l + 2),
      (.cap, l + 1), (.cap, l)]
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cross true, l + 1),
      (.cap, l + 3), (.cross true, l + 2), (.cap, l + 1), (.cap, l)]
    (.capSlide (l + 2) true true) false rfl
    (by simp only [morseOut_append, hP]; shared_fits)
    (by simp only [morseOut_append, hP]; shared_fits) rfl rfl
  have s7 := morseReach_rule 1 P
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3)]
    [(.cross true, l + 2), (.cap, l + 1), (.cap, l)] v
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cross true, l + 1),
      (.cap, l + 3), (.cross true, l + 2), (.cap, l + 1), (.cap, l)]
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cap, l + 3),
      (.cross true, l + 1), (.cross true, l + 2), (.cap, l + 1), (.cap, l)]
    (.exch (.cross true, l + 1) (.cap, l + 3)) false
    (decide_eq_true (by dsimp only [morseKindIn]; omega))
    (by simp only [morseOut_append, hP]; shared_fits)
    (by simp only [morseOut_append, hP]; shared_fits) rfl rfl
  have s8 := morseReach_rule 1 P
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cap, l + 3)]
    [(.cap, l)] v
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cap, l + 3),
      (.cross true, l + 1), (.cross true, l + 2), (.cap, l + 1), (.cap, l)]
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cap, l + 3), (.cap, l + 2),
      (.cap, l)]
    (.capSlide (l + 1) true true) false rfl
    (by simp only [morseOut_append, hP]; shared_fits)
    (by simp only [morseOut_append, hP]; shared_fits) rfl rfl
  have s9 := morseReach_rule 1 P
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cap, l + 3)]
    [] v
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cap, l + 3), (.cap, l + 2),
      (.cap, l)]
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cap, l + 3), (.cap, l),
      (.cap, l)]
    (.exch (.cap, l) (.cap, l + 2)) true
    (decide_eq_true (by dsimp only [morseKindIn]; omega))
    (by simp only [morseOut_append, hP]; shared_fits)
    (by simp only [morseOut_append, hP]; shared_fits) rfl rfl
  have s10 := morseReach_rule 1 P
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3)]
    [(.cap, l)] v
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cap, l + 3), (.cap, l),
      (.cap, l)]
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cap, l), (.cap, l + 1),
      (.cap, l)]
    (.exch (.cap, l) (.cap, l + 3)) true
    (decide_eq_true (by dsimp only [morseKindIn]; omega))
    (by simp only [morseOut_append, hP]; shared_fits)
    (by simp only [morseOut_append, hP]; shared_fits) rfl rfl
  have s11 := morseReach_rule 1 P
    [(.cross false, l), (.cross false, l + 1)]
    [(.cap, l + 1), (.cap, l)] v
    [(.cross false, l), (.cross false, l + 1), (.cross true, l + 3), (.cap, l), (.cap, l + 1),
      (.cap, l)]
    [(.cross false, l), (.cross false, l + 1), (.cap, l), (.cross true, l + 1), (.cap, l + 1),
      (.cap, l)]
    (.exch (.cap, l) (.cross true, l + 3)) true
    (decide_eq_true (by dsimp only [morseKindIn]; omega))
    (by simp only [morseOut_append, hP]; shared_fits)
    (by simp only [morseOut_append, hP]; shared_fits) rfl rfl
  have s12 := morseReach_rule 1 P
    []
    [(.cross true, l + 1), (.cap, l + 1), (.cap, l)] v
    [(.cross false, l), (.cross false, l + 1), (.cap, l), (.cross true, l + 1), (.cap, l + 1),
      (.cap, l)]
    [(.cap, l + 1), (.cross true, l + 1), (.cap, l + 1), (.cap, l)]
    (.capSlide l false true) false rfl
    (by simp only [morseOut_append, hP]; shared_fits)
    (by simp only [morseOut_append, hP]; shared_fits) rfl rfl
  exact morseReach_trans s1 <| morseReach_trans s2 <| morseReach_trans s3 <|
    morseReach_trans s4 <| morseReach_trans s5 <| morseReach_trans s6 <|
    morseReach_trans s7 <| morseReach_trans s8 <| morseReach_trans s9 <|
    morseReach_trans s10 <| morseReach_trans s11 s12

/-- The first two moves of the retraction of a cap: the cap passes the final climb, then slides
along the closing arc. -/
private theorem capRetract_head_shared (k l : ℕ) (hl : 2 * k + 1 ≤ l)
    (u : MorseWord) (hu : morseOut 1 u = 2 * l + 5) :
    MorseReach 1 (u ++ phaseOneTailFlipped k l)
      (u ++ (morseStairRun (2 * k) (l - 2) ++ morseBand 0 (2 * k + 1)) ++ [(MorseKind.cap, l)] ++
        morseBand (2 * k) l ++ ((MorseKind.cross true, l + 1) :: morseCapRun (l + 1))) := by
  have hX : ∀ n, morseOut n (morseStairRun (2 * k) (l - 2) ++ morseBand 0 (2 * k + 1)) = n :=
    fun n ↦ morseOut_of_cross n _ fun b hb ↦ (mem_stairLast_shared hb).1
  have hBo := morseOut_band (2 * k) l (by omega)
  unfold phaseOneTailFlipped
  generalize morseStairRun (2 * k) (l - 2) ++ morseBand 0 (2 * k + 1) = X at hX ⊢
  have h1 := morseReach_symm <| morseReach_comm 1
    (u ++ X ++ [(.cross true, l + 1), (.cross true, l)]) (morseBand (2 * k) l) [(.cap, l + 1)]
    ((.cross true, l + 1) :: morseCapRun (l + 1))
    (fun b hb ↦ (mem_morseBand (by omega) hb).1)
    (fun b hb a ha ↦ by
      have := (mem_morseBand (by omega) hb).2.2
      rw [List.mem_singleton] at ha
      subst ha
      dsimp only
      omega)
    (by
      rw [morseFits_append, Bool.and_eq_true]
      refine ⟨by simp only [morseOut_append, hu, hX]; shared_fits,
        morseFits_of_cross _ _ (fun b hb ↦ (mem_morseBand (by omega) hb).1) fun b hb ↦ ?_⟩
      have := (mem_morseBand (by omega) hb).2.2
      simp only [morseOut_append, hu, hX, morseOut, morseLetterOut, morseKindIn, morseKindOut]
      omega)
  have h2 := morseReach_rule 1 (u ++ X) [] []
    (morseBand (2 * k) l ++ (.cross true, l + 1) :: morseCapRun (l + 1))
    [(.cross true, l + 1), (.cross true, l), (.cap, l + 1)] [(.cap, l)]
    (.capSlide l true false) false rfl
    (by simp only [morseOut_append, hu, hX]; shared_fits)
    (by simp only [morseOut_append, hu, hX]; shared_fits) rfl rfl
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
  exact morseReach_trans h1 h2

/-- The flip of the levels `2k+1 … 4k-1` starts: the closing arc passes the last head cup and the
first letter of its walk passes the big climb. -/
theorem phaseOne_flipHead (k l : ℕ) (hk : 1 ≤ k) (hl : 2 * k + 1 ≤ l) (v : MorseWord) :
    MorseReach 1
      (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l ++ [(.cup, l + 1)] ++
        morseBand (2 * k - 1) (l + 1) ++ v)
      (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l ++ [(.cup, l + 2), (.cross true, l + 1)] ++
        morseBand (2 * k - 1) (l + 1) ++ [(.cross true, l + 2)] ++ v) := by
  have hH := morseOut_head_cups k l hk (by omega)
  generalize morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l = H at hH ⊢
  have h1 := morseReach_rule 1 H [] [] (morseBand (2 * k - 1) (l + 1) ++ v)
    [(.cup, l + 1)] [(.cup, l + 2), (.cross true, l + 1), (.cross true, l + 2)]
    (.cupSlide (l + 1) true true) true rfl
    (by simp only [morseOut_append, hH]; shared_fits)
    (by simp only [morseOut_append, hH]; shared_fits) rfl rfl
  have hn : morseOut 1 (H ++ [(.cup, l + 2), (.cross true, l + 1)]) = 2 * l + 3 := by
    simp only [morseOut_append, hH]
    shared_fits
  have h2 := morseReach_comm 1 (H ++ [(.cup, l + 2), (.cross true, l + 1)])
    (morseBand (2 * k - 1) (l + 1)) [(.cross true, l + 2)] v
    (fun b hb ↦ (mem_morseBand (by omega) hb).1)
    (fun b hb a ha ↦ by
      have := (mem_morseBand (by omega) hb).2.2
      rw [List.mem_singleton] at ha
      subst ha
      dsimp only
      omega)
    (by
      rw [hn]
      refine morseFits_of_cross _ _ (fun b hb ↦ ?_) (fun b hb ↦ ?_)
      · rcases List.mem_append.mp hb with h | h
        · rw [List.mem_singleton] at h
          exact ⟨true, by rw [h]⟩
        · exact (mem_morseBand (by omega) h).1
      · rcases List.mem_append.mp hb with h | h
        · rw [List.mem_singleton] at h
          rw [h]
          dsimp only
          omega
        · have := (mem_morseBand (by omega) h).2.2
          omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
  exact morseReach_trans h1 h2

/-- The flip of the level `l` ends: the walk passes the staircase, the last crossing and the
final climb, and ends at the closing caps. -/
theorem phaseOne_flipTail (k l : ℕ) (hk : 1 ≤ k) (hl : 2 * k + 1 ≤ l) (u : MorseWord)
    (hu : morseOut 1 u = 2 * l + 5) :
    MorseReach 1 (u ++ phaseOneTailWalk k l) (u ++ phaseOneTailFlipped k l) := by
  have hX : ∀ n, morseOut n (morseStairRun (2 * k) (l - 2) ++ morseBand 0 (2 * k + 1)) = n :=
    fun n ↦ morseOut_of_cross n _ fun b hb ↦ (mem_stairLast_shared hb).1
  have hBo := morseOut_band (2 * k) l (by omega)
  have hwalk : morseWalk true (l + 1) 4 = [(.cross true, l + 1), (.cross true, l + 2),
      (.cross true, l + 3), (.cross true, l + 4)] := rfl
  have hcaps : morseCapRun (l + 1) = (.cap, l + 1) :: (.cap, l) :: morseCapRun (l - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    rw [morseCapRun_succ, morseCapRun_succ, Nat.add_sub_cancel]
  have h1 := morseReach_comm 1 u (morseStairRun (2 * k) (l - 2) ++ morseBand 0 (2 * k + 1))
    [(.cross true, l + 1), (.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4)]
    (morseBand (2 * k) (l + 1) ++ [(.cross true, l + 2)] ++ morseCapRun (l + 2))
    (fun b hb ↦ (mem_stairLast_shared hb).1)
    (fun b hb a ha ↦ by
      have := (mem_stairLast_shared hb).2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> dsimp only <;> omega)
    (by
      rw [morseFits_append, Bool.and_eq_true]
      refine ⟨by rw [hu]; shared_fits,
        morseFits_of_cross _ _ (fun b hb ↦ (mem_stairLast_shared hb).1) fun b hb ↦ ?_⟩
      have := (mem_stairLast_shared hb).2
      simp only [hu, morseOut, morseLetterOut, morseKindIn, morseKindOut]
      omega)
  have h2 := morseReach_comm 1
    (u ++ (morseStairRun (2 * k) (l - 2) ++ morseBand 0 (2 * k + 1)) ++ [(.cross true, l + 1)])
    (morseBand (2 * k) (l + 1))
    [(.cross true, l + 2), (.cross true, l + 3), (.cross true, l + 4)]
    ([(.cross true, l + 2)] ++ morseCapRun (l + 2))
    (fun b hb ↦ (mem_morseBand (by omega) hb).1)
    (fun b hb a ha ↦ by
      have := (mem_morseBand (by omega) hb).2.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> dsimp only <;> omega)
    (by
      rw [morseFits_append, Bool.and_eq_true]
      refine ⟨by simp only [morseOut_append, hu, hX]; shared_fits,
        morseFits_of_cross _ _ (fun b hb ↦ (mem_morseBand (by omega) hb).1) fun b hb ↦ ?_⟩
      have := (mem_morseBand (by omega) hb).2.2
      simp only [morseOut_append, hu, hX, morseOut, morseLetterOut, morseKindIn, morseKindOut]
      omega)
  have h3 := morseReach_macroTL_shared l (by omega)
    (u ++ (morseStairRun (2 * k) (l - 2) ++ morseBand 0 (2 * k + 1)) ++
      [(.cross true, l + 1), (.cross true, l)] ++ morseBand (2 * k) l)
    (morseCapRun (l - 1))
    (by simp only [morseOut_append, hu, hX, hBo]; shared_fits)
  unfold phaseOneTailWalk phaseOneTailFlipped
  rw [hwalk, morseBand_succ (2 * k) l (by omega), show l + 2 = l + 1 + 1 by rfl,
    morseCapRun_succ (l + 1), hcaps]
  rw [morseBand_succ (2 * k) l (by omega), show l + 2 = l + 1 + 1 by rfl,
    morseCapRun_succ (l + 1), hcaps] at h1 h2
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
  exact morseReach_trans h1 <| morseReach_trans h2 h3

/-- The retraction of the cap of the level `l` (`l ≥ 2k + 2`). -/
theorem phaseOne_capRetract (k l : ℕ) (hk : 1 ≤ k) (hl : 2 * k + 2 ≤ l) (u : MorseWord)
    (hu : morseOut 1 u = 2 * l + 5) :
    MorseReach 1 (u ++ phaseOneTailFlipped k l) (u ++ phaseOneTailRetracted k l) := by
  refine morseReach_trans (capRetract_head_shared k l (by omega) u hu) ?_
  have hst : morseStairRun (2 * k) (l - 2) =
      morseBand (l - 2) l ++ morseStairRun (2 * k) (l - 3) := by
    have := morseStairRun_succ_shared (2 * k) (l - 3) (by omega)
    rwa [show l - 3 + 1 = l - 2 by omega, show l - 3 + 3 = l by omega] at this
  have hBo := morseOut_band (l - 2) l (by omega)
  have h := morseReach_symm <| morseReach_comm 1 (u ++ morseBand (l - 2) l)
    (morseStairRun (2 * k) (l - 3) ++ morseBand 0 (2 * k + 1)) [(.cap, l)]
    (morseBand (2 * k) l ++ (.cross true, l + 1) :: morseCapRun (l + 1))
    (fun b hb ↦ (mem_stairLast_shared hb).1)
    (fun b hb a ha ↦ by
      have := (mem_stairLast_shared hb).2
      rw [List.mem_singleton] at ha
      subst ha
      dsimp only
      omega)
    (by
      rw [morseFits_append, Bool.and_eq_true]
      refine ⟨by simp only [morseOut_append, hu, hBo]; shared_fits,
        morseFits_of_cross _ _ (fun b hb ↦ (mem_stairLast_shared hb).1) fun b hb ↦ ?_⟩
      have := (mem_stairLast_shared hb).2
      simp only [morseOut_append, hu, hBo, morseOut, morseLetterOut, morseKindIn, morseKindOut]
      omega)
  unfold phaseOneTailRetracted
  rw [hst]
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h ⊢
  exact h

/-- The retraction of the cap of the level `2k + 1`. -/
theorem phaseOne_capRetractX (k : ℕ) (hk : 1 ≤ k) (u : MorseWord) (hu : morseOut 1 u = 4 * k + 7) :
    MorseReach 1 (u ++ phaseOneTailFlipped k (2 * k + 1)) (u ++ phaseOneTailX k) := by
  refine morseReach_trans (capRetract_head_shared k (2 * k + 1) le_rfl u (by omega)) ?_
  have hst : morseStairRun (2 * k) (2 * k + 1 - 2) = [] := by
    rw [morseStairRun, show 2 * k + 1 - 2 + 1 - 2 * k = 0 by omega]
    rfl
  unfold phaseOneTailX
  rw [hst]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact morseReach_refl _ _

/-- The retraction of the levels `2k+1 … 4k-1` starts: the dead cup travels through the big
climb, which loses its outer crossings. -/
theorem phaseOne_retractHead (k l : ℕ) (hk : 1 ≤ k) (hl : 2 * k + 1 ≤ l) (v : MorseWord) :
    MorseReach 1
      (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l ++ [(.cup, l + 2), (.cross true, l + 1)] ++
        morseBand (2 * k - 1) (l + 1) ++ [(.cross false, l + 1)] ++ v)
      (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l ++ morseBand (2 * k - 1) l ++ [(.cup, l)] ++
        v) := by
  have hcup : morseCupRun (2 * k) l = morseCupRun (2 * k) (l - 1) ++ [(MorseKind.cup, l)] := by
    have := morseCupRun_succ (2 * k) (l - 1) (by omega)
    rwa [show l - 1 + 1 = l by omega] at this
  have hH := morseOut_head_cups k (l - 1) hk (by omega)
  have hBo := morseOut_band (2 * k - 1) l (by omega)
  rw [hcup, ← List.append_assoc (morseHeadRun (2 * k - 1)),
    morseBand_succ (2 * k - 1) l (by omega)]
  generalize morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) (l - 1) = H at hH ⊢
  have h1 := morseReach_rule 1 H [] [(.cross true, l + 1), (.cross true, l)]
    (morseBand (2 * k - 1) l ++ [(.cross false, l), (.cross false, l + 1)] ++ v)
    [(.cup, l), (.cup, l + 2), (.cross true, l + 1), (.cross true, l)]
    [(.cup, l), (.cup, l), (.cross true, l + 1), (.cross true, l)]
    (.exch (.cup, l) (.cup, l)) false
    (decide_eq_true (by dsimp only [morseKindIn]; omega))
    (by simp only [morseOut_append, hH]; shared_fits)
    (by simp only [morseOut_append, hH]; shared_fits) rfl rfl
  have h2 := morseReach_rule 1 H [(.cup, l)] []
    (morseBand (2 * k - 1) l ++ [(.cross false, l), (.cross false, l + 1)] ++ v)
    [(.cup, l), (.cup, l), (.cross true, l + 1), (.cross true, l)] [(.cup, l), (.cup, l + 1)]
    (.cupSlide l true false) false rfl
    (by simp only [morseOut_append, hH]; shared_fits)
    (by simp only [morseOut_append, hH]; shared_fits) rfl rfl
  have h3 := morseReach_comm 1 (H ++ [(.cup, l)]) (morseBand (2 * k - 1) l) [(.cup, l + 1)]
    ([(.cross false, l), (.cross false, l + 1)] ++ v)
    (fun b hb ↦ (mem_morseBand (by omega) hb).1)
    (fun b hb a ha ↦ by
      have := (mem_morseBand (by omega) hb).2.2
      rw [List.mem_singleton] at ha
      subst ha
      dsimp only
      omega)
    (by
      rw [morseFits_append, Bool.and_eq_true]
      refine ⟨by simp only [morseOut_append, hH]; shared_fits,
        morseFits_of_cross _ _ (fun b hb ↦ (mem_morseBand (by omega) hb).1) fun b hb ↦ ?_⟩
      have := (mem_morseBand (by omega) hb).2.2
      simp only [morseOut_append, hH, morseOut, morseLetterOut, morseKindIn, morseKindOut]
      omega)
  have h4 := morseReach_rule 1 (H ++ [(.cup, l)] ++ morseBand (2 * k - 1) l) [] [] v
    [(.cup, l + 1), (.cross false, l), (.cross false, l + 1)] [(.cup, l)]
    (.cupSlide l false true) false rfl
    (by simp only [morseOut_append, hH, hBo]; shared_fits)
    (by simp only [morseOut_append, hH, hBo]; shared_fits) rfl rfl
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 ⊢
  exact morseReach_trans h1 <| morseReach_trans h2 <| morseReach_trans h3 h4

end AJConjecture
