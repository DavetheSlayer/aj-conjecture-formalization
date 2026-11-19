import Mathlib
import AJHandoff.TorusKnot.PairKIsoMacros

/-!
# The normal forms of the round blocks (induction on `r`)

The three blocks whose band passes `r - 1` discs. Each statement is local (no idle strand on the
left) and is proved by induction on `r ≥ 2`, peeling off the disc passed first: for the rounds
`[u1] b(1, 3 + 2r) [n(3 + 2r)]` reaches `τ_{2r-1}(D) · [u1] b(1, 1 + 2r) [n(1 + 2r)]` (one doubled
crossing; checked for `r ≤ 4`), and `morseDouble (walkL 0 r) = τ_{2(r-1)} D · morseDouble
(walkL 0 (r-1))`. The case `r = 2` is the library macro `B` (`morseReach_phaseTwoMacroB`, after a
`cupSlide`) for the rounds and macro `M` for round `0`. All three statements were checked for
`r = 2, 3, 4` (`SCR/ISO/tools/c2checks.py`).
-/

namespace AJConjecture

/-- The doubled positive crossing of the bands `(k, k + 1)` and `(k + 2, k + 3)`. -/
private def dblPos_roundNF (k : ℕ) : MorseWord :=
  [isoX true (k + 1), isoX true (k + 2), isoX true k, isoX true (k + 1)]

/-- The doubled negative crossing of the bands `(k, k + 1)` and `(k + 2, k + 3)`. -/
private def dblNeg_roundNF (k : ℕ) : MorseWord :=
  [isoX false (k + 1), isoX false k, isoX false (k + 2), isoX false (k + 1)]

/-- Closes arity goals of the local moves of the round normal forms. -/
local macro "rnf_fits" : tactic =>
  `(tactic| (simp only [morseRuleLhs, morseRuleRhs, morseRuleOk, morseOut_append, morseOut,
    morseLetterOut, morseFits_cons, morseFits_nil, morseFits_append, isoX, isoU, isoN,
    morseKindIn, morseKindOut, Bool.and_eq_true, decide_eq_true_eq, and_true, true_and,
    ↓reduceIte, Bool.false_eq_true, morseShiftWord, List.map_cons, List.map_nil,
    shiftLetter, dblPos_roundNF, dblNeg_roundNF] <;> omega))

/-- A rule applied backward at the junction of `u` and `v`. -/
private theorem morseReach_isoRule_back_roundNF (n₀ : ℕ) (u v : MorseWord) (r : MorseRule)
    (hok : morseRuleOk r = true)
    (hl : morseFits (morseOut n₀ u) (morseRuleLhs r) = true)
    (hr : morseFits (morseOut n₀ u) (morseRuleRhs r) = true) :
    MorseReach n₀ (u ++ morseRuleRhs r ++ v) (u ++ morseRuleLhs r ++ v) :=
  morseReach_symm (morseReach_isoRule n₀ u v r hok hl hr)

/-- The peeling step: a band reaching two strands further splits off a doubled crossing. -/
private theorem morseReach_peel_roundNF (n₀ p : ℕ) (u X v : MorseWord)
    (hXc : ∀ l ∈ X, ∃ s, l.1 = MorseKind.cross s) (hXp : ∀ l ∈ X, l.2 + 1 ≤ p)
    (hm : p + 4 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ [isoX true (p + 1), isoX true p] ++ X ++
        [isoX false p, isoX false (p + 1), isoN (p + 2)] ++ v)
      (u ++ [isoX true (p + 1), isoX true (p + 2), isoX true p, isoX true (p + 1)] ++ X ++
        [isoN p] ++ v) := by
  have hXo : ∀ n, morseOut n X = n := fun n ↦ morseOut_of_cross n X hXc
  have hXf : ∀ n, p + 1 ≤ n → morseFits n X = true := fun n hn ↦
    morseFits_of_cross n X hXc fun l hl ↦ by have := hXp l hl; omega
  set m := morseOut n₀ u with hmdef
  apply morseReach_symm
  -- W0 → W1
  have s1 := morseReach_isoRule_back_roundNF n₀
    (u ++ [isoX true (p + 1), isoX true (p + 2), isoX true p, isoX true (p + 1)] ++ X) v
    (.capSlide p false false) rfl (by rw [morseOut_append, hXo]; rnf_fits)
    (by rw [morseOut_append, hXo]; rnf_fits)
  -- W1 → W2
  have s2 := morseReach_symm (morseReach_comm n₀
    (u ++ [isoX true (p + 1), isoX true (p + 2), isoX true p, isoX true (p + 1)]) X
    [isoX false (p + 1)] ([isoX false p, isoN (p + 1)] ++ v) hXc
    (fun b hb a ha ↦ by
      simp only [List.mem_singleton] at ha
      subst ha
      have := hXp b hb
      simp only [isoX]
      omega)
    (by
      rw [morseFits_append, hXf _ (by rnf_fits)]
      rnf_fits))
  -- W2 → W3
  have s3 := morseReach_isoRule n₀ (u ++ [isoX true (p + 1), isoX true (p + 2), isoX true p])
    (X ++ [isoX false p, isoN (p + 1)] ++ v) (.r2 (p + 1) true) rfl (by rnf_fits) (by rnf_fits)
  -- W3 → W4
  have s4 := morseReach_isoRule_back_roundNF n₀
    (u ++ [isoX true (p + 1), isoX true (p + 2), isoX true p] ++ X ++ [isoX false p]) v
    (.capSlide (p + 1) false false) rfl (by rw [morseOut_append, morseOut_append, hXo]; rnf_fits)
    (by rw [morseOut_append, morseOut_append, hXo]; rnf_fits)
  -- W4 → W5
  have s5 := morseReach_isoRule n₀
    (u ++ [isoX true (p + 1), isoX true (p + 2), isoX true p] ++ X)
    ([isoX false (p + 1), isoN (p + 2)] ++ v)
    (.exch (isoX false p) (isoX false (p + 2))) (by simp [morseRuleOk, isoX, morseKindIn])
    (by rw [morseOut_append, hXo]; rnf_fits) (by rw [morseOut_append, hXo]; rnf_fits)
  -- W5 → W6
  have s6 := morseReach_symm (morseReach_comm n₀
    (u ++ [isoX true (p + 1), isoX true (p + 2), isoX true p]) X
    [isoX false (p + 2)] ([isoX false p, isoX false (p + 1), isoN (p + 2)] ++ v) hXc
    (fun b hb a ha ↦ by
      simp only [List.mem_singleton] at ha
      subst ha
      have := hXp b hb
      simp only [isoX]
      omega)
    (by
      rw [morseFits_append, hXf _ (by rnf_fits)]
      rnf_fits))
  -- W6 → W7
  have s7 := morseReach_isoRule n₀ (u ++ [isoX true (p + 1), isoX true (p + 2)])
    (X ++ [isoX false p, isoX false (p + 1), isoN (p + 2)] ++ v)
    (.exch (isoX true p) (isoX false (p + 2))) (by simp [morseRuleOk, isoX, morseKindIn])
    (by rnf_fits) (by rnf_fits)
  -- W7 → W8
  have s8 := morseReach_isoRule n₀ (u ++ [isoX true (p + 1)])
    ([isoX true p] ++ X ++ [isoX false p, isoX false (p + 1), isoN (p + 2)] ++ v)
    (.r2 (p + 2) true) rfl (by rnf_fits) (by rnf_fits)
  simp only [morseRuleLhs, morseRuleRhs, isoX, isoN, morseKindOut, morseKindIn, ↓reduceIte,
    Bool.false_eq_true, Bool.not_true, List.append_assoc, List.cons_append,
    List.nil_append, Nat.add_sub_cancel] at s1 s2 s3 s4 s5 s6 s7 s8 ⊢
  exact morseReach_trans s1 (morseReach_trans s2 (morseReach_trans s3 (morseReach_trans s4
    (morseReach_trans s5 (morseReach_trans s6 (morseReach_trans s7 s8))))))

/-- Shifting by zero does nothing. -/
private theorem morseShiftWord_zero_roundNF (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- The frame lemma with two idle strands on the right (no shift). -/
private theorem morseReach_frameR_roundNF (n n₀ : ℕ) (u v w w' : MorseWord)
    (h : MorseReach n w w') (hfit : morseFits n w = true) (hu : morseOut n₀ u = n + 2) :
    MorseReach n₀ (u ++ w ++ v) (u ++ w' ++ v) := by
  have h' := morseReach_frame n n₀ 0 2 u v w w' h hfit (by rw [hu]; ring)
  rwa [morseShiftWord_zero_roundNF, morseShiftWord_zero_roundNF] at h'

/-- One more step of a left walk. -/
private theorem morseWalkL_succ_roundNF (s : Bool) (p j : ℕ) :
    morseWalkL s p (j + 1) = (MorseKind.cross s, p + j) :: morseWalkL s p j := by
  simp [morseWalkL, List.range_succ]

/-- One more step of a left walk, in front of a word. -/
private theorem morseWalkL_succ_append_roundNF (s : Bool) (p j : ℕ) (w : MorseWord) :
    morseWalkL s p (j + 1) ++ w = (MorseKind.cross s, p + j) :: (morseWalkL s p j ++ w) := by
  rw [morseWalkL_succ_roundNF, List.cons_append]

/-- A doubled positive crossing, shifted by one. -/
private theorem morseShiftWord_double_cons_roundNF (k : ℕ) (w : MorseWord) :
    morseShiftWord 1 (morseDouble ((MorseKind.cross true, k) :: w)) =
      [isoX true (2 * k + 2), isoX true (2 * k + 3), isoX true (2 * k + 1),
        isoX true (2 * k + 2)] ++ morseShiftWord 1 (morseDouble w) := by
  simp [morseDouble, morseDoubleLetter, cable, cableGen, morseOfBraid, morseShiftWord,
    shiftLetter, isoX, List.range_succ]

/-- The letters of the double of a word of crossings at positions below `K`. -/
private theorem mem_morseDouble_roundNF {w : MorseWord} {K : ℕ}
    (hw : ∀ a ∈ w, (∃ s, a.1 = MorseKind.cross s) ∧ a.2 < K) :
    ∀ l ∈ morseDouble w, (∃ s, l.1 = MorseKind.cross s) ∧ l.2 ≤ 2 * K := by
  intro l hl
  simp only [morseDouble, List.mem_flatMap] at hl
  obtain ⟨⟨κ, i⟩, ha, hl⟩ := hl
  obtain ⟨⟨s, hs⟩, hi⟩ := hw _ ha
  simp only at hs hi
  subst hs
  cases s <;>
  · simp [morseDoubleLetter, cable, cableGen, morseOfBraid, List.range_succ] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> exact ⟨⟨_, rfl⟩, by simp only; omega⟩

/-- The doubled walk of the conveyor: crossings at the positions `1 … 2j + 1`. -/
private theorem mem_walk_roundNF (j : ℕ) :
    ∀ l ∈ morseShiftWord 1 (morseDouble (morseWalkL true 0 j)),
      (∃ s, l.1 = MorseKind.cross s) ∧ l.2 ≤ 2 * j + 1 := by
  intro l hl
  simp only [morseShiftWord, List.mem_map] at hl
  obtain ⟨a, ha, rfl⟩ := hl
  have := mem_morseDouble_roundNF (K := j) (fun b hb ↦ by
    simp only [morseWalkL, List.mem_map, List.mem_reverse, List.mem_range] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact ⟨⟨_, rfl⟩, by simp only; omega⟩) a ha
  exact ⟨this.1, by simp only [shiftLetter]; omega⟩

/-- The local step of round `0`: a cup whose left leg makes an excursion over two strands to a
band `X` becomes a cup visiting `X`, followed by a doubled negative crossing. -/
private theorem morseReach_r0Local_roundNF (n₀ p : ℕ) (u X v : MorseWord)
    (hXc : ∀ l ∈ X, ∃ s, l.1 = MorseKind.cross s) (hXp : ∀ l ∈ X, l.2 + 1 ≤ p)
    (hm : p + 2 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ [isoU (p + 2), isoX true (p + 1), isoX true p] ++ X ++
        [isoX false p, isoX false (p + 1)] ++ v)
      (u ++ [isoU p] ++ X ++
        [isoX false (p + 1), isoX false p, isoX false (p + 2), isoX false (p + 1)] ++ v) := by
  have hXf : ∀ n, p + 1 ≤ n → morseFits n X = true := fun n hn ↦
    morseFits_of_cross n X hXc fun l hl ↦ by have := hXp l hl; omega
  set m := morseOut n₀ u with hmdef
  have t1 := morseReach_isoRule_back_roundNF n₀ u
    ([isoX true (p + 1), isoX true p] ++ X ++ [isoX false p, isoX false (p + 1)] ++ v)
    (.cupSlide (p + 1) false false) rfl (by rnf_fits) (by rnf_fits)
  have t2 := morseReach_isoRule_back_roundNF n₀ u
    ([isoX false (p + 2), isoX false (p + 1), isoX true (p + 1), isoX true p] ++ X ++
      [isoX false p, isoX false (p + 1)] ++ v)
    (.cupSlide p false false) rfl (by rnf_fits) (by rnf_fits)
  have t3 := morseReach_isoRule n₀ (u ++ [isoU p, isoX false (p + 1), isoX false p,
      isoX false (p + 2)]) ([isoX true p] ++ X ++ [isoX false p, isoX false (p + 1)] ++ v)
    (.r2 (p + 1) false) rfl (by rnf_fits) (by rnf_fits)
  have t4 := morseReach_isoRule_back_roundNF n₀ (u ++ [isoU p, isoX false (p + 1), isoX false p])
    (X ++ [isoX false p, isoX false (p + 1)] ++ v)
    (.exch (isoX true p) (isoX false (p + 2))) (by simp [morseRuleOk, isoX, morseKindIn])
    (by rnf_fits) (by rnf_fits)
  have t5 := morseReach_isoRule n₀ (u ++ [isoU p, isoX false (p + 1)])
    ([isoX false (p + 2)] ++ X ++ [isoX false p, isoX false (p + 1)] ++ v)
    (.r2 p false) rfl (by rnf_fits) (by rnf_fits)
  have t6 := morseReach_comm n₀ (u ++ [isoU p, isoX false (p + 1)]) X [isoX false (p + 2)]
    ([isoX false p, isoX false (p + 1)] ++ v) hXc
    (fun b hb a ha ↦ by
      simp only [List.mem_singleton] at ha
      subst ha
      have := hXp b hb
      simp only [isoX]
      omega)
    (by
      rw [morseFits_append, hXf _ (by rnf_fits)]
      rnf_fits)
  have t7 := morseReach_isoRule_back_roundNF n₀ (u ++ [isoU p, isoX false (p + 1)] ++ X)
    ([isoX false (p + 1)] ++ v)
    (.exch (isoX false p) (isoX false (p + 2))) (by simp [morseRuleOk, isoX, morseKindIn])
    (by rw [morseOut_append, morseOut_of_cross _ X hXc]; rnf_fits)
    (by rw [morseOut_append, morseOut_of_cross _ X hXc]; rnf_fits)
  have t8 := morseReach_comm n₀ (u ++ [isoU p]) X [isoX false (p + 1)]
    ([isoX false p, isoX false (p + 2), isoX false (p + 1)] ++ v) hXc
    (fun b hb a ha ↦ by
      simp only [List.mem_singleton] at ha
      subst ha
      have := hXp b hb
      simp only [isoX]
      omega)
    (by
      rw [morseFits_append, hXf _ (by rnf_fits)]
      rnf_fits)
  simp only [morseRuleLhs, morseRuleRhs, isoX, isoU, morseKindOut, morseKindIn, ↓reduceIte,
    Bool.false_eq_true, Bool.not_false, List.append_assoc, List.cons_append,
    List.nil_append, Nat.add_assoc, Nat.reduceAdd] at t1 t2 t3 t4 t5 t6 t7 t8 ⊢
  exact morseReach_trans t1 (morseReach_trans t2 (morseReach_trans t3 (morseReach_trans t4
    (morseReach_trans t5 (morseReach_trans t6 (morseReach_trans t7 t8))))))

/-- The doubled `cupSlide`: a doubled cup passes a doubled crossing (16 moves). -/
private theorem morseReach_dblCupSlide_roundNF :
    MorseReach 2 [isoU 0, isoU 1, isoX false 3, isoX false 2, isoX false 4, isoX false 3]
      [isoU 2, isoU 3, isoX true 1, isoX true 2, isoX true 0, isoX true 1] :=
  ⟨[(1, .exch (.cup, 1) (.cross false, 1), false), (2, .r2 0 false, true),
    (0, .cupSlide 0 false false, false), (3, .exch (.cross false, 2) (.cross false, 4), false),
    (2, .exch (.cup, 1) (.cross false, 2), false),
    (1, .exch (.cross true, 0) (.cross false, 2), false),
    (2, .r2 1 false, true), (0, .cupSlide 1 false false, false), (6, .r2 1 false, true),
    (5, .exch (.cross false, 1) (.cross false, 3), true), (3, .cupSlide 1 false false, false),
    (2, .exch (.cross true, 0) (.cup, 2), false),
    (3, .exch (.cross true, 0) (.cross false, 3), false),
    (4, .r2 2 false, true), (2, .cupSlide 2 false false, false),
    (1, .exch (.cross true, 1) (.cup, 3), false)], by decide⟩

/-- A doubled cup, shifted by one. -/
private theorem morseShiftWord_double_cup_roundNF (k : ℕ) (w : MorseWord) :
    morseShiftWord 1 (morseDouble ([isoU k] ++ w)) =
      [isoU (2 * k + 1), isoU (2 * k + 2)] ++ morseShiftWord 1 (morseDouble w) := by
  simp [morseDouble, morseDoubleLetter, morseShiftWord, shiftLetter, isoU]

/-- The round normal form, indexed by `j = r - 1`. -/
private theorem morseReach_roundNF_aux (j : ℕ) :
    MorseReach (2 * j + 3) ([isoU 1] ++ isoBand 1 (2 * j + 3) true ++ [isoN (2 * j + 3)])
      (morseShiftWord 1 (morseDouble (morseWalkL true 0 j)) ++ isoCurlL true 2) := by
  induction j with
  | zero => exact morseReach_isoMacroDEC
  | succ j ih =>
    have hb : isoBand 1 (2 * j + 5) true = [isoX true (2 * j + 4), isoX true (2 * j + 3)] ++
        isoBand 1 (2 * j + 3) true ++ [isoX false (2 * j + 3), isoX false (2 * j + 4)] := by
      rw [show 2 * j + 5 = (2 * j + 4) + 1 by ring, isoBand_peel_right 1 _ (by omega),
        isoBand_peel_right 1 _ (by omega)]
      simp
    have s1 := morseReach_peel_roundNF (2 * (j + 1) + 3) (2 * j + 3) [isoU 1]
      (isoBand 1 (2 * j + 3) true) [] (fun _ hl ↦ (mem_isoBand hl).1)
      (fun _ hl ↦ by obtain ⟨-, h1, h2⟩ := mem_isoBand hl; omega) (by rnf_fits)
    have s2 := (morseReach_isoCupSweep (2 * (j + 1) + 3) 1 []
      [isoX true (2 * j + 2), isoX true (2 * j + 3), isoX true (2 * j + 1),
        isoX true (2 * j + 2)] (isoBand 1 (2 * j + 3) true ++ [isoN (2 * j + 3)])
      (by simp [isoX]) (by rnf_fits))
    have s3 := morseReach_frameR_roundNF (2 * j + 3) (2 * (j + 1) + 3)
      [isoX true (2 * j + 2), isoX true (2 * j + 3), isoX true (2 * j + 1),
        isoX true (2 * j + 2)] [] _ _ ih
      (by
        rw [morseFits_append, morseFits_append, morseOut_append, morseOut_isoBand,
          morseFits_isoBand_of_le (by omega) (by rnf_fits)]
        rnf_fits)
      (by rnf_fits)
    rw [show 2 * (j + 1) + 3 = 2 * j + 5 by ring] at s1 s2 s3 ⊢
    rw [hb, morseWalkL_succ_roundNF, morseShiftWord_double_cons_roundNF]
    simp only [morseShiftWord, List.map_cons, List.map_nil, shiftLetter, isoX, isoN, isoU,
      List.append_assoc, List.cons_append, List.nil_append, List.append_nil, Nat.add_assoc,
      Nat.reduceAdd, Nat.zero_add] at s1 s2 s3 ⊢
    exact morseReach_trans s1 (morseReach_trans s2 s3)

/-- The normal form of the last round, indexed by `j = r - 1`. -/
private theorem morseReach_lastNF_aux (j : ℕ) :
    MorseReach (2 * j + 5) (isoBand 1 (2 * j + 3) true ++ [isoN (2 * j + 3), isoN 1])
      (phaseTwoMacroA_rhs ++
        morseShiftWord 1 (morseDouble (morseWalkL true 1 j ++ [isoN 0]))) := by
  induction j with
  | zero => exact morseReach_isoMacroRD
  | succ j ih =>
    have hb : isoBand 1 (2 * j + 5) true = [isoX true (2 * j + 4), isoX true (2 * j + 3)] ++
        isoBand 1 (2 * j + 3) true ++ [isoX false (2 * j + 3), isoX false (2 * j + 4)] := by
      rw [show 2 * j + 5 = (2 * j + 4) + 1 by ring, isoBand_peel_right 1 _ (by omega),
        isoBand_peel_right 1 _ (by omega)]
      simp
    set T := morseShiftWord 1 (morseDouble (morseWalkL true 1 j ++ [isoN 0])) with hT
    have s1 := morseReach_peel_roundNF (2 * j + 7) (2 * j + 3) []
      (isoBand 1 (2 * j + 3) true) [isoN 1] (fun _ hl ↦ (mem_isoBand hl).1)
      (fun _ hl ↦ by obtain ⟨-, h1, h2⟩ := mem_isoBand hl; omega) (by rnf_fits)
    have s2 := morseReach_frameR_roundNF (2 * j + 5) (2 * j + 7) (dblPos_roundNF (2 * j + 3)) []
      _ _ ih
      (by
        rw [morseFits_append, morseOut_isoBand, morseFits_isoBand_of_le (by omega) (by omega)]
        rnf_fits)
      (by rnf_fits)
    have s3 := morseReach_comm (2 * j + 7) [] [isoX false 1, isoX false 1]
      (dblPos_roundNF (2 * j + 3))
      ([isoU 2, isoX false 3, isoN 2] ++ T) (by simp [isoX])
      (by simp [isoX, dblPos_roundNF]) (by rnf_fits)
    have s4 := morseReach_symm (morseReach_isoCupSweep (2 * j + 7) 2
      [isoX false 1, isoX false 1] (dblPos_roundNF (2 * j + 3)) ([isoX false 3, isoN 2] ++ T)
      (by simp [isoX, dblPos_roundNF])
      (by rnf_fits))
    have s5 := morseReach_comm (2 * j + 7) [isoX false 1, isoX false 1, isoU 2] [isoX false 3]
      (morseShiftWord 2 (dblPos_roundNF (2 * j + 3))) ([isoN 2] ++ T) (by simp [isoX])
      (by simp [isoX, dblPos_roundNF, morseShiftWord, shiftLetter]) (by rnf_fits)
    have s6 := morseReach_isoCapSweep (2 * j + 7) 2 [isoX false 1, isoX false 1, isoU 2,
      isoX false 3] (dblPos_roundNF (2 * j + 3)) T (by simp [isoX, dblPos_roundNF]) (by rnf_fits)
    rw [show 2 * (j + 1) + 5 = 2 * j + 7 by ring, show 2 * (j + 1) + 3 = 2 * j + 5 by ring, hb,
      morseWalkL_succ_append_roundNF, Nat.add_comm 1 j, morseShiftWord_double_cons_roundNF, ← hT]
    simp only [phaseTwoMacroA_rhs, dblPos_roundNF, morseShiftWord, List.map_cons, List.map_nil,
      shiftLetter,
      isoX, isoN, isoU, List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
      Nat.add_assoc, Nat.reduceAdd, Nat.mul_add, Nat.mul_one] at s1 s2 s3 s4 s5 s6 ⊢
    exact morseReach_trans s1 (morseReach_trans s2 (morseReach_trans s3 (morseReach_trans s4
      (morseReach_trans s5 s6))))

/-- The normal form of round `0`, indexed by `j = r - 1`. -/
private theorem morseReach_r0NF_aux (j : ℕ) :
    MorseReach (2 * j + 1) ([isoU 1, isoU (2 * j + 3)] ++ isoBand 1 (2 * j + 3) true)
      (morseShiftWord 1 (morseDouble ([isoU j] ++ morseWalkL true 0 j)) ++ isoCurlL true 2) := by
  induction j with
  | zero => exact morseReach_isoMacroLC
  | succ j ih =>
    have hb : isoBand 1 (2 * j + 5) true = [isoX true (2 * j + 4), isoX true (2 * j + 3)] ++
        isoBand 1 (2 * j + 3) true ++ [isoX false (2 * j + 3), isoX false (2 * j + 4)] := by
      rw [show 2 * j + 5 = (2 * j + 4) + 1 by ring, isoBand_peel_right 1 _ (by omega),
        isoBand_peel_right 1 _ (by omega)]
      simp
    set W := morseShiftWord 1 (morseDouble (morseWalkL true 0 j)) with hW
    have hWc : ∀ l ∈ W, ∃ s, l.1 = MorseKind.cross s := fun l hl ↦
      (mem_walk_roundNF j l hl).1
    have hWo : ∀ n, morseOut n W = n := fun n ↦ morseOut_of_cross n W hWc
    have s1 := morseReach_r0Local_roundNF (2 * j + 3) (2 * j + 3) [isoU 1]
      (isoBand 1 (2 * j + 3) true) [] (fun _ hl ↦ (mem_isoBand hl).1)
      (fun _ hl ↦ by obtain ⟨-, h1, h2⟩ := mem_isoBand hl; omega) (by rnf_fits)
    have s2 := morseReach_frameR_roundNF (2 * j + 1) (2 * j + 3) [] (dblNeg_roundNF (2 * j + 3))
      _ _ ih
      (by
        rw [morseFits_append, morseFits_isoBand_of_le (by omega) (by rnf_fits)]
        rnf_fits)
      (by rnf_fits)
    rw [morseShiftWord_double_cup_roundNF, ← hW] at s2
    have s3 := morseReach_symm (morseReach_isoCapSweep (2 * j + 3) 2
      ([isoU (2 * j + 1), isoU (2 * j + 2)] ++ W ++ [isoU 2, isoX true 3])
      (dblNeg_roundNF (2 * j + 3)) []
      (by simp [isoX, dblNeg_roundNF]) (by rw [morseOut_append, morseOut_append, hWo]; rnf_fits))
    have s4 := morseReach_symm (morseReach_comm (2 * j + 3)
      ([isoU (2 * j + 1), isoU (2 * j + 2)] ++ W ++ [isoU 2]) [isoX true 3]
      (morseShiftWord 2 (dblNeg_roundNF (2 * j + 3)))
      [isoN 2] (by simp [isoX]) (by simp [isoX, dblNeg_roundNF, morseShiftWord, shiftLetter])
      (by rw [morseOut_append, morseOut_append, hWo]; rnf_fits))
    have s5 := morseReach_isoCupSweep (2 * j + 3) 2 ([isoU (2 * j + 1), isoU (2 * j + 2)] ++ W)
      (dblNeg_roundNF (2 * j + 3)) [isoX true 3, isoN 2] (by simp [isoX, dblNeg_roundNF])
      (by rw [morseOut_append, hWo]; rnf_fits)
    have s6 := morseReach_symm (morseReach_comm (2 * j + 3) [isoU (2 * j + 1), isoU (2 * j + 2)]
      W (dblNeg_roundNF (2 * j + 3)) (isoCurlL true 2) hWc
      (fun b hb a ha ↦ by
        have := (mem_walk_roundNF j b hb).2
        simp only [dblNeg_roundNF, isoX, List.mem_cons, List.mem_nil_iff, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> simp only <;> omega)
      (by
        rw [morseFits_append, morseFits_of_cross _ W hWc fun l hl ↦ by
          have := (mem_walk_roundNF j l hl).2
          simp only [dblNeg_roundNF, morseOut, morseLetterOut, isoU, isoX, morseKindOut,
            morseKindIn]
          omega]
        rnf_fits))
    have s7 := morseReach_frame 2 (2 * j + 3) (2 * j + 1) 0 [] (W ++ isoCurlL true 2) _ _
      morseReach_dblCupSlide_roundNF (by decide) (by simp [morseOut])
    have e1 : morseShiftWord (2 * j + 1)
        [isoU 0, isoU 1, isoX false 3, isoX false 2, isoX false 4, isoX false 3] =
        [isoU (2 * j + 1), isoU (2 * j + 2)] ++ dblNeg_roundNF (2 * j + 3) := by
      simp only [morseShiftWord, List.map_cons, List.map_nil, shiftLetter, isoU, isoX,
        dblNeg_roundNF, List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq,
        true_and, and_true]
      omega
    have e2 : morseShiftWord (2 * j + 1)
        [isoU 2, isoU 3, isoX true 1, isoX true 2, isoX true 0, isoX true 1] =
        [isoU (2 * j + 3), isoU (2 * j + 4), isoX true (2 * j + 2), isoX true (2 * j + 3),
          isoX true (2 * j + 1), isoX true (2 * j + 2)] := by
      simp only [morseShiftWord, List.map_cons, List.map_nil, shiftLetter, isoU, isoX,
        List.cons.injEq, Prod.mk.injEq, true_and, and_true]
      omega
    rw [e1, e2] at s7
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, show 2 * (j + 1) + 3 = 2 * j + 5 by ring, hb,
      morseShiftWord_double_cup_roundNF, morseWalkL_succ_roundNF,
      morseShiftWord_double_cons_roundNF, ← hW]
    simp only [isoCurlL, dblNeg_roundNF, morseShiftWord, List.map_cons, List.map_nil, shiftLetter,
      isoX, isoN, isoU, List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
      Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.mul_add, Nat.mul_one]
      at s1 s2 s3 s4 s5 s6 s7 ⊢
    exact morseReach_trans s1 (morseReach_trans s2 (morseReach_trans s3 (morseReach_trans s4
      (morseReach_trans s5 (morseReach_trans s6 s7)))))

/-- Normal form of a round. -/
theorem morseReach_isoRoundNF (r : ℕ) (hr : 2 ≤ r) :
    MorseReach (2 * r + 1) ([isoU 1] ++ isoBand 1 (1 + 2 * r) true ++ [isoN (1 + 2 * r)])
      (morseShiftWord 1 (morseDouble (morseWalkL true 0 (r - 1))) ++ isoCurlL true 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, show 1 + 2 * (j + 1) = 2 * j + 3 by ring,
    Nat.add_sub_cancel]
  exact morseReach_roundNF_aux j

/-- Normal form of round `0`. -/
theorem morseReach_isoR0NF (r : ℕ) (hr : 2 ≤ r) :
    MorseReach (2 * r - 1) ([isoU 1, isoU (1 + 2 * r)] ++ isoBand 1 (1 + 2 * r) true)
      (morseShiftWord 1 (morseDouble ([isoU (r - 1)] ++ morseWalkL true 0 (r - 1))) ++
        isoCurlL true 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 1 + 2 * (j + 1) = 2 * j + 3 by ring,
    Nat.add_sub_cancel]
  exact morseReach_r0NF_aux j

/-- Normal form of the last round. -/
theorem morseReach_isoLastNF (r : ℕ) (hr : 2 ≤ r) :
    MorseReach (2 * r + 3) (isoBand 1 (1 + 2 * r) true ++ [isoN (1 + 2 * r), isoN 1])
      (phaseTwoMacroA_rhs ++
        morseShiftWord 1 (morseDouble (morseWalkL true 1 (r - 1) ++ [isoN 0]))) := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  rw [show 2 * (j + 1) + 3 = 2 * j + 5 by ring, show 1 + 2 * (j + 1) = 2 * j + 3 by ring,
    Nat.add_sub_cancel]
  exact morseReach_lastNF_aux j

end AJConjecture
