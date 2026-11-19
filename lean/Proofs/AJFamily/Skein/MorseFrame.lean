import Mathlib
import AJFamily.Skein.MorseReach
import AJFamily.Skein.MorseShift

/-!
# The frame lemma

`morseReach_frame`: a reachability `MorseReach n w w'`, with `w` fitting on `n` strands, transports
into any word `u ++ morseShiftWord d w ++ v` whose prefix `u` ends on `d + n + e` strands. This is
how the fixed macros of the isotopy are applied inside the large words.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The arity of a concatenation. -/
private theorem morseOut_append_frame (n : ℕ) (u v : MorseWord) :
    morseOut n (u ++ v) = morseOut (morseOut n u) v := by
  induction u generalizing n with
  | nil => rfl
  | cons l u ih => exact ih _

/-- Fitting of a concatenation. -/
private theorem morseFits_append_frame (n : ℕ) (u v : MorseWord) :
    morseFits n (u ++ v) = (morseFits n u && morseFits (morseOut n u) v) := by
  induction u generalizing n with
  | nil => simp [morseFits, morseOut]
  | cons l u ih => simp only [List.cons_append, morseFits, morseOut, ih, Bool.and_assoc]

/-- Shifting distributes over concatenation. -/
private theorem morseShiftWord_append_frame (d : ℕ) (u v : MorseWord) :
    morseShiftWord d (u ++ v) = morseShiftWord d u ++ morseShiftWord d v :=
  List.map_append

/-- Reachability is reflexive. -/
private theorem morseReach_refl_frame (n : ℕ) (w : MorseWord) : MorseReach n w w := ⟨[], rfl⟩

/-- Fitting of a word with a first letter. -/
theorem morseFits_cons (n : ℕ) (l : MorseLetter) (w : MorseWord) :
    morseFits n (l :: w) = true ↔
      l.2 + morseKindIn l.1 ≤ n ∧ morseFits (morseLetterOut n l) w = true := by
  rw [morseFits, Bool.and_eq_true, decide_eq_true_eq]

/-- A shifted word on extra idle strands on both sides: arity and fitting. -/
theorem morseOut_fits_shift (n d e : ℕ) (x : MorseWord) (h : morseFits n x = true) :
    morseOut (d + n + e) (morseShiftWord d x) = d + morseOut n x + e ∧
      morseFits (d + n + e) (morseShiftWord d x) = true := by
  induction x generalizing n with
  | nil => exact ⟨rfl, rfl⟩
  | cons l x ih =>
    rw [morseFits_cons] at h
    have hl : morseLetterOut (d + n + e) (shiftLetter d l) = d + morseLetterOut n l + e := by
      simp only [morseLetterOut, shiftLetter]
      omega
    have := ih _ h.2
    simp only [morseShiftWord, List.map_cons, morseOut, morseFits_cons] at this ⊢
    rw [hl]
    exact ⟨this.1, by simp only [shiftLetter]; omega, this.2⟩

/-- The sides of a shifted rule are the shifted sides. -/
theorem shiftRule_sides (d : ℕ) (r : MorseRule) (hr : morseRuleOk r = true) :
    morseRuleLhs (shiftRule d r) = morseShiftWord d (morseRuleLhs r) ∧
      morseRuleRhs (shiftRule d r) = morseShiftWord d (morseRuleRhs r) ∧
      morseRuleOk (shiftRule d r) = true := by
  cases r with
  | exch a b =>
    obtain ⟨ka, pa⟩ := a
    obtain ⟨kb, pb⟩ := b
    simp only [morseRuleOk, decide_eq_true_eq] at hr
    simp only [shiftRule, morseRuleLhs, morseRuleRhs, morseRuleOk, morseShiftWord, shiftLetter,
      List.map_cons, List.map_nil, decide_eq_true_eq, List.cons.injEq, Prod.mk.injEq, true_and,
      and_true]
    omega
  | zig i r => cases r <;> simp [shiftRule, morseRuleLhs, morseRuleRhs, morseShiftWord,
      shiftLetter, morseRuleOk] <;> omega
  | r2 i s => simp [shiftRule, morseRuleLhs, morseRuleRhs, morseShiftWord, shiftLetter,
      morseRuleOk]
  | r3 i s =>
    simp only [shiftRule, morseRuleLhs, morseRuleRhs, morseShiftWord, shiftLetter, morseRuleOk,
      List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega
  | cupSlide i s r => cases r <;> simp [shiftRule, morseRuleLhs, morseRuleRhs, morseShiftWord,
      shiftLetter, morseRuleOk] <;> omega
  | capSlide i s r => cases r <;> simp [shiftRule, morseRuleLhs, morseRuleRhs, morseShiftWord,
      shiftLetter, morseRuleOk] <;> omega
  | kink i s =>
    simp only [shiftRule, morseRuleLhs, morseRuleRhs, morseShiftWord, shiftLetter, morseRuleOk,
      List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega

/-- The two sides of a rule have the same arity. -/
theorem morseOut_rule_sides (r : MorseRule) (n : ℕ) (hr : morseRuleOk r = true)
    (hl : morseFits n (morseRuleLhs r) = true) (hrr : morseFits n (morseRuleRhs r) = true) :
    morseOut n (morseRuleLhs r) = morseOut n (morseRuleRhs r) := by
  cases r with
  | exch a b =>
    obtain ⟨ka, pa⟩ := a
    obtain ⟨kb, pb⟩ := b
    simp only [morseRuleLhs, morseRuleRhs, morseFits_cons, morseOut, morseLetterOut]
      at hl hrr ⊢
    cases ka <;> cases kb <;> simp only [morseKindIn, morseKindOut] at hl hrr ⊢ <;> omega
  | zig i r => cases r <;> simp [morseRuleLhs, morseRuleRhs, morseFits_cons, morseOut,
      morseLetterOut, morseKindIn, morseKindOut] at hl hrr ⊢
  | r2 i s => simp [morseRuleLhs, morseRuleRhs, morseFits_cons, morseOut,
      morseLetterOut, morseKindIn, morseKindOut] at hl hrr ⊢
  | r3 i s => simp [morseRuleLhs, morseRuleRhs, morseFits_cons, morseOut,
      morseLetterOut, morseKindIn, morseKindOut] at hl hrr ⊢
  | cupSlide i s r => cases r <;> simp [morseRuleLhs, morseRuleRhs, morseFits_cons, morseOut,
      morseLetterOut, morseKindIn, morseKindOut] at hl hrr ⊢
  | capSlide i s r => cases r <;> simp [morseRuleLhs, morseRuleRhs, morseFits_cons, morseOut,
      morseLetterOut, morseKindIn, morseKindOut] at hl hrr ⊢
  | kink i s => simp [morseRuleLhs, morseRuleRhs, morseFits_cons, morseOut,
      morseLetterOut, morseKindIn, morseKindOut] at hl hrr ⊢

/-- The shape of a word on which a move applies. -/
theorem morseApply_shape (n₀ : ℕ) (w w' : MorseWord) (p : ℕ) (r : MorseRule)
    (bk : Bool) (h : morseApply n₀ w (p, r, bk) = some w') :
    ∃ a rest : MorseWord, a.length = p ∧
      w = a ++ (if bk then morseRuleRhs r else morseRuleLhs r) ++ rest ∧
      w' = a ++ (if bk then morseRuleLhs r else morseRuleRhs r) ++ rest ∧
      morseRuleOk r = true ∧
      morseFits (morseOut n₀ a) (if bk then morseRuleRhs r else morseRuleLhs r) = true ∧
      morseFits (morseOut n₀ a) (if bk then morseRuleLhs r else morseRuleRhs r) = true := by
  cases bk <;> simp only [morseApply, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;>
  · split_ifs at h with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨hp, hok⟩, hpre⟩, hs⟩, hd⟩ := hc
    rw [List.isPrefixOf_iff_prefix] at hpre
    obtain ⟨t, ht⟩ := hpre
    refine ⟨w.take p, t, by simp [hp], ?_, ?_, hok, hs, hd⟩
    · rw [List.append_assoc, ht, List.take_append_drop]
    · rw [← Option.some_inj.mp h, ← ht]
      simp

/-- A move applied at the junction of `a` and `src ++ rest`. -/
theorem morseApply_junction (n₀ : ℕ) (a rest : MorseWord) (r : MorseRule)
    (bk : Bool) (hok : morseRuleOk r = true)
    (hs : morseFits (morseOut n₀ a) (if bk then morseRuleRhs r else morseRuleLhs r) = true)
    (hd : morseFits (morseOut n₀ a) (if bk then morseRuleLhs r else morseRuleRhs r) = true) :
    morseApply n₀ (a ++ (if bk then morseRuleRhs r else morseRuleLhs r) ++ rest)
      (a.length, r, bk) =
      some (a ++ (if bk then morseRuleLhs r else morseRuleRhs r) ++ rest) := by
  simp only [morseApply]
  simp [hok, hs, hd]

/-- One move, transported into a frame. -/
private theorem morseApply_shifted_frame (n n₀ d e : ℕ) (u v w w' : MorseWord) (mv : MorseMove)
    (h : morseApply n w mv = some w') (hfit : morseFits n w = true)
    (hu : morseOut n₀ u = d + n + e) :
    MorseReach n₀ (u ++ morseShiftWord d w ++ v) (u ++ morseShiftWord d w' ++ v) ∧
      morseFits n w' = true := by
  obtain ⟨p, r, bk⟩ := mv
  obtain ⟨a, rest, -, rfl, rfl, hok, hs, hd⟩ := morseApply_shape n w w' p r bk h
  obtain ⟨hL, hR, hok'⟩ := shiftRule_sides d r hok
  have hSD : morseOut (morseOut n a) (if bk then morseRuleRhs r else morseRuleLhs r) =
      morseOut (morseOut n a) (if bk then morseRuleLhs r else morseRuleRhs r) := by
    cases bk
    · exact morseOut_rule_sides r _ hok hs hd
    · exact (morseOut_rule_sides r _ hok hd hs).symm
  generalize hS : (if bk then morseRuleRhs r else morseRuleLhs r) = S at hs hfit hSD
  generalize hD : (if bk then morseRuleLhs r else morseRuleRhs r) = D at hd hSD
  have hS' : (if bk then morseRuleRhs (shiftRule d r) else morseRuleLhs (shiftRule d r)) =
      morseShiftWord d S := by
    rw [← hS]
    cases bk <;> simp [hL, hR]
  have hD' : (if bk then morseRuleLhs (shiftRule d r) else morseRuleRhs (shiftRule d r)) =
      morseShiftWord d D := by
    rw [← hD]
    cases bk <;> simp [hL, hR]
  rw [morseFits_append_frame, morseFits_append_frame, Bool.and_eq_true, Bool.and_eq_true,
    morseOut_append_frame] at hfit
  obtain ⟨⟨ha, -⟩, hrest⟩ := hfit
  have hA := morseOut_fits_shift n d e a ha
  have hP : morseOut n₀ (u ++ morseShiftWord d a) = d + morseOut n a + e := by
    rw [morseOut_append_frame, hu, hA.1]
  refine ⟨⟨[((u ++ morseShiftWord d a).length, shiftRule d r, bk)], ?_⟩, ?_⟩
  · have := morseApply_junction n₀ (u ++ morseShiftWord d a) (morseShiftWord d rest ++ v)
      (shiftRule d r) bk hok' (by rw [hS', hP]; exact (morseOut_fits_shift _ d e S hs).2)
      (by rw [hD', hP]; exact (morseOut_fits_shift _ d e D hd).2)
    rw [hS', hD'] at this
    simp only [morseApplyAll, morseShiftWord_append_frame, List.append_assoc] at this ⊢
    rw [this]
    rfl
  · rw [morseFits_append_frame, morseFits_append_frame, ha, hd, morseOut_append_frame, ← hSD,
      hrest]
    rfl

/-- A list of moves, transported into a frame. -/
private theorem morseApplyAll_shifted_frame (n n₀ d e : ℕ) (u v : MorseWord)
    (hu : morseOut n₀ u = d + n + e) (mvs : List MorseMove) :
    ∀ w w' : MorseWord, morseApplyAll n w mvs = some w' → morseFits n w = true →
      MorseReach n₀ (u ++ morseShiftWord d w ++ v) (u ++ morseShiftWord d w' ++ v) := by
  induction mvs with
  | nil =>
    intro w w' h _
    simp only [morseApplyAll, Option.some.injEq] at h
    subst h
    exact morseReach_refl_frame _ _
  | cons mv mvs ih =>
    intro w w' h hfit
    simp only [morseApplyAll] at h
    cases h₁ : morseApply n w mv with
    | none => simp [h₁] at h
    | some w₁ =>
      rw [h₁, Option.bind_some] at h
      obtain ⟨h2, hf⟩ := morseApply_shifted_frame n n₀ d e u v w w₁ mv h₁ hfit hu
      exact morseReach_trans h2 (ih w₁ w' h hf)

theorem morseReach_frame (n n₀ d e : ℕ) (u v w w' : MorseWord) (h : MorseReach n w w')
    (hfit : morseFits n w = true) (hu : morseOut n₀ u = d + n + e) :
    MorseReach n₀ (u ++ morseShiftWord d w ++ v) (u ++ morseShiftWord d w' ++ v) := by
  obtain ⟨mvs, hm⟩ := h
  exact morseApplyAll_shifted_frame n n₀ d e u v hu mvs w w' hm hfit

end AJConjecture
