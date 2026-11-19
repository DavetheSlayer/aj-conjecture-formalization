import Mathlib
import AJFamily.Skein.MorseFrame
import AJConjecture.SkeinMorseCheck
import AJConjecture.SkeinMorseOpBasic
import AJConjecture.SkeinMorseRuleSound

/-!
# Soundness of the checker

A list of moves accepted by `AJConjecture.morseApplyAll` does not change the thick operator of the
word, for any thickness. This is what turns an isotopy of thin diagrams, checked by a kernel
computation that does not mention the thickness, into an identity of operators on bundles.

Proof of `morseOp_eq_of_morseApply`: write the word as `u ++ src ++ v` with `u = w.take pos`
(`List.take_append_drop`, `List.isPrefixOf_iff_prefix`), split the operator with
`AJConjecture.morseOp_append`, replace the middle factor with `AJConjecture.morseRuleSound` at
`n = morseOut n₀ u`, `N = morseThickOut c (c * n₀) u` — equal to `c * n` by
`AJConjecture.morseThickOut_eq` when `u` fits, and when `u` does not fit both sides are `0` — and
use that the two sides of a rule end on the same number of strands. The list version is an
induction on the list.
-/

namespace AJConjecture

/-- A placement that does not fit is `0`. -/
private theorem skPlace_eq_zero_of_not_le_checkSound (n n' i : ℕ) {k l : ℕ} (A : SkMat k l)
    (h : ¬ i + k ≤ n) : skPlace n n' i A = 0 := by
  ext a b
  simp only [skPlace, Matrix.of_apply, Matrix.zero_apply]
  rw [dite_eq_right fun h' ↦ h h'.1]

/-- The operator of a letter that does not fit on `n` strands is `0`, for a positive
thickness. -/
private theorem morseLetterOp_eq_zero_checkSound (c : ℕ) (hc : 0 < c) (l : MorseLetter)
    (n M : ℕ) (hl : ¬ l.2 + morseKindIn l.1 ≤ n) : morseLetterOp c l (c * n) M = 0 := by
  obtain ⟨k, i⟩ := l
  dsimp only at hl
  have hlt : c * n < c * (i + morseKindIn k) := Nat.mul_lt_mul_of_pos_left (by omega) hc
  rw [Nat.mul_add] at hlt
  cases k with
  | cup =>
    simp only [morseKindIn] at hlt hl
    exact skPlace_eq_zero_of_not_le_checkSound _ _ _ _ (by dsimp only; omega)
  | cap =>
    simp only [morseKindIn] at hlt hl
    exact skPlace_eq_zero_of_not_le_checkSound _ _ _ _ (by dsimp only; omega)
  | cross s =>
    simp only [morseKindIn] at hlt hl
    exact skPlace_eq_zero_of_not_le_checkSound _ _ _ _ (by dsimp only; omega)

/-- The operator of a word that does not fit on `n` strands is `0`, for a positive thickness. -/
private theorem morseOp_eq_zero_of_not_fits_checkSound (c : ℕ) (hc : 0 < c) (u : MorseWord) :
    ∀ n N M : ℕ, N = c * n → morseFits n u = false → morseOp c u N M = 0 := by
  induction u with
  | nil =>
    intro n N M _ h
    simp only [morseFits, Bool.true_eq_false] at h
  | cons l u ih =>
    intro n N M hN h
    subst hN
    rw [morseOp]
    by_cases hl : l.2 + morseKindIn l.1 ≤ n
    · simp only [morseFits, hl, decide_true, Bool.true_and] at h
      have hle : morseKindIn l.1 ≤ n := by omega
      rw [ih (morseLetterOut n l) _ M _ h, Matrix.mul_zero]
      rw [morseLetterOut, Nat.mul_sub, Nat.mul_add]
    · rw [morseLetterOp_eq_zero_checkSound c hc l n _ hl, Matrix.zero_mul]

/-- For the thickness `0` every word ends on `0` tensor factors. -/
private theorem morseThickOut_zero_checkSound (u : MorseWord) : morseThickOut 0 0 u = 0 := by
  induction u with
  | nil => rfl
  | cons l u ih =>
    rw [morseThickOut]
    simpa only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero] using ih

/-- Either a word ends on `c` times its number of strands, or its operator is `0`. -/
private theorem morseThickOut_eq_or_morseOp_eq_zero_checkSound (c n : ℕ) (u : MorseWord) :
    morseThickOut c (c * n) u = c * morseOut n u ∨ ∀ M : ℕ, morseOp c u (c * n) M = 0 := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    left
    rw [Nat.zero_mul, Nat.zero_mul, morseThickOut_zero_checkSound]
  · by_cases hu : morseFits n u = true
    · exact Or.inl (morseThickOut_eq c n u hu)
    · exact Or.inr fun M ↦
        morseOp_eq_zero_of_not_fits_checkSound c hc u n _ M rfl (Bool.not_eq_true _ ▸ hu)

/-- The two sides of a rule end on the same number of strands. -/
private theorem morseOut_morseRuleLhs_eq_checkSound (r : MorseRule) (n : ℕ)
    (hl : morseFits n (morseRuleLhs r) = true) (hr : morseFits n (morseRuleRhs r) = true) :
    morseOut n (morseRuleLhs r) = morseOut n (morseRuleRhs r) := by
  cases r with
  | zig i r =>
    cases r <;> simp only [morseRuleLhs, morseRuleRhs, morseOut, morseLetterOut, morseKindOut,
      morseKindIn, Bool.false_eq_true, ite_false, ite_true] <;> omega
  | r2 i s =>
    simp only [morseRuleLhs, morseRuleRhs, morseOut, morseLetterOut, morseKindOut, morseKindIn]
    omega
  | r3 i s =>
    simp only [morseRuleLhs, morseRuleRhs, morseOut, morseLetterOut, morseKindOut, morseKindIn]
  | cupSlide i s r =>
    cases r <;> simp only [morseRuleLhs, morseRuleRhs, morseOut, morseLetterOut, morseKindOut,
      morseKindIn, Bool.false_eq_true, ite_false, ite_true] <;> omega
  | capSlide i s r =>
    cases r <;> simp only [morseRuleLhs, morseRuleRhs, morseOut, morseLetterOut, morseKindOut,
      morseKindIn, morseFits_cons, Bool.false_eq_true, ite_false,
      ite_true] at hl hr ⊢ <;> omega
  | kink i s =>
    simp only [morseRuleLhs, morseRuleRhs, morseOut, morseLetterOut, morseKindOut, morseKindIn]
    omega
  | exch a b =>
    obtain ⟨ka, ia⟩ := a
    obtain ⟨kb, ib⟩ := b
    cases ka <;> cases kb <;> simp only [morseRuleLhs, morseRuleRhs, morseOut, morseLetterOut,
      morseKindOut, morseKindIn, morseFits_cons] at hl hr ⊢ <;> omega

/-- Replacing a factor of a word by a word with the same operator. -/
private theorem morseOp_append_congr_checkSound (c n₀ N' : ℕ) (u x y v : MorseWord)
    (hx : morseFits (morseOut n₀ u) x = true) (hy : morseFits (morseOut n₀ u) y = true)
    (hout : morseOut (morseOut n₀ u) x = morseOut (morseOut n₀ u) y)
    (hop : ∀ P : ℕ, morseOp c x (c * morseOut n₀ u) P = morseOp c y (c * morseOut n₀ u) P) :
    morseOp c (u ++ (x ++ v)) (c * n₀) N' = morseOp c (u ++ (y ++ v)) (c * n₀) N' := by
  rw [morseOp_append, morseOp_append c u]
  rcases morseThickOut_eq_or_morseOp_eq_zero_checkSound c n₀ u with hM | hM
  · rw [hM, morseOp_append, morseOp_append c y, morseThickOut_eq c _ x hx,
      morseThickOut_eq c _ y hy, hout, hop]
  · rw [hM, Matrix.zero_mul, Matrix.zero_mul]

/-- One accepted move preserves the thick operator. -/
theorem morseOp_eq_of_morseApply (c n₀ N N' : ℕ) (hN : N = c * n₀) (w w' : MorseWord)
    (mv : MorseMove) (h : morseApply n₀ w mv = some w') :
    morseOp c w N N' = morseOp c w' N N' := by
  subst hN
  obtain ⟨pos, r, b⟩ := mv
  have hsound := morseRuleSound r c (morseOut n₀ (w.take pos)) (c * morseOut n₀ (w.take pos))
  cases b
  · simp only [morseApply, Bool.false_eq_true, ite_false] at h
    split at h
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨⟨-, hok⟩, hpre⟩, hfs⟩, hfd⟩ := hcond
      rw [Option.some.injEq] at h
      subst h
      obtain ⟨v, hv⟩ := List.isPrefixOf_iff_prefix.mp hpre
      have hw : w = w.take pos ++ (morseRuleLhs r ++ v) := by rw [hv, List.take_append_drop]
      rw [← hv, List.drop_left, List.append_assoc]
      conv_lhs => rw [hw]
      exact morseOp_append_congr_checkSound c n₀ N' _ _ _ v hfs hfd
        (morseOut_morseRuleLhs_eq_checkSound r _ hfs hfd) fun P ↦ hsound P rfl hok hfs hfd
    · simp only [reduceCtorEq] at h
  · simp only [morseApply, ite_true] at h
    split at h
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨⟨-, hok⟩, hpre⟩, hfs⟩, hfd⟩ := hcond
      rw [Option.some.injEq] at h
      subst h
      obtain ⟨v, hv⟩ := List.isPrefixOf_iff_prefix.mp hpre
      have hw : w = w.take pos ++ (morseRuleRhs r ++ v) := by rw [hv, List.take_append_drop]
      rw [← hv, List.drop_left, List.append_assoc]
      conv_lhs => rw [hw]
      exact morseOp_append_congr_checkSound c n₀ N' _ _ _ v hfs hfd
        (morseOut_morseRuleLhs_eq_checkSound r _ hfd hfs).symm
        fun P ↦ (hsound P rfl hok hfd hfs).symm
    · simp only [reduceCtorEq] at h

/-- A list of accepted moves preserves the thick operator. -/
theorem morseOp_eq_of_morseApplyAll (c n₀ N N' : ℕ) (hN : N = c * n₀) (w w' : MorseWord)
    (mvs : List MorseMove) (h : morseApplyAll n₀ w mvs = some w') :
    morseOp c w N N' = morseOp c w' N N' := by
  induction mvs generalizing w with
  | nil =>
    rw [morseApplyAll, Option.some.injEq] at h
    rw [h]
  | cons mv mvs ih =>
    rw [morseApplyAll, Option.bind_eq_some_iff] at h
    obtain ⟨w₁, h₁, h₂⟩ := h
    rw [morseOp_eq_of_morseApply c n₀ N N' hN w w₁ mv h₁]
    exact ih w₁ h₂

end AJConjecture
