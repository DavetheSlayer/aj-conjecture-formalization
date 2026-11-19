import Mathlib
import AJHandoff.TorusKnot.PairKIsoDoubleRules
import AJFamily.Skein.MorseFrame

/-!
# Doubling a reachability (generic)

`morseReach_morseDouble`: if `w` reaches `w'` on `n` strands, the blackboard doubles reach each
other on `2n` strands. Induction on the move list: a move replaces `x S y` by `x S' y`; the double
is `morseDouble x · morseDouble S · morseDouble y`, `morseDouble x` ends on `2 · morseOut n x`
strands, and `morseReach_morseDouble_rule` applies with `morseReach_frame`. This lifts the
one-strand isotopy of the companion (`PairKIsoCompanion`) to the band without doubling any move
by hand.
-/

namespace AJConjecture

/-- Doubling distributes over concatenation. -/
private theorem morseDouble_append_dbl (u v : MorseWord) :
    morseDouble (u ++ v) = morseDouble u ++ morseDouble v :=
  List.flatMap_append

/-- The double of a fitting letter fits on twice the strands and doubles their number. -/
private theorem morseDoubleLetter_fits_dbl (n : ℕ) (l : MorseLetter)
    (h : l.2 + morseKindIn l.1 ≤ n) :
    morseFits (2 * n) (morseDoubleLetter l) = true ∧
      morseOut (2 * n) (morseDoubleLetter l) = 2 * morseLetterOut n l := by
  obtain ⟨k, i⟩ := l
  cases k with
  | cup =>
    simp only [morseKindIn] at h
    simp only [morseDoubleLetter, morseFits, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, Bool.and_true, Bool.and_eq_true]
    exact ⟨⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩, by omega⟩
  | cap =>
    simp only [morseKindIn] at h
    simp only [morseDoubleLetter, morseFits, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, Bool.and_true, Bool.and_eq_true]
    exact ⟨⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩, by omega⟩
  | cross s =>
    simp only [morseKindIn] at h
    cases s <;>
    · simp only [morseDoubleLetter, cable, cableGen, morseOfBraid, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, Bool.false_eq_true, ↓reduceIte,
        show List.range 2 = [0, 1] from rfl, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.map_cons, List.map_nil, List.flatMap_cons, morseFits, morseOut,
        morseLetterOut, morseKindIn, morseKindOut, Bool.and_true, Bool.and_eq_true]
      exact ⟨⟨decide_eq_true (by omega), decide_eq_true (by omega), decide_eq_true (by omega),
        decide_eq_true (by omega)⟩, by omega⟩

/-- The double of a fitting word fits on twice the strands and doubles their number. -/
private theorem morseDouble_fits_dbl :
    ∀ (w : MorseWord) (n : ℕ), morseFits n w = true →
      morseFits (2 * n) (morseDouble w) = true ∧
        morseOut (2 * n) (morseDouble w) = 2 * morseOut n w
  | [], _, _ => ⟨rfl, rfl⟩
  | l :: w, n, h => by
    rw [morseFits_cons] at h
    have hl := morseDoubleLetter_fits_dbl n l h.1
    have hw := morseDouble_fits_dbl w _ h.2
    rw [show morseDouble (l :: w) = morseDoubleLetter l ++ morseDouble w from List.flatMap_cons,
      morseFits_append, morseOut_append, hl.1, hl.2, hw.1, hw.2]
    exact ⟨rfl, rfl⟩

/-- Shifting by zero does nothing. -/
private theorem morseShiftWord_zero_dbl (w : MorseWord) : morseShiftWord 0 w = w := by
  have h : shiftLetter 0 = id := funext fun l ↦ by simp [shiftLetter]
  simp [morseShiftWord, h]

/-- One move preserves fitting. -/
private theorem morseFits_morseApply_dbl (n₀ : ℕ) (w w' : MorseWord) (mv : MorseMove)
    (h : morseApply n₀ w mv = some w') (hw : morseFits n₀ w = true) :
    morseFits n₀ w' = true := by
  obtain ⟨p, r, bk⟩ := mv
  obtain ⟨a, rest, -, rfl, rfl, hok, hs, hd⟩ := morseApply_shape n₀ w w' p r bk h
  have ho : morseOut (morseOut n₀ a) (if bk then morseRuleRhs r else morseRuleLhs r) =
      morseOut (morseOut n₀ a) (if bk then morseRuleLhs r else morseRuleRhs r) := by
    cases bk
    · simp only [Bool.false_eq_true, ↓reduceIte] at hs hd ⊢
      exact morseOut_rule_sides r _ hok hs hd
    · simp only [↓reduceIte] at hs hd ⊢
      exact (morseOut_rule_sides r _ hok hd hs).symm
  rw [morseFits_append, morseFits_append, Bool.and_eq_true, Bool.and_eq_true,
    morseOut_append] at hw ⊢
  rw [← ho]
  exact ⟨⟨hw.1.1, hd⟩, hw.2⟩

/-- One move, doubled. -/
private theorem morseReach_morseDouble_move (n : ℕ) (w w' : MorseWord) (mv : MorseMove)
    (h : morseApply n w mv = some w') (hw : morseFits n w = true) :
    MorseReach (2 * n) (morseDouble w) (morseDouble w') := by
  obtain ⟨p, r, bk⟩ := mv
  obtain ⟨a, rest, -, rfl, rfl, hok, hs, hd⟩ := morseApply_shape n w w' p r bk h
  rw [morseFits_append, morseFits_append, Bool.and_eq_true, Bool.and_eq_true] at hw
  have ha := morseDouble_fits_dbl a n hw.1.1
  have hR : MorseReach (2 * morseOut n a)
      (morseDouble (if bk then morseRuleRhs r else morseRuleLhs r))
      (morseDouble (if bk then morseRuleLhs r else morseRuleRhs r)) := by
    cases bk
    · exact morseReach_morseDouble_rule r _ hok hs hd
    · exact morseReach_symm (morseReach_morseDouble_rule r _ hok hd hs)
  have hF := morseReach_frame (2 * morseOut n a) (2 * n) 0 0 (morseDouble a) (morseDouble rest)
    _ _ hR (morseDouble_fits_dbl _ _ hs).1 (by rw [ha.2]; omega)
  simpa only [morseShiftWord_zero_dbl, morseDouble_append_dbl, List.append_assoc] using hF

/-- Doubling preserves reachability. -/
theorem morseReach_morseDouble {n : ℕ} {w w' : MorseWord} (h : MorseReach n w w')
    (hw : morseFits n w = true) : MorseReach (2 * n) (morseDouble w) (morseDouble w') := by
  obtain ⟨mvs, hm⟩ := h
  induction mvs generalizing w with
  | nil =>
    simp only [morseApplyAll, Option.some.injEq] at hm
    rw [hm]
    exact morseReach_refl _ _
  | cons mv mvs ih =>
    simp only [morseApplyAll] at hm
    cases h1 : morseApply n w mv with
    | none => simp [h1] at hm
    | some w₁ =>
      rw [h1, Option.bind_some] at hm
      exact morseReach_trans (morseReach_morseDouble_move n w w₁ mv h1 hw)
        (ih (morseFits_morseApply_dbl _ _ _ _ h1 hw) hm)

end AJConjecture
