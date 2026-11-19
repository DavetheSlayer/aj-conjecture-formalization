import Mathlib
import AJHandoff.TorusKnot.PairKWhDOrientRules
import AJFamily.Skein.MorseFrame

/-!
# Moves preserve orientations and the oriented writhe

`orientStates_perm_of_morseReach`: if `w` reaches `w'` by the moves of the checker, the two words
have the same oriented states up to order, for any input states on the right number of strands.
Consequences for long-knot diagrams: the oriented writhes of their orientations agree up to order
(`orientWrithes_perm_of_morseReach`), so the oriented writhe (`morseWrithe_eq_of_morseReach`) and
the property of being a long-knot diagram (`isLongKnotDiagram_of_morseReach`) are invariants of
reachability.

Route: a move replaces `a ++ src ++ rest` by `a ++ dst ++ rest` (`morseApply_shape`); the states
after `a` have `morseOut n a` directions (`orientStates_length`), on which `src` and `dst` agree
up to order (`orientStates_rule_perm`), and `rest` respects the order (`orientStates_perm`).
-/

namespace AJConjecture

/-- One move preserves fitting. -/
private theorem morseFits_morseApply_whd (n₀ : ℕ) (w w' : MorseWord) (mv : MorseMove)
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

/-- Reachability preserves fitting. -/
theorem morseFits_of_morseReach_whd {n₀ : ℕ} {w w' : MorseWord}
    (h : MorseReach n₀ w w') (hw : morseFits n₀ w = true) : morseFits n₀ w' = true := by
  obtain ⟨mvs, h⟩ := h
  induction mvs generalizing w with
  | nil =>
    simp only [morseApplyAll, Option.some.injEq] at h
    rw [← h]
    exact hw
  | cons mv mvs ih =>
    simp only [morseApplyAll] at h
    cases h1 : morseApply n₀ w mv with
    | none => simp [h1] at h
    | some w₁ =>
      rw [h1, Option.bind_some] at h
      exact ih (morseFits_morseApply_whd _ _ _ _ h1 hw) h

/-- Two words with the same oriented states on every label list of length `n` have the same
oriented states on every list of such inputs, up to order. -/
private theorem orientStates_perm_of_pointwise (u v : MorseWord) (n : ℕ)
    (huv : ∀ L : List Bool, L.length = n → ∀ x : ℤ,
      (orientStates u [(L, x)]).Perm (orientStates v [(L, x)]))
    (S : List (List Bool × ℤ)) (hS : ∀ st ∈ S, st.1.length = n) :
    (orientStates u S).Perm (orientStates v S) := by
  rw [orientStates_eq_flatMap u, orientStates_eq_flatMap v]
  exact List.Perm.flatMap_left _ fun st hst ↦ huv st.1 (hS st hst) st.2

/-- One move preserves the oriented states up to order. -/
private theorem orientStates_perm_of_morseApply (n : ℕ) (w w' : MorseWord) (mv : MorseMove)
    (h : morseApply n w mv = some w') (hw : morseFits n w = true)
    (S : List (List Bool × ℤ)) (hS : ∀ st ∈ S, st.1.length = n) :
    (orientStates w S).Perm (orientStates w' S) := by
  obtain ⟨p, r, bk⟩ := mv
  obtain ⟨a, rest, -, rfl, rfl, hok, hs, hd⟩ := morseApply_shape n w w' p r bk h
  rw [morseFits_append, morseFits_append, Bool.and_eq_true, Bool.and_eq_true] at hw
  rw [orientStates_append, orientStates_append, orientStates_append, orientStates_append]
  refine orientStates_perm rest (orientStates_perm_of_pointwise _ _ (morseOut n a) ?_ _
    (orientStates_length n a hw.1.1 S hS))
  intro L hL x
  cases bk
  · simp only [Bool.false_eq_true, ↓reduceIte] at hs hd ⊢
    exact orientStates_rule_perm r _ hok hs hd L hL x
  · simp only [↓reduceIte] at hs hd ⊢
    exact (orientStates_rule_perm r _ hok hd hs L hL x).symm

/-- **Reachability preserves the oriented states up to order.** -/
theorem orientStates_perm_of_morseReach {n : ℕ} {w w' : MorseWord} (h : MorseReach n w w')
    (hw : morseFits n w = true) (S : List (List Bool × ℤ)) (hS : ∀ st ∈ S, st.1.length = n) :
    (orientStates w S).Perm (orientStates w' S) := by
  obtain ⟨mvs, h⟩ := h
  induction mvs generalizing w with
  | nil =>
    simp only [morseApplyAll, Option.some.injEq] at h
    rw [h]
  | cons mv mvs ih =>
    simp only [morseApplyAll] at h
    cases h1 : morseApply n w mv with
    | none => simp [h1] at h
    | some w₁ =>
      rw [h1, Option.bind_some] at h
      exact (orientStates_perm_of_morseApply n w w₁ mv h1 hw S hS).trans
        (ih (morseFits_morseApply_whd _ _ _ _ h1 hw) h)

/-- Reachable long-knot diagrams have the same oriented writhes, up to order. -/
theorem orientWrithes_perm_of_morseReach {D D' : MorseWord} (hD : morseFits 1 D = true)
    (h : MorseReach 1 D D') : (orientWrithes D).Perm (orientWrithes D') :=
  ((orientStates_perm_of_morseReach h hD _ (by simp)).filter _).map _

/-- **The oriented writhe is invariant under the moves.** -/
theorem morseWrithe_eq_of_morseReach {D D' : MorseWord} (hD : morseFits 1 D = true)
    (h : MorseReach 1 D D') : morseWrithe D = morseWrithe D' :=
  (orientWrithes_perm_of_morseReach hD h).sum_eq

/-- Being a long-knot diagram is invariant under the moves. -/
theorem isLongKnotDiagram_of_morseReach {D D' : MorseWord} (hD : IsLongKnotDiagram D)
    (h : MorseReach 1 D D') : IsLongKnotDiagram D' :=
  ⟨morseFits_of_morseReach_whd h hD.1,
    (orientWrithes_perm_of_morseReach hD.1 h).length_eq ▸ hD.2⟩

end AJConjecture
