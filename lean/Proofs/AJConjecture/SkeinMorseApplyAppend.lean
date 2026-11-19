import Mathlib
import AJConjecture.SkeinMorseCheck

/-!
# Composition of move lists

Applying a concatenation of two lists of moves is applying the first list and then the second.
This composes the chunks of a long certificate, each checked by its own kernel computation.
-/

namespace AJConjecture

/-- Applying a concatenation of move lists. -/
theorem morseApplyAll_append (n₀ : ℕ) (w : MorseWord) (a b : List MorseMove) :
    morseApplyAll n₀ w (a ++ b) = (morseApplyAll n₀ w a).bind fun w' ↦ morseApplyAll n₀ w' b := by
  induction a generalizing w with
  | nil => simp [morseApplyAll]
  | cons mv a ih =>
    simp only [List.cons_append, morseApplyAll]
    cases h : morseApply n₀ w mv with
    | none => simp
    | some w' => simp [ih]

/-- Two accepted lists of moves compose. -/
theorem morseApplyAll_append_eq_some (n₀ : ℕ) (w w' w'' : MorseWord) (a b : List MorseMove)
    (h₁ : morseApplyAll n₀ w a = some w') (h₂ : morseApplyAll n₀ w' b = some w'') :
    morseApplyAll n₀ w (a ++ b) = some w'' := by
  rw [morseApplyAll_append, h₁]
  simpa using h₂

end AJConjecture
