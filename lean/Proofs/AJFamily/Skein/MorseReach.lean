import Mathlib
import AJConjecture.SkeinMorseApplyAppend

/-!
# Checker reachability

`MorseReach n w w'`: some list of moves of the Morse-word checker turns `w` into `w'` (words
starting on `n` strands). Reachability is transitive; reflexivity and symmetry are in
`MorsePhaseTools`, and soundness of the checker (`morseOp_eq_of_morseApplyAll`) turns reachability
into equality of thick operators.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- Reachability by the checker: some list of moves turns `w` into `w'` (words starting on `n`
strands). -/
def MorseReach (n : ℕ) (w w' : MorseWord) : Prop :=
  ∃ mvs : List MorseMove, morseApplyAll n w mvs = some w'

/-- Checker reachability is transitive: concatenate the move lists. -/
theorem morseReach_trans {n : ℕ} {w₁ w₂ w₃ : MorseWord} (h₁ : MorseReach n w₁ w₂)
    (h₂ : MorseReach n w₂ w₃) : MorseReach n w₁ w₃ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exact ⟨a ++ b, morseApplyAll_append_eq_some n w₁ w₂ w₃ a b ha hb⟩

end AJConjecture
