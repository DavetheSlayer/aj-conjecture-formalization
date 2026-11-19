import Mathlib
import AJHandoff.TorusKnot.PairKIsoFlip

/-!
# Thinning all discs

`morseReach_isoThin`: the long closure of a block word reaches its thin word. Induction on the
number of thinned discs, from the top disc down (`morseReach_isoThin_step`), starting from
`isoThinPartial_top`.
-/

namespace AJConjecture

/-- The discs `j + 1, …, n` can be thinned for every `j ≤ n`. -/
theorem morseReach_isoThinPartial {n : ℕ} {B : List SBlock} (hB : ∀ b ∈ B, b.Valid (n + 1))
    (j : ℕ) (hj : j ≤ n) : MorseReach 1 (isoThinPartial n B n) (isoThinPartial n B j) := by
  have key : ∀ m, m ≤ n → MorseReach 1 (isoThinPartial n B n) (isoThinPartial n B (n - m)) := by
    intro m
    induction m with
    | zero => exact fun _ ↦ morseReach_refl 1 _
    | succ m ih =>
      intro hm
      have h := morseReach_isoThin_step hB (show n - (m + 1) < n by omega)
      rw [show n - (m + 1) + 1 = n - m by omega] at h
      exact morseReach_trans (ih (by omega)) h
  have := key (n - j) (by omega)
  rwa [show n - (n - j) = j by omega] at this

/-- Thinning (generic): the long closure of a block word on `n + 1` strands reaches its thin
word. -/
theorem morseReach_isoThin {n : ℕ} {B : List SBlock} (hB : ∀ b ∈ B, b.Valid (n + 1)) :
    MorseReach 1 (morseLongClosure (n + 1) (blocksWord B)) (isoThinWord n B) := by
  rw [← isoThinPartial_top hB]
  exact morseReach_isoThinPartial hB 0 (Nat.zero_le n)

end AJConjecture
