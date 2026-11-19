import Mathlib
import AJConjecture.QAlgCycloStep

/-!
# The twisted Chebyshev operators are linear

`S_d(V)` commutes with multiplication of the sequence by a constant and with addition of
sequences.
-/

namespace AJConjecture

/-- `S_d(V)` commutes with multiplication by a constant. -/
theorem cycloCheb_const_mul (d : ℕ) (c : RatFunc ℚ) (y : ℕ → RatFunc ℚ) (j : ℕ) :
    cycloCheb d (fun i ↦ c * y i) j = c * cycloCheb d y j := by
  induction d using Nat.twoStepInduction generalizing j with
  | zero =>
    simp only [cycloCheb]
    ring
  | one =>
    simp only [cycloCheb, cycloStep]
    ring
  | more d ih0 ih1 =>
    have h : cycloCheb (d + 1) (fun i ↦ c * y i) = fun i ↦ c * cycloCheb (d + 1) y i :=
      funext ih1
    simp only [cycloCheb]
    rw [h, ih0]
    simp only [cycloStep]
    ring

end AJConjecture
