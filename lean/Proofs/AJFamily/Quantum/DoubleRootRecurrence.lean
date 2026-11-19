import Mathlib
import AJFamily.Quantum.NodeClosedForms

/-!
# Recurrences with a double root

`dblRoot_closed` solves in closed form a second-order recurrence with double root `w` and an
inhomogeneous companion driven by it. It gives the values and derivatives of the twist
polynomials at a double point of their recursion.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- Closed forms of the double-root recurrence for `y` and of its inhomogeneous companion for
`z`. -/
theorem dblRoot_closed {w δ z₁ α β : ℂ} (hw : w ≠ 0) {y z : ℕ → ℂ} (hy0 : y 0 = 1)
    (hy1 : y 1 = w + δ) (hy : ∀ k, y (k + 2) = 2 * w * y (k + 1) - w ^ 2 * y k)
    (hz0 : z 0 = 0) (hz1 : z 1 = z₁)
    (hz : ∀ k, z (k + 2) = 2 * w * z (k + 1) - w ^ 2 * z k + α * y (k + 1) - β * y k) (k : ℕ) :
    y k = w ^ k + k * w ^ (k - 1) * δ ∧ z k = dblRootDeriv w δ z₁ α β k := by
  have hY : ∀ n : ℕ, y n = w ^ n * (1 + n * δ / w) ∧
      y (n + 1) = w ^ (n + 1) * (1 + ((n + 1 : ℕ) : ℂ) * δ / w) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [hy0], ?_⟩
      rw [hy1]
      field_simp
      ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hy, ih.1, ih.2]
      push_cast
      field_simp
      ring
  have hZ : ∀ n : ℕ, z n = dblRootDeriv w δ z₁ α β n ∧
      z (n + 1) = dblRootDeriv w δ z₁ α β (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [hz0, dblRootDeriv], ?_⟩
      rw [hz1, dblRootDeriv]
      push_cast
      field_simp
      ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hz, ih.1, ih.2, (hY n).1, (hY n).2]
      simp only [dblRootDeriv]
      push_cast
      field_simp
      ring
  refine ⟨?_, (hZ k).1⟩
  rw [(hY k).1]
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel]
    field_simp
    ring

end AJConjecture
