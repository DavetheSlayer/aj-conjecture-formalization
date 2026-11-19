import Mathlib

/-!
# Chebyshev polynomials of the second kind

The polynomials `U_n`, their trigonometric evaluation and a Cassini-type identity.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- Chebyshev polynomials of the second kind in the variable `z = 2cos θ`. -/
def chebU {R : Type*} [CommRing R] (z : R) : ℕ → R
  | 0 => 1
  | 1 => z
  | n + 2 => z * chebU z (n + 1) - chebU z n

/-- `U_(n+1)² + U_n² - z U_(n+1) U_n = 1`. -/
theorem chebU_succ_sq_add {R : Type*} [CommRing R] (z : R) (n : ℕ) :
    chebU z (n + 1) ^ 2 + chebU z n ^ 2 - z * chebU z (n + 1) * chebU z n = 1 := by
  induction n with
  | zero => simp [chebU]; ring
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 from rfl, chebU]
    linear_combination ih

/-- `U_n(2cos θ) sin θ = sin((n + 1)θ)`. -/
theorem chebU_two_mul_cos (θ : ℝ) (n : ℕ) :
    chebU (2 * Real.cos θ) n * Real.sin θ = Real.sin ((n + 1) * θ) := by
  have key : ∀ n : ℕ, chebU (2 * Real.cos θ) n * Real.sin θ = Real.sin ((n + 1) * θ) ∧
      chebU (2 * Real.cos θ) (n + 1) * Real.sin θ = Real.sin ((n + 2) * θ) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [chebU], ?_⟩
      simp only [chebU, Nat.cast_zero, zero_add]
      rw [show (2 : ℝ) * θ = θ + θ by ring, Real.sin_add]
      ring
    | succ n ih =>
      refine ⟨by rw [ih.2]; push_cast; ring_nf, ?_⟩
      rw [show n + 1 + 1 = n + 2 from rfl, chebU, sub_mul, mul_assoc, ih.2, ih.1]
      push_cast
      have h1 : Real.sin (((n : ℝ) + 1 + 2) * θ) = Real.sin (((n : ℝ) + 2) * θ + θ) := by ring_nf
      have h2 : Real.sin (((n : ℝ) + 1) * θ) = Real.sin (((n : ℝ) + 2) * θ - θ) := by ring_nf
      rw [h1, h2, Real.sin_add, Real.sin_sub]
      ring
  exact (key n).1

end AJConjecture
