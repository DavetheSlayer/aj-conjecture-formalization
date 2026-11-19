import Mathlib
import AJFamily.Quantum.ChebU

/-!
# The twist parameter

`K(z) = z - 1/(A B)`, `A = U_(m-1) - U_m`, `B = U_(m-1)`, and the identity
`(z + 2) A B - 1 = -(U_(2m) + U_(2m-1))`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The rational function `K(z) = z - 1/(A(z) B(z))`, `A = U_(m-1) - U_m`, `B = U_(m-1)`. -/
def twistParamK (m : ℕ) : RatFunc ℂ :=
  RatFunc.X - (algebraMap ℂ[X] (RatFunc ℂ)
    ((chebU (X : ℂ[X]) (m - 1) - chebU (X : ℂ[X]) m) * chebU (X : ℂ[X]) (m - 1)))⁻¹

/-- Doubling formulas for `chebU`: `U_(2n+1) = U_n (2 U_(n+1) - z U_n)` and
`U_(2n+2) = U_(n+1)^2 - U_n^2`. -/
private theorem chebU_double_formulas {R : Type*} [CommRing R] (z : R) (n : ℕ) :
    chebU z (2 * n + 1) = chebU z n * (2 * chebU z (n + 1) - z * chebU z n) ∧
      chebU z (2 * n + 2) = chebU z (n + 1) ^ 2 - chebU z n ^ 2 := by
  induction n with
  | zero => simp only [chebU]; constructor <;> ring
  | succ n ih =>
    have h3 : chebU z (2 * (n + 1) + 1) = z * chebU z (2 * n + 2) - chebU z (2 * n + 1) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, chebU]
    have h4 : chebU z (2 * (n + 1) + 2) =
        z * chebU z (2 * (n + 1) + 1) - chebU z (2 * n + 2) := by
      rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by ring, chebU,
        show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring]
    have h2 : chebU z (n + 1 + 1) = z * chebU z (n + 1) - chebU z n := by
      rw [show n + 1 + 1 = n + 2 from rfl, chebU]
    have h3' : chebU z (2 * (n + 1) + 1) =
        chebU z (n + 1) * (2 * chebU z (n + 1 + 1) - z * chebU z (n + 1)) := by
      rw [h3, ih.1, ih.2, h2]; ring
    refine ⟨h3', ?_⟩
    rw [h4, h3', h2, ih.2]; ring

theorem twistParam_add_two_identity (m : ℕ) (hm : 1 ≤ m) :
    (X + 2) * ((chebU (X : ℤ[X]) (m - 1) - chebU (X : ℤ[X]) m) * chebU (X : ℤ[X]) (m - 1)) - 1 =
      -(chebU (X : ℤ[X]) (2 * m) + chebU (X : ℤ[X]) (2 * m - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨h1, h2⟩ := chebU_double_formulas (X : ℤ[X]) n
  have hc := chebU_succ_sq_add (X : ℤ[X]) n
  rw [show n + 1 - 1 = n by omega, show 2 * (n + 1) = 2 * n + 2 by ring,
    show 2 * n + 2 - 1 = 2 * n + 1 by omega, h1, h2]
  linear_combination hc

end AJConjecture
