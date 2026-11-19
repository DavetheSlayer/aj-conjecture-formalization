import Mathlib
import AJConjecture.SkeinCupTlCap
import AJConjecture.SkeinJwBasic

/-!
# The Jones–Wenzl projector kills cups and caps, and is absorbed by what kills the generators

`f e_j = 0` and `e_j = capAt * cupAt` give `f * capAt = δ⁻¹ f * capAt * cupAt * capAt = 0` (the loop
value `δ = -t² - t⁻²` is not zero), and symmetrically for cups. Conversely a matrix `Z` with
`Z e_j = 0` for all generators of a block satisfies `Z f = Z`: by induction with Wenzl's recursion
`f_{k+2} = f_{k+1} + c f_{k+1} e_{i+k} f_{k+1}`, the second term is killed by `Z f_{k+1} = Z` and
`Z e_{i+k} = 0`. The last two statements are the uniqueness of the projector in the form used to
identify idempotents with projectors.
-/

namespace AJConjecture

/-- The loop value `δ = -t² - t⁻²` is not zero. -/
private theorem loop_ne_zero_jwCapKill :
    (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) ≠ 0 := by
  intro h
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h4 : (RatFunc.X : RatFunc ℚ) ^ 4 + 1 = 0 := by
    have h2 : (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) * RatFunc.X ^ (-2 : ℤ) = 1 := by
      rw [← zpow_add₀ hX]; norm_num
    have h3 : (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) = RatFunc.X ^ 2 := by norm_cast
    rw [h3] at h h2
    linear_combination (-(RatFunc.X : RatFunc ℚ) ^ 2) * h - h2
  have h5 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X ^ 4 + 1) = 0 := by
    rw [map_add, map_pow, map_one, RatFunc.algebraMap_X, h4]
  have h6 := (map_eq_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mp h5
  have h7 := congrArg (Polynomial.eval 0) h6
  simp at h7

/-- Absorption of the projector on the right, by induction on its size. -/
private theorem mul_jwAt_of_forall_mul_tlGenF_eq_zero_jwCapKill (n i : ℕ) {l : ℕ}
    (Z : SkMat l n) :
    ∀ k : ℕ, (∀ j : ℕ, i ≤ j → j + 1 < i + k → Z * tlGenF n j = 0) → Z * jwAt n i k = Z
  | 0, _ => by rw [jwAt, Matrix.mul_one]
  | 1, _ => by rw [jwAt, Matrix.mul_one]
  | k + 2, hZ => by
    have ih := mul_jwAt_of_forall_mul_tlGenF_eq_zero_jwCapKill n i Z (k + 1) fun j hij hjk ↦
      hZ j hij (by omega)
    rw [jwAt, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ih,
      hZ (i + k) (by omega) (by omega), Matrix.zero_mul, smul_zero, add_zero]

/-- The projector kills a cup on two strands of its block. -/
theorem cupAt_mul_jwAt (n i k j : ℕ) (hij : i ≤ j) (hjk : j + 2 ≤ i + k) :
    cupAt n j * jwAt (n + 2) i k = 0 := by
  rcases Nat.lt_or_ge n j with h | h
  · rw [cupAt_eq_zero n j h, Matrix.zero_mul]
  · have h1 : cupAt n j * capAt n j * (cupAt n j * jwAt (n + 2) i k) = 0 := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (cupAt n j), capAt_mul_cupAt n j h,
        Matrix.mul_assoc, tlGenF_mul_jwAt (n + 2) i k j hij (by omega), Matrix.mul_zero]
    rw [cupAt_mul_capAt n j h, Matrix.smul_mul, Matrix.one_mul] at h1
    exact (smul_eq_zero.mp h1).resolve_left loop_ne_zero_jwCapKill

/-- A matrix that kills the generators of a block on the right absorbs the projector of the
block. -/
theorem mul_jwAt_of_forall_mul_tlGenF_eq_zero (n i k : ℕ) {l : ℕ} (Z : SkMat l n)
    (h : ∀ j, i ≤ j → j + 1 < i + k → Z * tlGenF n j = 0) : Z * jwAt n i k = Z :=
  mul_jwAt_of_forall_mul_tlGenF_eq_zero_jwCapKill n i Z k h

end AJConjecture
