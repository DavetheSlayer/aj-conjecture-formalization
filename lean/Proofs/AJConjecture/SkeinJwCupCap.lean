import Mathlib
import AJConjecture.SkeinJwCapComm
import AJConjecture.SkeinCupAtComm
import AJConjecture.SkeinJwBasic

/-!
# Closing the last strand of a projector inside a bundle

In a bundle of `k + 2` strands whose first `j + 1` strands carry `f_{j+1}`, closing the strand
`j` with the next one by a cup below and a cap above leaves `-([j+2]/[j+1]) f_j` on a bundle of
`k` strands: this is the partial trace of `f_{j+1}` over its last strand, written with a cup and
a cap, in the presence of spectator strands.
-/

namespace AJConjecture

/-- `δ + [j]/[j+1] = -[j+2]/[j+1]`. -/
theorem loop_add_quantumInt_div (j : ℕ) :
    (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) +
        quantumInt (j : ℤ) / quantumInt ((j : ℤ) + 1) =
      -(quantumInt ((j : ℤ) + 2) / quantumInt ((j : ℤ) + 1)) := by
  have h1 : quantumInt ((j : ℤ) + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have hrec := quantumInt_recurrence ((j : ℤ) + 1)
  rw [show (j : ℤ) + 1 + 1 = (j : ℤ) + 2 from by ring, show (j : ℤ) + 1 - 1 = (j : ℤ) from by ring]
    at hrec
  rw [← neg_div, eq_div_iff h1, add_mul, div_mul_cancel₀ _ h1]
  linear_combination -hrec

/-- The last strand of `f_{j+1}` closed by a cup and a cap inside a bundle. -/
theorem cupAt_mul_jwAt_mul_capAt (k j : ℕ) (hj : j ≤ k) :
    cupAt k j * jwAt (k + 2) 0 (j + 1) * capAt k j =
      -(quantumInt ((j : ℤ) + 2) / quantumInt ((j : ℤ) + 1)) • jwAt k 0 j := by
  cases j with
  | zero =>
    have h0 : quantumInt ((0 : ℕ) : ℤ) = 0 := by simp [quantumInt]
    have hs := loop_add_quantumInt_div 0
    rw [h0, zero_div, add_zero] at hs
    rw [← hs, jwAt, jwAt, Matrix.mul_one, cupAt_mul_capAt k 0 hj]
  | succ m =>
    have hs := loop_add_quantumInt_div (m + 1)
    rw [show (((m + 1 : ℕ) : ℤ)) = (m : ℤ) + 1 from by push_cast; ring,
      show (m : ℤ) + 1 + 1 = (m : ℤ) + 2 from by ring] at hs ⊢
    have hcup : jwAt k 0 (m + 1) * cupAt k (m + 1) = cupAt k (m + 1) * jwAt (k + 2) 0 (m + 1) :=
      jwAt_mul_eq_mul_jwAt k (k + 2) 0 0 _ (m + 1) fun l hl ↦
        tlGenF_mul_cupAt_of_lt k (m + 1) (0 + l) (by omega)
    have hcap : jwAt (k + 2) 0 (m + 1) * capAt k (m + 1) = capAt k (m + 1) * jwAt k 0 (m + 1) :=
      jwAt_mul_eq_mul_jwAt (k + 2) k 0 0 _ (m + 1) fun l hl ↦
        (capAt_mul_tlGenF_of_lt k (m + 1) (0 + l) (by omega)).symm
    have h1 : cupAt k (m + 1) * jwAt (k + 2) 0 (m + 1) * capAt k (m + 1) =
        (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) • jwAt k 0 (m + 1) := by
      rw [← hcup, Matrix.mul_assoc, cupAt_mul_capAt k (m + 1) hj, Matrix.mul_smul, Matrix.mul_one]
    have hzig : cupAt k (m + 1) * tlGenF (k + 2) (0 + m) * capAt k (m + 1) = 1 := by
      rw [Nat.zero_add, ← capAt_mul_cupAt k m (by omega), ← Matrix.mul_assoc, Matrix.mul_assoc,
        cupAt_succ_mul_capAt k m (by omega), cupAt_mul_capAt_succ k m (by omega), Matrix.one_mul]
    have h2 : cupAt k (m + 1) * (jwAt (k + 2) 0 (m + 1) * tlGenF (k + 2) (0 + m) *
        jwAt (k + 2) 0 (m + 1)) * capAt k (m + 1) = jwAt k 0 (m + 1) :=
      calc cupAt k (m + 1) * (jwAt (k + 2) 0 (m + 1) * tlGenF (k + 2) (0 + m) *
            jwAt (k + 2) 0 (m + 1)) * capAt k (m + 1)
          = (cupAt k (m + 1) * jwAt (k + 2) 0 (m + 1)) * tlGenF (k + 2) (0 + m) *
            (jwAt (k + 2) 0 (m + 1) * capAt k (m + 1)) := by simp only [Matrix.mul_assoc]
        _ = jwAt k 0 (m + 1) * (cupAt k (m + 1) * tlGenF (k + 2) (0 + m) * capAt k (m + 1)) *
            jwAt k 0 (m + 1) := by rw [← hcup, hcap]; simp only [Matrix.mul_assoc]
        _ = jwAt k 0 (m + 1) := by rw [hzig, Matrix.mul_one, jwAt_mul_self]
    rw [show jwAt (k + 2) 0 (m + 1 + 1) = jwAt (k + 2) 0 (m + 1) +
      (quantumInt ((m : ℤ) + 1) / quantumInt ((m : ℤ) + 2)) • (jwAt (k + 2) 0 (m + 1) *
        tlGenF (k + 2) (0 + m) * jwAt (k + 2) 0 (m + 1)) from by rw [jwAt],
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h1, h2, ← add_smul, hs]

end AJConjecture
