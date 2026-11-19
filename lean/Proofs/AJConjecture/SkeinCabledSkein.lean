import Mathlib
import AJConjecture.ClaspAlgFullTwistSum
import AJConjecture.SkeinHalfTwistSpectral

/-!
# The cabled full twist in the turnback basis

`Σ_c² (f ⊗ f) = ∑_k s_k D_k` with `s_k = claspAlgFullTwistCoeff c k`. Both sides are combinations
of the channel idempotents: the left-hand side by `AJConjecture.halfTwist_mul_twoBundleProj_eq_sum`
and `AJConjecture.halfTwist_mul_channelIdem`, the right-hand side by `AJConjecture.turnback_eq_sum`;
the coefficients of `Q_n` agree by `AJConjecture.claspAlg_sum_fullTwistCoeff_mul_turnbackEigen`.
-/

namespace AJConjecture

/-- A combination of turnback elements in the basis of the channel idempotents. -/
private theorem sum_smul_turnback_cabledSkein (c : ℕ) (f : ℕ → RatFunc ℚ) :
    ∑ k ∈ Finset.range (c + 1), f k • turnback c k =
      ∑ n ∈ Finset.range (c + 1),
        (∑ k ∈ Finset.range (c + 1), f k * claspAlgTurnbackEigen c k n) • channelIdem c n := by
  have h : ∀ k ∈ Finset.range (c + 1), f k • turnback c k =
      ∑ n ∈ Finset.range (c + 1), (f k * claspAlgTurnbackEigen c k n) • channelIdem c n := by
    intro k _
    rw [turnback_eq_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun n _ ↦ smul_smul _ _ _
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ ↦ (Finset.sum_smul).symm

/-- The cabled full twist in the turnback basis. -/
theorem halfTwist_sq_mul_twoBundleProj_eq_sum_turnback (c : ℕ) :
    halfTwist c true * halfTwist c true * twoBundleProj c =
      ∑ k ∈ Finset.range (c + 1), claspAlgFullTwistCoeff c k • turnback c k := by
  rw [sum_smul_turnback_cabledSkein, Matrix.mul_assoc, halfTwist_mul_twoBundleProj_eq_sum,
    Matrix.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn' : n ≤ c := by
    rw [Finset.mem_range] at hn
    omega
  rw [claspAlg_sum_fullTwistCoeff_mul_turnbackEigen c n hn', Matrix.mul_smul,
    halfTwist_mul_channelIdem c n true hn', smul_smul, sq]
  rfl

end AJConjecture
