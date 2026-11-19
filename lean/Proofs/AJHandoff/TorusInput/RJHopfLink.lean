import Mathlib
import AJHandoff.TorusInput.RJFusionComplete

/-!
# The coloured torus link `T(2, 2p)` (node RA5.iii)

`qtr (J_(a,b)^p (f_a ⊗ f_b)) = ∑_(j ≤ min a b) (θ_(a+b-2j)/(θ_a θ_b))^p Δ_(a+b-2j)`: the closure
of the 2-bundle braid `σ^(2p)` coloured by `f_a`, `f_b`.

Route. `rj_fusion_complete`, then `J^p π_j = λ_j^p π_j` (`rj_fullTwist_mul_fusionProj`,
induction on `p`), linearity of `qtr`, and `rj_qtr_fusionProj_mul_fusionIncl` (the `d_j`
cancel). Estimate 40–70 lines.
-/

noncomputable section

namespace AJConjecture

/-- A power of the full twist acts on the fusion map of a channel by the power of the
eigenvalue. -/
private theorem rj_fullTwist_pow_mul_fusionProj_hopfLink (a b j p : ℕ) (hj : j ≤ min a b) :
    rjFullTwist a b ^ p * rjFusionProj a b j = rjTwistRatio a b j ^ p • rjFusionProj a b j := by
  induction p with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mul, one_smul]
  | succ p ih =>
    rw [pow_succ, Matrix.mul_assoc, rj_fullTwist_mul_fusionProj a b j hj, Matrix.mul_smul, ih,
      smul_smul, pow_succ, mul_comm (rjTwistRatio a b j)]

/-- The quantum trace of a finite sum. -/
private theorem rj_qtr_sum_hopfLink (n : ℕ) (s : Finset ℕ) (f : ℕ → SkMat n n) :
    qtr n (∑ i ∈ s, f i) = ∑ i ∈ s, qtr n (f i) := by
  rw [qtr, Finset.mul_sum, Matrix.trace_sum]
  rfl

/-- The closure of `σ^(2p)` on two bundles coloured `f_a`, `f_b`. -/
theorem rj_qtr_fullTwist_pow_bundleProj (a b p : ℕ) :
    qtr (a + b) (rjFullTwist a b ^ p * rjBundleProj a b) =
      ∑ j ∈ Finset.range (min a b + 1), rjTwistRatio a b j ^ p * loopScalar (a + b - 2 * j) := by
  rw [rj_fusion_complete, Finset.mul_sum, rj_qtr_sum_hopfLink]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ min a b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, rj_fullTwist_pow_mul_fusionProj_hopfLink a b j p hj',
    Matrix.smul_mul, qtr_smul, qtr_smul, rj_qtr_fusionProj_mul_fusionIncl a b j hj', ← mul_assoc,
    mul_comm _ (rjTwistRatio a b j ^ p), mul_assoc,
    inv_mul_cancel_left₀ (rj_fusionDim_ne_zero a b j hj')]

end AJConjecture
