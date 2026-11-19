import Mathlib
import AJHandoff.TorusInput.RJAxisIsotopy
import AJHandoff.TorusInput.RJIsoProjProps
import AJHandoff.TorusInput.RJIsoProjHopf
import AJHandoff.TorusInput.RJHopfLink
import AJConjecture.SkeinPtrTailBasic

/-!
# The linear relations for the traces of `c` on the isotypic parts (node RA5.iv.1)

For every colour `k` of the axis:
`∑_N qtr(c P_N) h_k(N) = θ_b^(r-1) ∑_(j ≤ min b k) (θ_(b+k-2j)/(θ_b θ_k))^r Δ_(b+k-2j)`.

Route. Compute `qtr(c f_b^{⊗ r} Ω_k)` twice. (1) `f_b^{⊗ r} = ∑_N P_N` (`rj_sum_isoProj`) and
`P_N Ω_k = h_k(N) P_N` (`rj_isoProj_mul_axisLoop`). (2) `qtr (Y · ptr Z) = qtr ((Y ⊗ 1) Z)`
(`qtr_eq_qtr_ptrTail`, `ptrTail_skPlace_mul`; `rjAxisLoop` is a partial trace), then
`rj_axis_isotopy` and `rj_qtr_fullTwist_pow_bundleProj`. Estimate 60–100 lines.
-/

noncomputable section

namespace AJConjecture

/-- The traces of the cyclic braid on the isotypic parts satisfy one linear relation for every
colour of the axis. -/
theorem rj_cycle_relation (b r k : ℕ) (hr : 1 ≤ r) :
    ∑ N ∈ rjSpec b r, qtr (b * r) (rjCycleMat b r * rjIsoProj b r N) * rjHopf N k =
      kinkScalar b ^ (r - 1) *
        ∑ j ∈ Finset.range (min b k + 1), rjTwistRatio b k j ^ r * loopScalar (b + k - 2 * j) := by
  have hsum : ∑ N ∈ rjSpec b r, qtr (b * r) (rjCycleMat b r * rjIsoProj b r N) * rjHopf N k =
      qtr (b * r) (rjCycleMat b r * rjColsProj b r * rjAxisLoop (b * r) k) := by
    rw [← rj_sum_isoProj, Matrix.mul_sum, Matrix.sum_mul]
    simp only [qtr, Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun N hN ↦ ?_
    rw [mul_assoc (rjCycleMat b r), rj_isoProj_mul_axisLoop b r N k hr hN, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_comm]
  rw [hsum, rjAxisLoop, rjLoopWith, ← ptrTail_skPlace_mul _ _ (Nat.le_add_right _ _),
    ← qtr_eq_qtr_ptrTail _ _ (Nat.le_add_right _ _),
    ← jwAt_eq_skPlace (b * r + k) (b * r) k le_rfl, ← mul_assoc, rj_axis_isotopy b r k hr,
    rj_qtr_fullTwist_pow_bundleProj]

end AJConjecture
