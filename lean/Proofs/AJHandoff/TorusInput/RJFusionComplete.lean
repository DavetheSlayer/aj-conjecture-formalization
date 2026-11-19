import Mathlib
import AJHandoff.TorusInput.RJFusionOrth
import AJHandoff.TorusInput.RJFusionInclProj
import AJHandoff.TorusInput.RJRankLemma
import AJHandoff.TorusInput.RJFusionTraceSum
import AJHandoff.TorusInput.RJFusionNat
import AJConjecture.SkeinTraceCyclic
import AJConjecture.SkeinJwTrace

/-!
# Completeness of the fusion of two unequal bundles (node RA1.12, crux of RA1)

`f_a ⊗ f_b = ∑_(j ≤ min a b) d_j⁻¹ π_j ι_j` (fusion rule `V_(a+1) ⊗ V_(b+1) = ⊕_j V_(a+b+1-2j)`),
and `qtr (π_j ι_j) = d_j Δ_(a+b-2j)`.

Route (avoids the turnback algebra `D_k`, `k ≥ 2`, and the channel idempotents of the equal case).
Put `Q_j = d_j⁻¹ π_j ι_j` (`rj_fusionDim_ne_zero`). By `rj_fusionIncl_mul_fusionProj` and
`rj_fusionIncl_mul_fusionProj_of_ne`, the `Q_j` are orthogonal idempotents, and each is absorbed
by `F = f_a ⊗ f_b` on both sides (`rjFusionProj_absorb`, `rjFusionIncl_absorb`). So
`E = F - ∑ Q_j` is an idempotent; it commutes with the weight (`rjNat_bundleProj`,
`rjNat_fusionProj`, `rjNat_fusionIncl`); and by cyclicity (`qtr_mul_comm_of_weight`) and
`qtr_jwAt`, `qtr Q_j = Δ_(a+b-2j)`, so `qtr E = Δ_a Δ_b - ∑ Δ_(a+b-2j) = 0`
(`rj_qtr_bundleProj`, `rj_sum_loopScalar`). Conclude with
`rj_eq_zero_of_idempotent_of_qtr_eq_zero`. Estimate 100–150 lines.
-/

noncomputable section

namespace AJConjecture

/-- The quantum trace is additive under subtraction. -/
private theorem rj_qtr_sub_complete (n : ℕ) (A B : SkMat n n) :
    qtr n (A - B) = qtr n A - qtr n B := by
  rw [qtr, qtr, qtr, Matrix.mul_sub, Matrix.trace_sub]

/-- The quantum trace of a finite sum. -/
private theorem rj_qtr_sum_complete (n : ℕ) (s : Finset ℕ) (f : ℕ → SkMat n n) :
    qtr n (∑ i ∈ s, f i) = ∑ i ∈ s, qtr n (f i) := by
  rw [qtr, Finset.mul_sum, Matrix.trace_sum]
  rfl

/-- The quantum trace of a channel. -/
theorem rj_qtr_fusionProj_mul_fusionIncl (a b j : ℕ) (hj : j ≤ min a b) :
    qtr (a + b) (rjFusionProj a b j * rjFusionIncl a b j) =
      rjFusionDim a b j * loopScalar (a + b - 2 * j) := by
  rw [qtr_mul_comm_of_weight _ _ _ _ (rjNat_fusionProj a b j hj).1,
    rj_fusionIncl_mul_fusionProj a b j hj, qtr_smul, qtr_jwAt]

/-- The normalized channels multiply as orthogonal idempotents. -/
private theorem rj_channel_mul_channel_complete (a b j k : ℕ) (hj : j ≤ min a b)
    (hk : k ≤ min a b) :
    (rjFusionDim a b j)⁻¹ • (rjFusionProj a b j * rjFusionIncl a b j) *
        ((rjFusionDim a b k)⁻¹ • (rjFusionProj a b k * rjFusionIncl a b k)) =
      if j = k then (rjFusionDim a b j)⁻¹ • (rjFusionProj a b j * rjFusionIncl a b j)
        else 0 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (rjFusionIncl a b j)]
  by_cases h : j = k
  · subst h
    rw [ite_eq_left rfl, rj_fusionIncl_mul_fusionProj a b j hj, Matrix.smul_mul, Matrix.mul_smul,
      ← Matrix.mul_assoc, (rjFusionProj_absorb a b j).2, smul_smul,
      inv_mul_cancel_right₀ (rj_fusionDim_ne_zero a b j hj)]
  · rw [ite_eq_right h, rj_fusionIncl_mul_fusionProj_of_ne a b j k hj hk h, Matrix.zero_mul,
      Matrix.mul_zero, smul_zero]

/-- Completeness: `f_a ⊗ f_b` is the sum of its channels. -/
theorem rj_fusion_complete (a b : ℕ) :
    rjBundleProj a b = ∑ j ∈ Finset.range (min a b + 1),
      (rjFusionDim a b j)⁻¹ • (rjFusionProj a b j * rjFusionIncl a b j) := by
  set s := Finset.range (min a b + 1)
  set Q : ℕ → SkMat (a + b) (a + b) := fun j ↦
    (rjFusionDim a b j)⁻¹ • (rjFusionProj a b j * rjFusionIncl a b j) with hQ
  set F := rjBundleProj a b
  have hs : ∀ j ∈ s, j ≤ min a b := fun j hj ↦ Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hSS : (∑ j ∈ s, Q j) * (∑ j ∈ s, Q j) = ∑ j ∈ s, Q j := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mul_sum]
    simp only [hQ]
    rw [Finset.sum_congr rfl fun k hk ↦
        rj_channel_mul_channel_complete a b j k (hs j hj) (hs k hk),
      Finset.sum_ite_eq, ite_eq_left hj]
  have hFS : F * (∑ j ∈ s, Q j) = ∑ j ∈ s, Q j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [hQ, F]
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, (rjFusionProj_absorb a b j).1]
  have hSF : (∑ j ∈ s, Q j) * F = ∑ j ∈ s, Q j := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [hQ, F]
    rw [Matrix.smul_mul, Matrix.mul_assoc, (rjFusionIncl_absorb a b j).2]
  have hWS : skWeight (a + b) * (∑ j ∈ s, Q j) = (∑ j ∈ s, Q j) * skWeight (a + b) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    simp only [hQ]
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc,
      (rjNat_fusionProj a b j (hs j hj)).1, Matrix.mul_assoc, (rjNat_fusionIncl a b j (hs j hj)).1,
      Matrix.mul_assoc]
  have htr : qtr (a + b) (∑ j ∈ s, Q j) = loopScalar a * loopScalar b := by
    rw [rj_qtr_sum_complete, ← rj_sum_loopScalar]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    simp only [hQ]
    rw [qtr_smul, rj_qtr_fusionProj_mul_fusionIncl a b j (hs j hj),
      inv_mul_cancel_left₀ (rj_fusionDim_ne_zero a b j (hs j hj))]
  have hE := rj_eq_zero_of_idempotent_of_qtr_eq_zero (a + b) (F - ∑ j ∈ s, Q j)
    (by
      rw [sub_mul, mul_sub, mul_sub, rjBundleProj_mul_self, hFS, hSF, hSS]
      abel)
    (by rw [mul_sub, sub_mul, (rjNat_bundleProj a b).1, hWS])
    (by rw [rj_qtr_sub_complete, htr, rj_qtr_bundleProj, sub_self])
  exact sub_eq_zero.mp hE

end AJConjecture
