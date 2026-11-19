import Mathlib
import AJHandoff.TorusInput.RJFusionTranspose
import AJConjecture.QAlgQParamBasic

/-!
# Different channels are orthogonal (node RA1.9)

The eigenvalues `θ_(a+b-2j)/(θ_a θ_b)`, `j ≤ min a b`, are pairwise distinct, so
`ι_j π_(j') = 0` for `j ≠ j'`.

Route. Distinctness: `θ_M = (-1)^M t^(M(M+2))`, the sign is the same for all channels (same parity
of `M = a + b - 2j`) and `M ↦ M(M+2)` is injective on `ℕ`; powers of `X` with different exponents
differ (`RatFunc.X`, `zpow` injectivity, e.g. via `intDegree` or `RatFunc.X_ne_zero` and
`zpow_right_injective₀` with `X` not a root of unity). Orthogonality:
`λ_j ι_j π_(j') = ι_j J π_(j') = λ_(j') ι_j π_(j')` (`rj_fusionIncl_mul_fullTwist`,
`rj_fullTwist_mul_fusionProj`). Estimate 50–90 lines.
-/

noncomputable section

namespace AJConjecture

/-- The sign of the kink scalar is the same on all channels. -/
private theorem rj_neg_one_pow_channel_orth (a b j : ℕ) (hj : j ≤ min a b) :
    (-1 : RatFunc ℚ) ^ (a + b - 2 * j) = (-1) ^ (a + b) := by
  conv_rhs => rw [show a + b = (a + b - 2 * j) + 2 * j from by omega, pow_add, pow_mul,
    neg_one_sq, one_pow, mul_one]

/-- The full-twist eigenvalues of the channels are pairwise distinct. -/
theorem rj_twistRatio_injOn (a b : ℕ) : Set.InjOn (rjTwistRatio a b) {j | j ≤ min a b} := by
  intro j hj j' hj' h
  simp only [Set.mem_ofPred_eq] at hj hj'
  have hD : kinkScalar a * kinkScalar b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (zpow_ne_zero _ RatFunc.X_ne_zero))
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (zpow_ne_zero _ RatFunc.X_ne_zero))
  rw [rjTwistRatio, rjTwistRatio, div_left_inj₀ hD, kinkScalar, kinkScalar,
    rj_neg_one_pow_channel_orth a b j hj, rj_neg_one_pow_channel_orth a b j' hj'] at h
  have h2 := ratFuncX_zpow_injective (mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h)
  have h3 : ((a + b - 2 * j : ℕ) : ℤ) = ((a + b - 2 * j' : ℕ) : ℤ) := by
    nlinarith
  omega

/-- Different channels are orthogonal. -/
theorem rj_fusionIncl_mul_fusionProj_of_ne (a b j j' : ℕ) (hj : j ≤ min a b) (hj' : j' ≤ min a b)
    (hne : j ≠ j') : rjFusionIncl a b j * rjFusionProj a b j' = 0 := by
  have h : (rjTwistRatio a b j - rjTwistRatio a b j') •
      (rjFusionIncl a b j * rjFusionProj a b j') = 0 := by
    rw [sub_smul, ← Matrix.smul_mul, ← rj_fusionIncl_mul_fullTwist a b j hj, ← Matrix.mul_smul,
      ← rj_fullTwist_mul_fusionProj a b j' hj', Matrix.mul_assoc, sub_self]
  exact (smul_eq_zero.mp h).resolve_left
    (sub_ne_zero.mpr fun he ↦ hne (rj_twistRatio_injOn a b hj hj' he))

end AJConjecture
