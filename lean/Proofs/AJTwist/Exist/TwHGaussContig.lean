import Mathlib
import AJTwist.Quantum.TwQReindexZ
import AJTwist.Exist.TwHGauss

/-!
# The contiguity relation of the inner Gaussian periods

For every twist `ℓ`, every `c ∈ ℤ` and every `j ≥ 0`, with `J = q^j`:
`𝔊^(c) - q J 𝔊^(c+1) - q^(1+2ℓ+c) J 𝔊^(c+2ℓ) + q^(1+2ℓ+c) 𝔊^(c+2ℓ+1) = 0`.

This is the re-indexing of the bilateral transform along the first-order recurrence of the
Gaussian weight `g(n) = q^(ℓ n(n+1))`, `g(n+1) = q^(2ℓ(n+1)) g(n)`:
`twQ_cycloBilateralSum_reindex` with index `a = -ℓ`, `v = g`, forcing `h = 0` and the weight
`φ(n) = q^(c n)` (the kernel shift `K_{j,n+1}(1 - q² J Q) = -q K_{j,n}(Q - J)` of
Section 3.2 of the manuscript; no boundary terms). The summand of the left side there is
`[(1 - qJQ) Q^c + q^(1+2ℓ+c) (Q - J) Q^(2ℓ+c)] g(n)`, the sum of the four monomials above.

For `ℓ ≥ 1` the two extreme periods `𝔊^(c)`, `𝔊^(c+2ℓ+1)` have unit coefficients; for `ℓ ≤ -1`
the extreme periods are `𝔊^(c+2ℓ)`, `𝔊^(c+1)` with coefficients a unit times `J`; for `ℓ = 0`
the relation has two terms, `(1 - q^(1+c) J) 𝔊^(c) = (q J - q^(1+c)) 𝔊^(c+1)`. In every case any
`2|ℓ| + 1` consecutive periods generate the others up to nonzero polynomial multipliers
(`AJTwist.Exist.TwHGaussUp`, `TwHGaussDown`, `TwHGaussWindow`).

Checked in exact arithmetic for `|ℓ| ≤ 3`, `|c| ≤ 9`, `j ≤ 7` (scratch `H/h01_basic.py`, item
(b)).
-/

noncomputable section

namespace AJConjecture

/-- The summand of the re-indexed bilateral transform is the sum of four Gaussian monomials. -/
private theorem twHGauss_contiguity_term (ℓ c n : ℤ) (J K : RatFunc ℚ) :
    K * qParam ^ (ℓ * n * (n + 1) + c * n)
        - qParam * J * (K * qParam ^ (ℓ * n * (n + 1) + (c + 1) * n))
        - qParam ^ (1 + 2 * ℓ + c) * J * (K * qParam ^ (ℓ * n * (n + 1) + (c + 2 * ℓ) * n))
        + qParam ^ (1 + 2 * ℓ + c) * (K * qParam ^ (ℓ * n * (n + 1) + (c + 2 * ℓ + 1) * n)) =
      K * (((1 - qParam * J * qParam ^ n) * qParam ^ (c * n) +
        qParam ^ (1 - 2 * -ℓ) * (qParam ^ n - J) * qParam ^ (-(2 * -ℓ * n)) *
          qParam ^ (c * (n + 1))) * qParam ^ (ℓ * n * (n + 1))) := by
  have hq := qParam_ne_zero
  rw [show 1 - 2 * -ℓ = 1 + 2 * ℓ by ring, show -(2 * -ℓ * n) = 2 * ℓ * n by ring,
    show c * (n + 1) = c * n + c by ring,
    show ℓ * n * (n + 1) + (c + 1) * n = ℓ * n * (n + 1) + c * n + n by ring,
    show ℓ * n * (n + 1) + (c + 2 * ℓ) * n = ℓ * n * (n + 1) + c * n + 2 * ℓ * n by ring,
    show ℓ * n * (n + 1) + (c + 2 * ℓ + 1) * n = ℓ * n * (n + 1) + c * n + 2 * ℓ * n + n by ring]
  simp only [zpow_add₀ hq]
  ring

/-- The contiguity relation in the index `c` of the inner Gaussian periods. -/
theorem twHGauss_contiguity (ℓ c : ℤ) (j : ℕ) :
    twHGauss ℓ c j - qParam * qParam ^ j * twHGauss ℓ (c + 1) j
        - qParam ^ (1 + 2 * ℓ + c) * qParam ^ j * twHGauss ℓ (c + 2 * ℓ) j
        + qParam ^ (1 + 2 * ℓ + c) * twHGauss ℓ (c + 2 * ℓ + 1) j = 0 := by
  have hrec : ∀ n : ℤ, qParam ^ (ℓ * (n + 1) * (n + 1 + 1)) =
      qParam ^ (-(2 * -ℓ * (n + 1))) * qParam ^ (ℓ * n * (n + 1)) + 0 := fun n ↦ by
    rw [add_zero, ← zpow_add₀ qParam_ne_zero]
    congr 1
    ring
  have h := twQ_cycloBilateralSum_reindex (-ℓ) (v := fun n ↦ qParam ^ (ℓ * n * (n + 1)))
    (h := fun _ ↦ 0) hrec (fun n ↦ qParam ^ (c * n)) j
  simp only [cycloBilateralSum, mul_zero, Finset.sum_const_zero] at h
  refine Eq.trans ?_ h
  simp only [twHGauss, cycloBilateralSum]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ ↦ twHGauss_contiguity_term ℓ c n _ _

end AJConjecture
