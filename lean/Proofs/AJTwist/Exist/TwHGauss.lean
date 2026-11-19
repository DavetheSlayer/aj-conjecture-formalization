import Mathlib
import AJConjecture.QAlgCycloBilateralSumCheb
import AJHandoff.TorusQuantum.PairQCycloBilateral
import AJTwist.Quantum.TwQInput

/-!
# The inner Gaussian periods in bilateral form

Source: revision 5, Section 6.3 (`selection.tex`, "The finite Gaussian forcing module"): the
half-interval input `w_n^{(ℓ,c)} = q^(ℓ n(n+1)) (Q^c - \hat Q^c)`, `Q = q^n`,
`\hat Q = q^(-(n+1))` (the library's `twPeriodInput ℓ c`). Its cyclotomic coefficients
`𝔊^(c)_j = ∑_{n ≤ j} K_{j,n} w_n^{(ℓ,c)}` are the inner periods of the existence argument.

`twHGauss ℓ c j = ∑_{n=-j-1}^{j} K_{j,n} q^(ℓ n(n+1) + c n)` is the same number written as a
bilateral transform of a single monomial:

* `twH_cycloCoeff_twPeriodInput`: `pairQCycloCoeff (twPeriodInput ℓ c) j = twHGauss ℓ c j`.
  By `pairQ_two_mul_cycloCoeff`, twice the left side is the bilateral transform of the odd
  extension `q^(ℓ n(n+1)) (Q^c - \hat Q^c)` (`twH_oddExt_twPeriodInput`); the reflection
  `n ↦ -n-1` fixes `ℓ n(n+1)`, maps `Q^c` to `\hat Q^c` and changes the sign of the kernel
  (`cycloBilateralKernel_neg_sub_one`), so the `\hat Q^c` part is minus the `Q^c` part.
* `twH_cycloStep_gauss`: `V 𝔊^(c) = 𝔊^(c+1) + q⁻¹ 𝔊^(c-1)`, because `V` is multiplication by
  `Q + \hat Q = Q + q⁻¹ Q⁻¹` under the bilateral transform (`cycloBilateralSum_cheb 1`).

Checked in exact arithmetic for `|ℓ| ≤ 3`, `|c| ≤ 9`, `j ≤ 7` (scratch `H/h01_basic.py`, items
(a), (c)).
-/

noncomputable section

namespace AJConjecture

/-- The inner Gaussian period `𝔊^(c)_j = ∑_{n=-j-1}^{j} K_{j,n} q^(ℓ n(n+1) + c n)`. -/
def twHGauss (ℓ c : ℤ) (j : ℕ) : RatFunc ℚ :=
  cycloBilateralSum (fun n ↦ qParam ^ (ℓ * n * (n + 1) + c * n)) j

/-- The odd extension of the period input is given by the same formula at every integer. -/
theorem twH_oddExt_twPeriodInput (ℓ c n : ℤ) :
    pairQOddExt (twPeriodInput ℓ c) n =
      qParam ^ (ℓ * n * (n + 1)) * (qParam ^ (c * n) - qParam ^ (-(c * (n + 1)))) := by
  unfold pairQOddExt twPeriodInput
  rcases le_or_gt 0 n with hn | hn
  · rw [ite_eq_left hn, Int.toNat_of_nonneg hn]
  · rw [ite_eq_right (by omega : ¬(0 : ℤ) ≤ n), Int.toNat_of_nonneg (by omega : 0 ≤ -n - 1),
      show ℓ * (-n - 1) * (-n - 1 + 1) = ℓ * n * (n + 1) by ring,
      show c * (-n - 1) = -(c * (n + 1)) by ring, show -(c * (-n - 1 + 1)) = c * n by ring]
    ring

/-- The reflection `n ↦ -n - 1` changes the sign of the bilateral transform. -/
private theorem cycloBilateralSum_reflect_twHGauss (g : ℤ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum (fun n ↦ g (-n - 1)) j = -cycloBilateralSum g j := by
  rw [cycloBilateralSum, cycloBilateralSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' (fun n ↦ -n - 1) (fun n ↦ -n - 1) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    omega
  · intro n _
    ring
  · intro n _
    ring
  · intro n _
    rw [cycloBilateralKernel_neg_sub_one, neg_mul, neg_neg]

/-- The bilateral transform is subtractive. -/
private theorem cycloBilateralSum_sub_twHGauss (f g : ℤ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum (fun n ↦ f n - g n) j = cycloBilateralSum f j - cycloBilateralSum g j := by
  simp only [cycloBilateralSum, mul_sub, Finset.sum_sub_distrib]

/-- The cyclotomic coefficients of the period input are the bilateral transform of one
monomial. -/
theorem twH_cycloCoeff_twPeriodInput (ℓ c : ℤ) (j : ℕ) :
    pairQCycloCoeff (twPeriodInput ℓ c) j = twHGauss ℓ c j := by
  have hq := qParam_ne_zero
  have h2 := pairQ_two_mul_cycloCoeff (twPeriodInput ℓ c) j
  have hfun : pairQOddExt (twPeriodInput ℓ c) = fun n ↦
      qParam ^ (ℓ * n * (n + 1) + c * n) -
        qParam ^ (ℓ * (-n - 1) * (-n - 1 + 1) + c * (-n - 1)) := by
    funext n
    rw [twH_oddExt_twPeriodInput, mul_sub, ← zpow_add₀ hq, ← zpow_add₀ hq]
    congr 2
    ring
  rw [hfun, cycloBilateralSum_sub_twHGauss,
    cycloBilateralSum_reflect_twHGauss (fun n ↦ qParam ^ (ℓ * n * (n + 1) + c * n)),
    sub_neg_eq_add, ← two_mul] at h2
  exact mul_left_cancel₀ two_ne_zero h2

/-- The step operator on the periods: `V 𝔊^(c) = 𝔊^(c+1) + q⁻¹ 𝔊^(c-1)`. -/
theorem twH_cycloStep_gauss (ℓ c : ℤ) (j : ℕ) :
    cycloStep (twHGauss ℓ c) j = twHGauss ℓ (c + 1) j + qParam⁻¹ * twHGauss ℓ (c - 1) j := by
  have hq := qParam_ne_zero
  have h := cycloBilateralSum_cheb 1 (fun n ↦ qParam ^ (ℓ * n * (n + 1) + c * n)) j
  have hstep : cycloCheb 1 (cycloBilateralSum fun n ↦ qParam ^ (ℓ * n * (n + 1) + c * n)) j =
      cycloStep (twHGauss ℓ c) j := rfl
  rw [hstep] at h
  rw [← h]
  simp only [twHGauss, cycloBilateralSum, Nat.cast_one, mul_one]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [show ℓ * n * (n + 1) + (c + 1) * n = n + (ℓ * n * (n + 1) + c * n) by ring,
    show ℓ * n * (n + 1) + (c - 1) * n = -n + (ℓ * n * (n + 1) + c * n) by ring,
    zpow_add₀ hq n, zpow_add₀ hq (-n), zpow_neg_one]
  ring

end AJConjecture
