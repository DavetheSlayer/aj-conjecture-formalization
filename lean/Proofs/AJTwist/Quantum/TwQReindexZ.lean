import Mathlib
import AJConjecture.QAlgCycloKernelShift
import AJHandoff.TorusQuantum.PairQCycloReindex

/-!
# Re-indexing the bilateral transform for an integer index (Unit Q4)

Source: revision 5, Section 3.2 (`transfer.tex`): "Cancellation of consecutive factorials gives
`K_{j,n+1}(1 - q² J Q) = -q K_{jn}(Q - J)`. Thus for a weight `f(Q)` the sum of
`K_{jn}(1 - qJQ) f(Q) v_n` on the reflected interval equals the sum of
`-q K_{jn}(Q - J) f(qQ) v_{n+1}`. The lower endpoint has `1 - qJQ = 0`, the upper `Q - J = 0`."

`twQ_cycloBilateralSum_reindex`: if `v(n+1) = q^(-2a(n+1)) v(n) + h(n)` at every integer `n`,
then for every weight `φ` and every `j`
`𝔅_j([(1 - qJQ) φ(n) + q^(1-2a) (Q - J) Q^(-2a) φ(n+1)] v) = -q 𝔅_j((Q - J) φ(n+1) h)`.
This is the library's `pairQ_cycloBilateralSum_reindex` with the natural number `m` replaced by
an integer `a`; its proof (kernel shift `cycloBilateralKernel_succ`, vanishing at both ends of
the support) does not use the sign of the index.
-/

noncomputable section

namespace AJConjecture

/-- Shifting the summation index of a sum over an integer interval when the summand vanishes
at the lower end and just above the upper end. -/
private theorem sum_Icc_int_shift_of_ends_eq_zero_reindexZ (F : ℤ → RatFunc ℚ) (a b : ℤ)
    (ha : F a = 0) (hb : F (b + 1) = 0) :
    ∑ n ∈ Finset.Icc a b, F (n + 1) = ∑ n ∈ Finset.Icc a b, F n := by
  have h1 : ∑ n ∈ Finset.Icc a b, F (n + 1) = ∑ m ∈ Finset.Icc (a + 1) (b + 1), F m := by
    refine Finset.sum_nbij' (fun n ↦ n + 1) (fun m ↦ m - 1) ?_ ?_ ?_ ?_ ?_
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
      rfl
  have h2 : ∑ m ∈ Finset.Icc (a + 1) b, F m = ∑ m ∈ Finset.Icc (a + 1) (b + 1), F m := by
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      rw [Finset.mem_Icc] at hn hn'
      obtain rfl : n = b + 1 := by omega
      exact hb
  have h3 : ∑ m ∈ Finset.Icc (a + 1) b, F m = ∑ m ∈ Finset.Icc a b, F m := by
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      rw [Finset.mem_Icc] at hn hn'
      obtain rfl : n = a := by omega
      exact ha
  rw [h1, ← h2, h3]

/-- The term of the forcing sum splits into a shifted term and a homogeneous term. -/
private theorem cycloBilateralKernel_mul_forcing_split_reindexZ (a : ℤ) {v h : ℤ → RatFunc ℚ}
    (hrec : ∀ n : ℤ, v (n + 1) = qParam ^ (-(2 * a * (n + 1))) * v n + h n)
    (φ : ℤ → RatFunc ℚ) (j : ℕ) (n : ℤ) :
    -qParam * (cycloBilateralKernel j n * ((qParam ^ n - qParam ^ j) * φ (n + 1) * h n)) =
      (1 - qParam * qParam ^ j * qParam ^ (n + 1)) * cycloBilateralKernel j (n + 1) *
          φ (n + 1) * v (n + 1) +
        cycloBilateralKernel j n *
          (qParam ^ (1 - 2 * a) * (qParam ^ n - qParam ^ j) *
            qParam ^ (-(2 * a * n)) * φ (n + 1) * v n) := by
  have hq := qParam_ne_zero
  have hK := cycloBilateralKernel_succ j n
  have hF : h n = v (n + 1) - qParam ^ (-(2 * a * (n + 1))) * v n := by
    rw [hrec n]
    ring
  have hpow : qParam ^ (-(2 * a * (n + 1))) =
      qParam ^ (-(2 * a)) * qParam ^ (-(2 * a * n)) := by
    rw [← zpow_add₀ hq]
    congr 1
    ring
  have h1 : qParam ^ (1 - 2 * a) = qParam * qParam ^ (-(2 * a)) := by
    rw [← zpow_one_add₀ hq]
    ring_nf
  rw [hF, hpow, h1, zpow_add_one₀ hq]
  linear_combination (-(φ (n + 1) * v (n + 1))) * hK

/-- Re-indexing the bilateral transform along the recurrence `v(n+1) = q^(-2a(n+1)) v(n) + h(n)`,
for an integer index `a`. -/
theorem twQ_cycloBilateralSum_reindex (a : ℤ) {v h : ℤ → RatFunc ℚ}
    (hrec : ∀ n : ℤ, v (n + 1) = qParam ^ (-(2 * a * (n + 1))) * v n + h n)
    (φ : ℤ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum
        (fun n ↦ ((1 - qParam * qParam ^ j * qParam ^ n) * φ n +
          qParam ^ (1 - 2 * a) * (qParam ^ n - qParam ^ j) *
            qParam ^ (-(2 * a * n)) * φ (n + 1)) * v n) j =
      -qParam * cycloBilateralSum (fun n ↦ (qParam ^ n - qParam ^ j) * φ (n + 1) * h n) j := by
  have hq := qParam_ne_zero
  have ha : (1 - qParam * qParam ^ j * qParam ^ (-((j : ℤ) + 1))) *
      cycloBilateralKernel j (-((j : ℤ) + 1)) * φ (-((j : ℤ) + 1)) *
        v (-((j : ℤ) + 1)) = 0 := by
    have h0 : 1 - qParam * qParam ^ j * qParam ^ (-((j : ℤ) + 1)) = 0 := by
      rw [zpow_neg, zpow_add_one₀ hq, zpow_natCast, mul_comm qParam]
      exact sub_eq_zero.mpr (mul_inv_cancel₀ (mul_ne_zero (pow_ne_zero j hq) hq)).symm
    rw [h0, zero_mul, zero_mul, zero_mul]
  have hb : (1 - qParam * qParam ^ j * qParam ^ ((j : ℤ) + 1)) *
      cycloBilateralKernel j ((j : ℤ) + 1) * φ ((j : ℤ) + 1) *
        v ((j : ℤ) + 1) = 0 := by
    rw [cycloBilateralKernel, ite_eq_right (by omega), mul_zero, zero_mul, zero_mul]
  have hshift := sum_Icc_int_shift_of_ends_eq_zero_reindexZ
    (fun n ↦ (1 - qParam * qParam ^ j * qParam ^ n) * cycloBilateralKernel j n * φ n *
      v n) (-((j : ℤ) + 1)) j ha hb
  simp only [cycloBilateralSum]
  rw [Finset.mul_sum, Finset.sum_congr rfl fun n _ ↦
    cycloBilateralKernel_mul_forcing_split_reindexZ a hrec φ j n, Finset.sum_add_distrib, hshift,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  ring

end AJConjecture
