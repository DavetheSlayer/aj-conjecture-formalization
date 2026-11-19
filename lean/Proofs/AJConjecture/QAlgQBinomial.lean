import Mathlib
import AJConjecture.ClaspAlgQVandermonde
import AJConjecture.QAlgQParamBasic

/-!
# The finite `q`-binomial theorem

`∑_{m=0}^{N} (-1)^m q^(m(m-1)/2) [N choose m]_q z^m = (z; q)_N`, with the Gaussian binomial
coefficient written as `(q;q)_N / ((q;q)_m (q;q)_(N-m))`, in the field `ℚ(t)` with `q = t⁴`.
-/

namespace AJConjecture

/-- The `m`-th term of the finite `q`-binomial sum of length `N + 1`. -/
private noncomputable def qBinomialSumTerm (z : RatFunc ℚ) (N m : ℕ) : RatFunc ℚ :=
  (-1) ^ m * qParam ^ (m * (m - 1) / 2) * z ^ m *
    (qPochhammer qParam N / (qPochhammer qParam m * qPochhammer qParam (N - m)))

/-- The term of index `0` of the `q`-binomial sum is `1`. -/
private theorem qBinomialSumTerm_zero (z : RatFunc ℚ) (N : ℕ) : qBinomialSumTerm z N 0 = 1 := by
  have h0 : qPochhammer qParam 0 = 1 := Finset.prod_range_zero _
  simp only [qBinomialSumTerm, Nat.zero_mul, Nat.zero_div, pow_zero, Nat.sub_zero, h0, one_mul,
    div_self (qPochhammer_qParam_ne_zero N)]

/-- The `q`-Pascal rule `[N+1, m+1] = [N, m+1] + q^(N-m) [N, m]` for `m < N`. -/
private theorem qBinomial_pascal_interior (N m : ℕ) (hm : m < N) :
    qPochhammer qParam (N + 1) /
        (qPochhammer qParam (m + 1) * qPochhammer qParam (N + 1 - (m + 1))) =
      qPochhammer qParam N / (qPochhammer qParam (m + 1) * qPochhammer qParam (N - (m + 1))) +
        qParam ^ (N - m) *
          (qPochhammer qParam N / (qPochhammer qParam m * qPochhammer qParam (N - m))) := by
  obtain ⟨r, rfl⟩ : ∃ r, N = m + 1 + r := ⟨N - (m + 1), by omega⟩
  have e1 : m + 1 + r + 1 - (m + 1) = r + 1 := by omega
  have e2 : m + 1 + r - (m + 1) = r := by omega
  have e3 : m + 1 + r - m = r + 1 := by omega
  have hN : qPochhammer qParam (m + 1 + r + 1) =
      qPochhammer qParam (m + 1 + r) * (1 - qParam * qParam ^ (m + 1 + r)) :=
    Finset.prod_range_succ _ _
  have hm1 : qPochhammer qParam (m + 1) = qPochhammer qParam m * (1 - qParam * qParam ^ m) :=
    Finset.prod_range_succ _ _
  have hr1 : qPochhammer qParam (r + 1) = qPochhammer qParam r * (1 - qParam * qParam ^ r) :=
    Finset.prod_range_succ _ _
  have hPm := qPochhammer_qParam_ne_zero m
  have hPr := qPochhammer_qParam_ne_zero r
  have hm0 := claspAlg_one_sub_qParam_mul_pow_ne_zero m
  have hr0 := claspAlg_one_sub_qParam_mul_pow_ne_zero r
  rw [e1, e2, e3, hN, hm1, hr1]
  field_simp
  ring

/-- The recursion of the terms of the `q`-binomial sum in `N`. -/
private theorem qBinomialSumTerm_succ_succ (z : RatFunc ℚ) (N m : ℕ) (hm : m ≤ N) :
    qBinomialSumTerm z (N + 1) (m + 1) =
      (if m + 1 ≤ N then qBinomialSumTerm z N (m + 1) else 0) -
        z * qParam ^ N * qBinomialSumTerm z N m := by
  have hE : (m + 1) * (m + 1 - 1) / 2 = m * (m - 1) / 2 + m := Nat.triangle_succ m
  unfold qBinomialSumTerm
  rw [hE]
  rcases hm.lt_or_eq with h | rfl
  · have hq : qParam ^ N = qParam ^ (N - m) * qParam ^ m := by
      rw [← pow_add]
      congr 1
      omega
    rw [ite_eq_left (by omega : m + 1 ≤ N), qBinomial_pascal_interior N m h, hq]
    ring
  · have h0 : qPochhammer qParam 0 = 1 := Finset.prod_range_zero _
    rw [ite_eq_right (by omega : ¬(m + 1 ≤ m)), Nat.sub_self, Nat.sub_self, h0, mul_one, mul_one,
      div_self (qPochhammer_qParam_ne_zero (m + 1)), div_self (qPochhammer_qParam_ne_zero m)]
    ring

/-- The finite `q`-binomial theorem. -/
theorem sum_qBinomial_eq_qPochhammer (N : ℕ) (z : RatFunc ℚ) :
    ∑ m ∈ Finset.range (N + 1), (-1) ^ m * qParam ^ (m * (m - 1) / 2) * z ^ m *
        (qPochhammer qParam N / (qPochhammer qParam m * qPochhammer qParam (N - m))) =
      qPochhammer z N := by
  change ∑ m ∈ Finset.range (N + 1), qBinomialSumTerm z N m = qPochhammer z N
  induction N with
  | zero =>
    rw [Finset.sum_range_one, qBinomialSumTerm_zero]
    exact (Finset.prod_range_zero _).symm
  | succ N ih =>
    have hP : qPochhammer z (N + 1) = qPochhammer z N * (1 - z * qParam ^ N) :=
      Finset.prod_range_succ _ _
    have hshift : ∑ m ∈ Finset.range (N + 1),
        (if m + 1 ≤ N then qBinomialSumTerm z N (m + 1) else 0) =
          ∑ m ∈ Finset.range N, qBinomialSumTerm z N (m + 1) := by
      rw [Finset.sum_range_succ, ite_eq_right (by omega : ¬(N + 1 ≤ N)), add_zero]
      refine Finset.sum_congr rfl fun m hm ↦ ite_eq_left ?_
      have := Finset.mem_range.mp hm
      omega
    have h0 : qBinomialSumTerm z (N + 1) 0 = qBinomialSumTerm z N 0 := by
      rw [qBinomialSumTerm_zero, qBinomialSumTerm_zero]
    have hsplit := Finset.sum_range_succ' (fun m ↦ qBinomialSumTerm z N m) N
    rw [ih] at hsplit
    rw [Finset.sum_range_succ', Finset.sum_congr rfl fun m hm ↦
      qBinomialSumTerm_succ_succ z N m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)),
      Finset.sum_sub_distrib, ← Finset.mul_sum, hshift, h0, ih, hP]
    linear_combination -hsplit

end AJConjecture
