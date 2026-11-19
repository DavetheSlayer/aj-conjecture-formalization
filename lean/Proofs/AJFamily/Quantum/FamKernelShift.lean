import Mathlib
import AJConjecture.QAlgQParamBasic
import AJFamily.Quantum.FamTransferPoly

/-!
# Shifting the colour of the cyclotomic kernel

`cyclotomicKernel_sub_mul_famBasisPoly`: `C_j(N - i) P_0(q^N, q^j) = C_j(N) P_i(q^N, q^j)` for the
family basis polynomials `P_i`, `i ≤ 2m + 3`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The value of a basis polynomial at a point, as a product. -/
theorem evalEval_famBasisPoly_eq {R : Type*} [CommRing R]
    (m : ℕ) (q x y : R) (i : ℕ) :
    (famBasisPoly m q i).evalEval x y =
      (∏ r ∈ Finset.range i, ((q ^ r - x) * (x - q ^ (r + 1) * y))) *
        ∏ r ∈ Finset.Ico i (2 * m + 3), ((x - q ^ (r + 1)) * (q ^ r - x * y)) := by
  simp only [famBasisPoly, evalEval_prod, evalEval_mul, evalEval_sub, evalEval_C,
    evalEval_X, eval_sub, eval_C, eval_X]

/-- An integer power of `q` whose exponent is a natural number plus an integer. -/
private theorem famShift_qParam_zpow_eq_pow_mul_zpow (n : ℕ) (K e : ℤ) (h : e = n + K) :
    qParam ^ e = qParam ^ n * qParam ^ K := by
  subst h
  rw [zpow_add₀ qParam_ne_zero, zpow_natCast]

/-- The cyclotomic kernel with one more factor. -/
private theorem famShift_cyclotomicKernel_succ_eq_mul (j : ℕ) (K : ℤ) :
    cyclotomicKernel (j + 1) K = cyclotomicKernel j K *
      ((1 - qParam ^ (((j + 1 : ℕ) : ℤ) + K)) *
        (1 - qParam ^ (((j + 1 : ℕ) : ℤ) - K))) := by
  unfold cyclotomicKernel
  rw [Finset.prod_Icc_succ_top (by omega)]

/-- The cyclotomic kernels at two consecutive colours. -/
private theorem famShift_cyclotomicKernel_sub_one_mul_eq (j : ℕ) (M : ℤ) :
    cyclotomicKernel j (M - 1) *
        ((1 - qParam ^ j * qParam ^ M) * (1 - qParam * qParam ^ (-M))) =
      cyclotomicKernel j M *
        ((1 - qParam ^ M) * (1 - qParam ^ j * qParam * qParam ^ (-M))) := by
  induction j with
  | zero => simp only [cyclotomicKernel, pow_zero, one_mul, zero_lt_one, Finset.Icc_eq_empty_of_lt,
      Finset.prod_empty]
  | succ j ih =>
    rw [famShift_cyclotomicKernel_succ_eq_mul, famShift_cyclotomicKernel_succ_eq_mul,
      famShift_qParam_zpow_eq_pow_mul_zpow j M (((j + 1 : ℕ) : ℤ) + (M - 1))
        (by push_cast; ring),
      famShift_qParam_zpow_eq_pow_mul_zpow (j + 2) (-M) (((j + 1 : ℕ) : ℤ) - (M - 1))
        (by push_cast; ring),
      famShift_qParam_zpow_eq_pow_mul_zpow (j + 1) M (((j + 1 : ℕ) : ℤ) + M) rfl,
      famShift_qParam_zpow_eq_pow_mul_zpow (j + 1) (-M) (((j + 1 : ℕ) : ℤ) - M) (by ring)]
    linear_combination
      (1 - qParam ^ (j + 2) * qParam ^ (-M)) * (1 - qParam ^ (j + 1) * qParam ^ M) * ih

/-- The algebra of one step of the shift of the cyclotomic kernel. -/
private theorem famKernelShift_step_algebra {K : Type*} [CommRing K]
    (A' A B P P' p a J u v x : K) (huv : u * v = 1) (hx : x = u * p)
    (hstep : A' * ((1 - J * u) * (1 - a * v)) = A * ((1 - u) * (1 - J * a * v)))
    (ih : A * P = B * P') :
    A' * (P * ((x - p * a) * (p - x * J))) = B * (P' * ((p - x) * (x - p * a * J))) := by
  subst hx
  linear_combination P * p ^ 2 * u * hstep +
    (A' * P * p ^ 2 * (1 - u * J) * a - P * p ^ 2 * A * (1 - u) * a * J) * huv +
    p ^ 2 * (1 - u) * (u - a * J) * ih

/-- The shift of the cyclotomic kernel by `i`, against the first `i` factors. -/
private theorem famShift_cyclotomicKernel_sub_mul_prod_range (j : ℕ) (N : ℤ) (i : ℕ) :
    cyclotomicKernel j (N - i) * ∏ r ∈ Finset.range i,
        ((qParam ^ N - qParam ^ (r + 1)) * (qParam ^ r - qParam ^ N * qParam ^ j)) =
      cyclotomicKernel j N * ∏ r ∈ Finset.range i,
        ((qParam ^ r - qParam ^ N) * (qParam ^ N - qParam ^ (r + 1) * qParam ^ j)) := by
  induction i with
  | zero => simp only [Nat.cast_zero, sub_zero, Finset.range_zero, Finset.prod_empty]
  | succ i ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ,
      show N - ((i + 1 : ℕ) : ℤ) = N - i - 1 by push_cast; ring, pow_succ qParam i]
    refine famKernelShift_step_algebra _ _ _ _ _ _ _ _ (qParam ^ (N - i)) (qParam ^ (-(N - i))) _
      ?_ ?_ (famShift_cyclotomicKernel_sub_one_mul_eq j (N - i)) ih
    · rw [← zpow_add₀ qParam_ne_zero, add_neg_cancel, zpow_zero]
    · rw [← zpow_natCast, ← zpow_add₀ qParam_ne_zero, sub_add_cancel]

/-- The cyclotomic kernel at the colour `N - i`, times the common denominator, is the
cyclotomic kernel at the colour `N` times the `i`-th family basis polynomial. -/
theorem cyclotomicKernel_sub_mul_famBasisPoly (m j : ℕ) (N : ℤ) {i : ℕ} (hi : i ≤ 2 * m + 3) :
    cyclotomicKernel j (N - i) * (famBasisPoly m qParam 0).evalEval (qParam ^ N) (qParam ^ j) =
      cyclotomicKernel j N * (famBasisPoly m qParam i).evalEval (qParam ^ N) (qParam ^ j) := by
  rw [evalEval_famBasisPoly_eq, evalEval_famBasisPoly_eq,
    Finset.range_zero, Finset.prod_empty, one_mul, ← Nat.Ico_zero_eq_range,
    ← Finset.prod_Ico_consecutive _ (Nat.zero_le i) hi, Nat.Ico_zero_eq_range, ← mul_assoc,
    famShift_cyclotomicKernel_sub_mul_prod_range, mul_assoc]

end AJConjecture
