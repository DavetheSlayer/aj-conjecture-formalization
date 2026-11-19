import Mathlib
import AJConjecture.QAlgCycloStep
import AJFamily.Quantum.FamTransferKernel

/-!
# Summation by parts against the family kernel

`sum_famKernel_mul_cycloStep`: for `N ≥ 2m + 4`, the operator `V = cycloStep` moves across the
family kernel as `famAdjoint`, without boundary terms.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The value of `divX p` at a point, when the constant coefficient of `p` vanishes. -/
private theorem famSbp_evalEval_divX_mul_of_coeff_zero {R : Type*} [CommRing R] (p : R[X][X])
    (h0 : p.coeff 0 = 0) (x y : R) : (divX p).evalEval x y * y = p.evalEval x y := by
  have h := divX_mul_X_add p
  rw [h0, C_0, add_zero] at h
  conv_rhs => rw [← h]
  rw [evalEval_mul, evalEval_X]

/-- The value at `(x, y)` of the substitution `J ↦ q J` is the value at `(x, q y)`. -/
private theorem famSbp_evalEval_comp_C_mul_X {R : Type*} [CommRing R] (q x y : R)
    (n : R[X][X]) : (n.comp (C (C q) * X)).evalEval x y = n.evalEval x (q * y) := by
  simp only [evalEval, eval_comp, eval_mul, eval_C, eval_X, C_mul]

/-- The numerator divided by `J` in `famAdjoint` has no constant coefficient. -/
private theorem famSbp_adjoint_numerator_coeff_zero {R : Type*} [CommRing R] (m : ℕ) (q : R)
    (n : R[X][X]) :
    (C (C (q ^ (2 * m + 2)) * X) * n -
      (1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ (2 * m + 2))) - C X * X) *
        n.comp (C (C q) * X)).coeff 0 = 0 := by
  simp only [coeff_zero_eq_eval_zero, eval_sub, eval_mul, eval_C, eval_X, eval_comp, eval_one,
    mul_zero, sub_zero, one_mul]
  ring

/-- The value of the adjoint of a numerator at a point, cleared of the division by `J`. -/
private theorem famSbp_evalEval_famAdjoint_mul {R : Type*} [CommRing R] (m : ℕ) (q x y : R)
    (n : R[X][X]) :
    (famAdjoint m q n).evalEval x y * y =
      q ^ (2 * m + 3) * x * y * n.evalEval x y * y + (q ^ (2 * m + 2) * x * n.evalEval x y -
        (1 - q * y) * (x - q * y) * (q ^ (2 * m + 2) - x * y) * n.evalEval x (q * y)) := by
  rw [famAdjoint, evalEval_add, add_mul,
    famSbp_evalEval_divX_mul_of_coeff_zero _ (famSbp_adjoint_numerator_coeff_zero m q n)]
  simp only [evalEval_mul, evalEval_sub, evalEval_C, evalEval_X, evalEval_one,
    famSbp_evalEval_comp_C_mul_X, eval_mul, eval_C, eval_X]

/-- The product `∏_{r ≤ m} (q^r - z)` under the substitution `z ↦ q z`. -/
private theorem famSbp_prod_range_pow_sub_mul_shift {R : Type*} [CommRing R] (q z : R) (m : ℕ) :
    (∏ r ∈ Finset.range (m + 1), (q ^ r - z * q)) * (q ^ m - z) =
      q ^ m * (1 - z * q) * ∏ r ∈ Finset.range (m + 1), (q ^ r - z) := by
  induction m with
  | zero => simp only [zero_add, Finset.range_one, Finset.prod_singleton, pow_zero, one_mul]
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ _ (m + 1)]
    linear_combination q * (q ^ (m + 1) - z) * ih

/-- The common denominator under the substitution `J ↦ q J`. -/
private theorem famSbp_evalEval_famBasisPoly_zero_mul_shift {R : Type*} [CommRing R] (m : ℕ)
    (q x y : R) :
    (famBasisPoly m q 0).evalEval x (q * y) * (q ^ (2 * m + 2) - x * y) =
      q ^ (2 * m + 2) * (1 - q * x * y) * (famBasisPoly m q 0).evalEval x y := by
  have h : (∏ r ∈ Finset.range (2 * m + 3), (q ^ r - x * y * q)) * (q ^ (2 * m + 2) - x * y) =
      q ^ (2 * m + 2) * (1 - x * y * q) * ∏ r ∈ Finset.range (2 * m + 3), (q ^ r - x * y) :=
    famSbp_prod_range_pow_sub_mul_shift q (x * y) (2 * m + 2)
  simp only [famBasisPoly, Finset.range_zero, Finset.prod_empty, one_mul, evalEval_prod,
    evalEval_mul, evalEval_sub, evalEval_C, evalEval_X, eval_sub, eval_C, eval_X,
    Finset.prod_mul_distrib, Nat.Ico_zero_eq_range]
  rw [show x * (q * y) = x * y * q by ring]
  linear_combination (∏ r ∈ Finset.range (2 * m + 3), (x - q ^ (r + 1))) * h

/-- The algebra of the ratio of two consecutive values of the family kernel. -/
private theorem famSbp_kernel_step_algebra {K : Type*} [CommRing K] (e a D0 D1 q J x u : K)
    (hxu : x * u = 1) (hD : D1 * (e - x * J) = e * (1 - q * x * J) * D0) :
    e * q * x * (a * ((1 - q * J * x) * (1 - q * J * u))) * D0 =
      a * ((x - q * J) * (e - x * J) * q) * D1 := by
  linear_combination (-(a * (x - q * J) * q)) * hD -
    e * q * a * (1 - q * J * x) * D0 * q * J * hxu

/-- The ratio of two consecutive values of the family kernel, cleared of denominators. -/
private theorem famSbp_famKernel_succ_mul_eq (m : ℕ) {N : ℕ} (hN : 2 * m + 4 ≤ N) (k : ℕ) :
    qParam ^ (2 * m + 3) * qParam ^ (N : ℤ) * famKernel m (k + 1) N =
      famKernel m k N * ((qParam ^ (N : ℤ) - qParam * qParam ^ k) *
        (qParam ^ (2 * m + 2) - qParam ^ (N : ℤ) * qParam ^ k) * qParam) := by
  have hq := qParam_ne_zero
  have hD0 := famBasisPoly_zero_evalEval_ne_zero m (N := (N : ℤ)) (by exact_mod_cast hN) k
  have hD1 := famBasisPoly_zero_evalEval_ne_zero m (N := (N : ℤ)) (by exact_mod_cast hN)
    (k + 1)
  have hD := famSbp_evalEval_famBasisPoly_zero_mul_shift m qParam (qParam ^ (N : ℤ))
    (qParam ^ k)
  have hxu : qParam ^ (N : ℤ) * qParam ^ (-(N : ℤ)) = 1 := by
    rw [← zpow_add₀ hq, add_neg_cancel, zpow_zero]
  have hC : cyclotomicKernel (k + 1) N = cyclotomicKernel k N *
      ((1 - qParam * qParam ^ k * qParam ^ (N : ℤ)) *
        (1 - qParam * qParam ^ k * qParam ^ (-(N : ℤ)))) := by
    have e1 : qParam ^ (((k + 1 : ℕ) : ℤ) + N) = qParam * qParam ^ k * qParam ^ (N : ℤ) := by
      rw [zpow_add₀ hq, zpow_natCast, pow_succ']
    have e2 : qParam ^ (((k + 1 : ℕ) : ℤ) - N) =
        qParam * qParam ^ k * qParam ^ (-(N : ℤ)) := by
      rw [sub_eq_add_neg, zpow_add₀ hq, zpow_natCast, pow_succ']
    unfold cyclotomicKernel
    rw [Finset.prod_Icc_succ_top (by omega), e1, e2]
  rw [pow_succ' qParam k] at hD1
  rw [famKernel, famKernel, hC, pow_succ' qParam k, mul_div_assoc',
    div_mul_eq_mul_div, div_eq_div_iff hD1 hD0, show 2 * m + 3 = (2 * m + 2) + 1 from rfl,
    pow_succ]
  exact famSbp_kernel_step_algebra _ _ _ _ _ _ _ _ hxu hD

/-- Two sums over `j < N` agree when the terms of the first are those of the second shifted by
one, the first term of the first and the last term of the second being zero. -/
private theorem famSbp_sum_range_eq_sum_range_of_shift {K : Type*} [AddCommMonoid K]
    (a b : ℕ → K) {N : ℕ} (hN : 1 ≤ N) (h0 : a 0 = 0) (hlast : b (N - 1) = 0)
    (hstep : ∀ k : ℕ, a (k + 1) = b k) :
    ∑ j ∈ Finset.range N, a j = ∑ j ∈ Finset.range N, b j := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hlast
  rw [Finset.sum_range_succ', Finset.sum_range_succ, h0, hlast]
  exact congrArg (· + 0) (Finset.sum_congr rfl fun k _ ↦ hstep k)

/-- One term of the sum against the adjoint numerator, split into its diagonal part and its
shifted part. -/
private theorem famSbp_famKernel_mul_evalEval_famAdjoint (m N : ℕ) (n : (RatFunc ℚ)[X][X])
    (y : ℕ → RatFunc ℚ) (j : ℕ) :
    famKernel m j N *
        (famAdjoint m qParam n).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j =
      qParam ^ (2 * m + 3) * qParam ^ (N : ℤ) * (famKernel m j N *
          n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
            (((qParam * qParam ^ j)⁻¹ + qParam ^ j) * y j)) -
        famKernel m j N * ((1 - qParam * qParam ^ j) *
          (qParam ^ (N : ℤ) - qParam * qParam ^ j) *
            (qParam ^ (2 * m + 2) - qParam ^ (N : ℤ) * qParam ^ j)) *
              n.evalEval (qParam ^ (N : ℤ)) (qParam ^ (j + 1)) / qParam ^ j * y j := by
  have hq := qParam_ne_zero
  have hJ : qParam ^ j ≠ 0 := pow_ne_zero j hq
  rw [eq_div_of_mul_eq hJ
      (famSbp_evalEval_famAdjoint_mul m qParam (qParam ^ (N : ℤ)) (qParam ^ j) n),
    pow_succ' qParam j, show 2 * m + 3 = (2 * m + 2) + 1 from rfl, pow_succ]
  field_simp
  ring

/-- Summation by parts: the adjoint of `V` against the family kernel is `famAdjoint`. -/
theorem sum_famKernel_mul_cycloStep (m : ℕ) {N : ℕ} (hN : 2 * m + 4 ≤ N)
    (n : (RatFunc ℚ)[X][X]) (y : ℕ → RatFunc ℚ) :
    qParam ^ (2 * m + 3) * qParam ^ (N : ℤ) *
        ∑ j ∈ Finset.range N,
          famKernel m j N * n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloStep y j =
      ∑ j ∈ Finset.range N, famKernel m j N *
        (famAdjoint m qParam n).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j := by
  have hq := qParam_ne_zero
  have hshift : ∑ j ∈ Finset.range N, qParam ^ (2 * m + 3) * qParam ^ (N : ℤ) *
      (famKernel m j N * n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
        ((1 - qParam ^ j) / qParam ^ j * y (j - 1))) =
      ∑ j ∈ Finset.range N, famKernel m j N * ((1 - qParam * qParam ^ j) *
        (qParam ^ (N : ℤ) - qParam * qParam ^ j) *
          (qParam ^ (2 * m + 2) - qParam ^ (N : ℤ) * qParam ^ j)) *
            n.evalEval (qParam ^ (N : ℤ)) (qParam ^ (j + 1)) / qParam ^ j * y j := by
    refine famSbp_sum_range_eq_sum_range_of_shift _ _ (by omega) ?_ ?_ fun k ↦ ?_
    · simp only [pow_zero, sub_self, zero_div, zero_mul, mul_zero]
    · have hx : qParam ^ (N : ℤ) = qParam * qParam ^ (N - 1) := by
        rw [zpow_natCast, ← pow_succ', Nat.sub_add_cancel (by omega)]
      simp only [hx, sub_self, mul_zero, zero_mul, zero_div]
    · have hk : qParam ^ k ≠ 0 := pow_ne_zero k hq
      have hG := famSbp_famKernel_succ_mul_eq m hN k
      rw [Nat.add_sub_cancel, pow_succ' qParam k, ← mul_assoc, ← mul_assoc, ← mul_assoc, hG]
      field_simp
  simp only [famSbp_famKernel_mul_evalEval_famAdjoint]
  rw [Finset.sum_sub_distrib, ← hshift, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [cycloStep]
  ring

end AJConjecture
