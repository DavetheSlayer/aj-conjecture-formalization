import Mathlib
import AJTwist.Quantum.TwQWindowKernel
import AJFamily.Quantum.FamSummationByParts

/-!
# Summation by parts for an arbitrary pole window (Unit Q4)

Source: revision 5, Section 3.3: "The adjoint of `𝒵` in the sum against `C_j(N)` is `Z^*` …
This follows by reindexing `B D_j` and using `C_(j+1)/C_j = (1 - q x J)(1 - q J / x)`. The
endpoints vanish by `1 - J = 0` and `C_N(N) = 0`."

For `N > d ≥ 1`, the operator `V = cycloStep` (multiplication by `Q + \hat Q` on the Bailey
kernel) moves across the kernel `twKernel d` as `twAdjoint d`, without boundary terms. This is
`AJFamily/Quantum/FamSummationByParts.lean` with `2m + 3` replaced by `d` (`2m + 2` by `d - 1`).
The trace operators are in `AJTwist.Quantum.TwQWindowSbpCheb`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value of `divX p` at a point, when the constant coefficient of `p` vanishes. -/
private theorem evalEval_divX_mul_of_coeff_zero_windowSbp {R : Type*} [CommRing R] (p : R[X][X])
    (h0 : p.coeff 0 = 0) (x y : R) : (divX p).evalEval x y * y = p.evalEval x y := by
  have h := divX_mul_X_add p
  rw [h0, C_0, add_zero] at h
  conv_rhs => rw [← h]
  rw [evalEval_mul, evalEval_X]

/-- The value at `(x, y)` of the substitution `J ↦ q J` is the value at `(x, q y)`. -/
private theorem evalEval_comp_C_mul_X_windowSbp {R : Type*} [CommRing R] (q x y : R)
    (n : R[X][X]) : (n.comp (C (C q) * X)).evalEval x y = n.evalEval x (q * y) := by
  simp only [evalEval, eval_comp, eval_mul, eval_C, eval_X, C_mul]

/-- The numerator divided by `J` in `twAdjoint` has no constant coefficient. -/
private theorem adjoint_numerator_coeff_zero_windowSbp {R : Type*} [CommRing R] (e : ℕ) (q : R)
    (n : R[X][X]) :
    (C (C (q ^ e) * X) * n -
      (1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ e)) - C X * X) *
        n.comp (C (C q) * X)).coeff 0 = 0 := by
  simp only [coeff_zero_eq_eval_zero, eval_sub, eval_mul, eval_C, eval_X, eval_comp, eval_one,
    mul_zero, sub_zero, one_mul]
  ring

/-- The value of the adjoint of a numerator at a point, cleared of the division by `J`. -/
private theorem evalEval_twAdjoint_mul_windowSbp {R : Type*} [CommRing R] (e : ℕ) (q x y : R)
    (n : R[X][X]) :
    (twAdjoint (e + 1) q n).evalEval x y * y =
      q ^ (e + 1) * x * y * n.evalEval x y * y + (q ^ e * x * n.evalEval x y -
        (1 - q * y) * (x - q * y) * (q ^ e - x * y) * n.evalEval x (q * y)) := by
  rw [twAdjoint, Nat.add_sub_cancel, evalEval_add, add_mul,
    evalEval_divX_mul_of_coeff_zero_windowSbp _ (adjoint_numerator_coeff_zero_windowSbp e q n)]
  simp only [evalEval_mul, evalEval_sub, evalEval_C, evalEval_X, evalEval_one,
    evalEval_comp_C_mul_X_windowSbp, eval_mul, eval_C, eval_X]

/-- The product `∏_{r ≤ e} (q^r - z)` under the substitution `z ↦ q z`. -/
private theorem prod_range_pow_sub_mul_shift_windowSbp {R : Type*} [CommRing R] (q z : R)
    (e : ℕ) :
    (∏ r ∈ Finset.range (e + 1), (q ^ r - z * q)) * (q ^ e - z) =
      q ^ e * (1 - z * q) * ∏ r ∈ Finset.range (e + 1), (q ^ r - z) := by
  induction e with
  | zero => simp only [zero_add, Finset.range_one, Finset.prod_singleton, pow_zero, one_mul]
  | succ e ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ _ (e + 1)]
    linear_combination q * (q ^ (e + 1) - z) * ih

/-- The common denominator under the substitution `J ↦ q J`. -/
private theorem evalEval_twBasisPoly_zero_mul_shift_windowSbp {R : Type*} [CommRing R] (e : ℕ)
    (q x y : R) :
    (twBasisPoly (e + 1) q 0).evalEval x (q * y) * (q ^ e - x * y) =
      q ^ e * (1 - q * x * y) * (twBasisPoly (e + 1) q 0).evalEval x y := by
  have h : (∏ r ∈ Finset.range (e + 1), (q ^ r - x * y * q)) * (q ^ e - x * y) =
      q ^ e * (1 - x * y * q) * ∏ r ∈ Finset.range (e + 1), (q ^ r - x * y) :=
    prod_range_pow_sub_mul_shift_windowSbp q (x * y) e
  simp only [twBasisPoly, Finset.range_zero, Finset.prod_empty, one_mul, evalEval_prod,
    evalEval_mul, evalEval_sub, evalEval_C, evalEval_X, eval_sub, eval_C, eval_X,
    Finset.prod_mul_distrib, Nat.Ico_zero_eq_range]
  rw [show x * (q * y) = x * y * q by ring]
  linear_combination (∏ r ∈ Finset.range (e + 1), (x - q ^ (r + 1))) * h

/-- The algebra of the ratio of two consecutive values of the kernel. -/
private theorem kernel_step_algebra_windowSbp {K : Type*} [CommRing K] (e a D0 D1 q J x u : K)
    (hxu : x * u = 1) (hD : D1 * (e - x * J) = e * (1 - q * x * J) * D0) :
    e * q * x * (a * ((1 - q * J * x) * (1 - q * J * u))) * D0 =
      a * ((x - q * J) * (e - x * J) * q) * D1 := by
  linear_combination (-(a * (x - q * J) * q)) * hD -
    e * q * a * (1 - q * J * x) * D0 * q * J * hxu

/-- The ratio of two consecutive values of the kernel, cleared of denominators. -/
private theorem twKernel_succ_mul_eq_windowSbp (e : ℕ) {N : ℕ} (hN : e + 2 ≤ N) (k : ℕ) :
    qParam ^ (e + 1) * qParam ^ (N : ℤ) * twKernel (e + 1) (k + 1) N =
      twKernel (e + 1) k N * ((qParam ^ (N : ℤ) - qParam * qParam ^ k) *
        (qParam ^ e - qParam ^ (N : ℤ) * qParam ^ k) * qParam) := by
  have hq := qParam_ne_zero
  have hD0 := twBasisPoly_zero_evalEval_ne_zero (e + 1) (N := (N : ℤ))
    (by exact_mod_cast hN) k
  have hD1 := twBasisPoly_zero_evalEval_ne_zero (e + 1) (N := (N : ℤ))
    (by exact_mod_cast hN) (k + 1)
  have hD := evalEval_twBasisPoly_zero_mul_shift_windowSbp e qParam (qParam ^ (N : ℤ))
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
  rw [twKernel, twKernel, hC, pow_succ' qParam k, mul_div_assoc',
    div_mul_eq_mul_div, div_eq_div_iff hD1 hD0, pow_succ qParam e]
  exact kernel_step_algebra_windowSbp _ _ _ _ _ _ _ _ hxu hD

/-- Two sums over `j < N` agree when the terms of the first are those of the second shifted by
one, the first term of the first and the last term of the second being zero. -/
private theorem sum_range_eq_sum_range_of_shift_windowSbp {K : Type*} [AddCommMonoid K]
    (a b : ℕ → K) {N : ℕ} (hN : 1 ≤ N) (h0 : a 0 = 0) (hlast : b (N - 1) = 0)
    (hstep : ∀ k : ℕ, a (k + 1) = b k) :
    ∑ j ∈ Finset.range N, a j = ∑ j ∈ Finset.range N, b j := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hlast
  rw [Finset.sum_range_succ', Finset.sum_range_succ, h0, hlast]
  exact congrArg (· + 0) (Finset.sum_congr rfl fun k _ ↦ hstep k)

/-- One term of the sum against the adjoint numerator, split into its diagonal part and its
shifted part. -/
private theorem twKernel_mul_evalEval_twAdjoint_windowSbp (e N : ℕ) (n : (RatFunc ℚ)[X][X])
    (y : ℕ → RatFunc ℚ) (j : ℕ) :
    twKernel (e + 1) j N *
        (twAdjoint (e + 1) qParam n).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j =
      qParam ^ (e + 1) * qParam ^ (N : ℤ) * (twKernel (e + 1) j N *
          n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
            (((qParam * qParam ^ j)⁻¹ + qParam ^ j) * y j)) -
        twKernel (e + 1) j N * ((1 - qParam * qParam ^ j) *
          (qParam ^ (N : ℤ) - qParam * qParam ^ j) *
            (qParam ^ e - qParam ^ (N : ℤ) * qParam ^ j)) *
              n.evalEval (qParam ^ (N : ℤ)) (qParam ^ (j + 1)) / qParam ^ j * y j := by
  have hq := qParam_ne_zero
  have hJ : qParam ^ j ≠ 0 := pow_ne_zero j hq
  rw [eq_div_of_mul_eq hJ
      (evalEval_twAdjoint_mul_windowSbp e qParam (qParam ^ (N : ℤ)) (qParam ^ j) n),
    pow_succ' qParam j, pow_succ qParam e]
  field_simp
  ring

/-- Summation by parts for the window `e + 1`. -/
private theorem sum_twKernel_succ_mul_cycloStep_windowSbp (e : ℕ) {N : ℕ} (hN : e + 2 ≤ N)
    (n : (RatFunc ℚ)[X][X]) (y : ℕ → RatFunc ℚ) :
    qParam ^ (e + 1) * qParam ^ (N : ℤ) *
        ∑ j ∈ Finset.range N,
          twKernel (e + 1) j N * n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloStep y j =
      ∑ j ∈ Finset.range N, twKernel (e + 1) j N *
        (twAdjoint (e + 1) qParam n).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j := by
  have hq := qParam_ne_zero
  have hshift : ∑ j ∈ Finset.range N, qParam ^ (e + 1) * qParam ^ (N : ℤ) *
      (twKernel (e + 1) j N * n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
        ((1 - qParam ^ j) / qParam ^ j * y (j - 1))) =
      ∑ j ∈ Finset.range N, twKernel (e + 1) j N * ((1 - qParam * qParam ^ j) *
        (qParam ^ (N : ℤ) - qParam * qParam ^ j) *
          (qParam ^ e - qParam ^ (N : ℤ) * qParam ^ j)) *
            n.evalEval (qParam ^ (N : ℤ)) (qParam ^ (j + 1)) / qParam ^ j * y j := by
    refine sum_range_eq_sum_range_of_shift_windowSbp _ _ (by omega) ?_ ?_ fun k ↦ ?_
    · simp only [pow_zero, sub_self, zero_div, zero_mul, mul_zero]
    · have hx : qParam ^ (N : ℤ) = qParam * qParam ^ (N - 1) := by
        rw [zpow_natCast, ← pow_succ', Nat.sub_add_cancel (by omega)]
      simp only [hx, sub_self, mul_zero, zero_mul, zero_div]
    · have hk : qParam ^ k ≠ 0 := pow_ne_zero k hq
      have hG := twKernel_succ_mul_eq_windowSbp e hN k
      rw [Nat.add_sub_cancel, pow_succ' qParam k, ← mul_assoc, ← mul_assoc, ← mul_assoc, hG]
      field_simp
  simp only [twKernel_mul_evalEval_twAdjoint_windowSbp]
  rw [Finset.sum_sub_distrib, ← hshift, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [cycloStep]
  ring

/-- Summation by parts: the adjoint of `V` against the kernel of the window `d` is
`twAdjoint d`. -/
theorem sum_twKernel_mul_cycloStep (d : ℕ) (hd : 1 ≤ d) {N : ℕ} (hN : d + 1 ≤ N)
    (n : (RatFunc ℚ)[X][X]) (y : ℕ → RatFunc ℚ) :
    qParam ^ d * qParam ^ (N : ℤ) *
        ∑ j ∈ Finset.range N,
          twKernel d j N * n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloStep y j =
      ∑ j ∈ Finset.range N, twKernel d j N *
        (twAdjoint d qParam n).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  exact sum_twKernel_succ_mul_cycloStep_windowSbp e hN n y

end AJConjecture
