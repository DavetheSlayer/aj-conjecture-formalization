import Mathlib
import AJTwist.Quantum.TwQTarget
import AJTwist.Quantum.TwQWindowSbpCheb
import AJTwist.Quantum.TwQDefect
import AJHandoff.TorusQuantum.PairQTargetSum

/-!
# Adjunction: the cleared numerator against the inner operator (Unit Q4)

Source: revision 5, Section 3.3: "Adjunction places the left multipliers of `p_a` on the seeds
before applying the trace polynomials. The cleared numerator is [eq. (adjointnumerator)]".

For every integer `a`, every input `u` and `N > d = twWindow a`:
`∑_{j<N} G_j(N) 𝒯_a(q^N, q^j) D_j = (q^d q^N)^(|a|+1) ∑_{j<N} G_j(N) (p_a D)_j`,
with `𝒯_a = twTarget a q`, `G = twKernel d` and `p_a D = twDefect a u`.

* `a ≥ 1`: the library's `pairQ_sum_famKernel_mul_famTarget` (with `famKernel_eq_twKernel`,
  `twTarget_natCast`, `twDefect_natCast`);
* `a = 0` (`twQ_sum_twKernel_mul_zeroTarget`): `sum_twKernel_mul_cycloStep` with the seed
  `1 - J`, and the multiplication term `2 q³ x (1 - qJ)`;
* `a = -b` (`twQ_sum_twKernel_mul_negTarget`): `sum_twKernel_mul_cycloCheb` with
  `(k, seed) = (b+1, 1), (b, 1 - qJ), (b-1, J)` and the weights `q, q^d x, (q^d x)²`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Adjunction at `a = 0` (window `3`). -/
theorem twQ_sum_twKernel_mul_zeroTarget (u : ℕ → RatFunc ℚ) {N : ℕ} (hN : 4 ≤ N) :
    ∑ j ∈ Finset.range N, twKernel 3 j N *
        (twZeroTarget qParam).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * pairQCycloCoeff u j =
      qParam ^ 3 * qParam ^ (N : ℤ) *
        ∑ j ∈ Finset.range N, twKernel 3 j N * twDefect 0 u j := by
  have h := sum_twKernel_mul_cycloStep 3 (by norm_num) hN (1 - X) (pairQCycloCoeff u)
  have hL : ∑ j ∈ Finset.range N, twKernel 3 j N *
      (twZeroTarget qParam).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * pairQCycloCoeff u j =
      qParam * (∑ j ∈ Finset.range N, twKernel 3 j N *
        (twAdjoint 3 qParam (1 - X)).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          pairQCycloCoeff u j) +
      2 * (qParam ^ 3 * qParam ^ (N : ℤ)) * ∑ j ∈ Finset.range N, twKernel 3 j N *
        ((1 - qParam * qParam ^ j) * pairQCycloCoeff u j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [twZeroTarget, two_mul, evalEval_add, evalEval_mul, evalEval_sub, evalEval_one,
      evalEval_C, evalEval_X, eval_mul, eval_C, eval_X]
    ring
  have hR : ∑ j ∈ Finset.range N, twKernel 3 j N * twDefect 0 u j =
      qParam * (∑ j ∈ Finset.range N, twKernel 3 j N *
        (1 - X : (RatFunc ℚ)[X][X]).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          cycloStep (pairQCycloCoeff u) j) +
      2 * ∑ j ∈ Finset.range N, twKernel 3 j N *
        ((1 - qParam * qParam ^ j) * pairQCycloCoeff u j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [twDefect_zero, evalEval_sub, evalEval_one, evalEval_X]
    ring
  rw [hL, hR]
  linear_combination (-qParam) * h

/-- Adjunction at `a = -b < 0` (window `2b + 2`). -/
theorem twQ_sum_twKernel_mul_negTarget (b : ℕ) (hb : 1 ≤ b) (u : ℕ → RatFunc ℚ) {N : ℕ}
    (hN : 2 * b + 3 ≤ N) :
    ∑ j ∈ Finset.range N, twKernel (2 * b + 2) j N *
        (twNegTarget b qParam).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * pairQCycloCoeff u j =
      (qParam ^ (2 * b + 2) * qParam ^ (N : ℤ)) ^ (b + 1) *
        ∑ j ∈ Finset.range N, twKernel (2 * b + 2) j N * twDefect (-(b : ℤ)) u j := by
  have hd : 1 ≤ 2 * b + 2 := by omega
  have h1 := sum_twKernel_mul_cycloCheb (2 * b + 2) hd hN (b + 1) 1 (pairQCycloCoeff u)
  have h2 := sum_twKernel_mul_cycloCheb (2 * b + 2) hd hN b (1 - C (C qParam) * X)
    (pairQCycloCoeff u)
  have h3 := sum_twKernel_mul_cycloCheb (2 * b + 2) hd hN (b - 1) X (pairQCycloCoeff u)
  set Q := qParam ^ (2 * b + 2) * qParam ^ (N : ℤ) with hQ
  have hL : ∑ j ∈ Finset.range N, twKernel (2 * b + 2) j N *
      (twNegTarget b qParam).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * pairQCycloCoeff u j =
      qParam ^ b * (qParam * (∑ j ∈ Finset.range N, twKernel (2 * b + 2) j N *
        (twCheb (2 * b + 2) qParam (b + 1) 1).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          pairQCycloCoeff u j) +
      Q * (∑ j ∈ Finset.range N, twKernel (2 * b + 2) j N *
        (twCheb (2 * b + 2) qParam b (1 - C (C qParam) * X)).evalEval (qParam ^ (N : ℤ))
          (qParam ^ j) * pairQCycloCoeff u j) -
      Q ^ 2 * ∑ j ∈ Finset.range N, twKernel (2 * b + 2) j N *
        (twCheb (2 * b + 2) qParam (b - 1) X).evalEval (qParam ^ (N : ℤ))
          (qParam ^ j) * pairQCycloCoeff u j) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [twNegTarget, evalEval_mul, evalEval_sub, evalEval_add, evalEval_mul, evalEval_mul,
      evalEval_mul, evalEval_C, evalEval_C, evalEval_C, evalEval_C, eval_pow, eval_mul,
      eval_C, eval_C, eval_C, eval_X]
    ring
  have hR : ∑ j ∈ Finset.range N, twKernel (2 * b + 2) j N * twDefect (-(b : ℤ)) u j =
      qParam ^ b * (qParam * (∑ j ∈ Finset.range N, twKernel (2 * b + 2) j N *
        (1 : (RatFunc ℚ)[X][X]).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          cycloCheb (b + 1) (pairQCycloCoeff u) j) +
      (∑ j ∈ Finset.range N, twKernel (2 * b + 2) j N *
        (1 - C (C qParam) * X : (RatFunc ℚ)[X][X]).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          cycloCheb b (pairQCycloCoeff u) j) -
      ∑ j ∈ Finset.range N, twKernel (2 * b + 2) j N *
        (X : (RatFunc ℚ)[X][X]).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          cycloCheb (b - 1) (pairQCycloCoeff u) j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [twDefect_neg_natCast b hb, evalEval_sub, evalEval_one, evalEval_mul, evalEval_C,
      evalEval_X, eval_C]
    ring
  rw [hL, hR]
  have e2 : Q ^ (b + 1) = Q * Q ^ b := pow_succ' Q b
  have e3 : Q ^ (b + 1) = Q ^ 2 * Q ^ (b - 1) := by
    rw [← pow_add]; congr 1; omega
  linear_combination (-(qParam ^ b * qParam)) * h1 - qParam ^ b * Q * h2 +
    qParam ^ b * Q ^ 2 * h3 +
    qParam ^ b * (∑ j ∈ Finset.range N, twKernel (2 * b + 2) j N *
      (1 - C (C qParam) * X : (RatFunc ℚ)[X][X]).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
        cycloCheb b (pairQCycloCoeff u) j) * e2 +
    qParam ^ b * (∑ j ∈ Finset.range N, twKernel (2 * b + 2) j N *
      (X : (RatFunc ℚ)[X][X]).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
        cycloCheb (b - 1) (pairQCycloCoeff u) j) * e3

/-- Adjunction for every integer `a`. -/
theorem twQ_sum_twKernel_mul_twTarget (a : ℤ) (u : ℕ → RatFunc ℚ) {N : ℕ}
    (hN : twWindow a + 1 ≤ N) :
    ∑ j ∈ Finset.range N, twKernel (twWindow a) j N *
        (twTarget a qParam).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * pairQCycloCoeff u j =
      (qParam ^ twWindow a * qParam ^ (N : ℤ)) ^ (a.natAbs + 1) *
        ∑ j ∈ Finset.range N, twKernel (twWindow a) j N * twDefect a u j := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.cast_zero, twWindow_zero] at hN ⊢
      rw [twTarget_zero, Int.natAbs_zero, zero_add, pow_one]
      exact twQ_sum_twKernel_mul_zeroTarget u hN
    · rw [twWindow_natCast] at hN ⊢
      rw [twTarget_natCast m hm, twDefect_natCast m hm, Int.natAbs_natCast]
      exact pairQ_sum_famKernel_mul_famTarget m hm u hN
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.cast_zero, neg_zero, twWindow_zero] at hN ⊢
      rw [twTarget_zero, Int.natAbs_zero, zero_add, pow_one]
      exact twQ_sum_twKernel_mul_zeroTarget u hN
    · rw [twWindow_neg_natCast m hm] at hN ⊢
      rw [twTarget_neg_natCast m hm, Int.natAbs_neg, Int.natAbs_natCast]
      exact twQ_sum_twKernel_mul_negTarget m hm u hN

end AJConjecture
