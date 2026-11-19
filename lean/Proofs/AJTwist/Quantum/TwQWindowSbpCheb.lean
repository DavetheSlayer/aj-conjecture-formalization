import Mathlib
import AJTwist.Quantum.TwQWindowSbp
import AJFamily.Quantum.FamSummationCheb

/-!
# The trace operators against the kernel of an arbitrary pole window (Unit Q4)

Source: revision 5, Section 3.3: "Adjunction places the left multipliers of `p_a` on the seeds
before applying the trace polynomials."

`sum_twKernel_mul_cycloCheb`: for `N > d ≥ 1` the trace operator `S_k(V) = cycloCheb k` moves
across the kernel `twKernel d` as `twCheb d q k`, with the factor `(q^d q^N)^k`. This is
`AJFamily/Quantum/FamSummationCheb.lean` with `2m + 3` replaced by `d` (`4m + 5` by `2d - 1`):
two-step induction on `k` from `sum_twKernel_mul_cycloStep`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The adjoint of the trace operator `S_k(V)` against the kernel of the window `d` is
`twCheb d q k`. -/
theorem sum_twKernel_mul_cycloCheb (d : ℕ) (hd : 1 ≤ d) {N : ℕ} (hN : d + 1 ≤ N) (k : ℕ)
    (n : (RatFunc ℚ)[X][X]) (y : ℕ → RatFunc ℚ) :
    (qParam ^ d * qParam ^ (N : ℤ)) ^ k *
        ∑ j ∈ Finset.range N,
          twKernel d j N * n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloCheb k y j =
      ∑ j ∈ Finset.range N, twKernel d j N *
        (twCheb d qParam k n).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  induction k using Nat.twoStepInduction generalizing n with
  | zero =>
    rw [pow_zero, one_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [cycloCheb, twCheb, two_mul, evalEval_add]
    ring
  | one =>
    rw [pow_one]
    exact sum_twKernel_mul_cycloStep (e + 1) hd hN n y
  | more k ih0 ih1 =>
    have hqi : qParam * qParam⁻¹ = 1 := mul_inv_cancel₀ qParam_ne_zero
    have h1 := ih1 (twAdjoint (e + 1) qParam n)
    have h0 := ih0 n
    have hs := sum_twKernel_mul_cycloStep (e + 1) hd hN n (cycloCheb (k + 1) y)
    have hL : ∑ j ∈ Finset.range N, twKernel (e + 1) j N *
        n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloCheb (k + 2) y j =
        (∑ j ∈ Finset.range N, twKernel (e + 1) j N *
          n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloStep (cycloCheb (k + 1) y) j) -
        qParam⁻¹ * ∑ j ∈ Finset.range N, twKernel (e + 1) j N *
          n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloCheb k y j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [cycloCheb]
      ring
    have hR : ∑ j ∈ Finset.range N, twKernel (e + 1) j N *
        (twCheb (e + 1) qParam (k + 2) n).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j =
        (∑ j ∈ Finset.range N, twKernel (e + 1) j N * (twCheb (e + 1) qParam (k + 1)
          (twAdjoint (e + 1) qParam n)).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j) -
        qParam ^ (2 * e + 1) * (qParam ^ (N : ℤ)) ^ 2 *
          ∑ j ∈ Finset.range N, twKernel (e + 1) j N *
          (twCheb (e + 1) qParam k n).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [twCheb, show 2 * (e + 1) - 1 = 2 * e + 1 by omega, evalEval_sub, evalEval_mul,
        evalEval_C, eval_mul, eval_C, eval_pow, eval_X]
      ring
    rw [hL, hR]
    linear_combination (qParam ^ (e + 1) * qParam ^ (N : ℤ)) ^ (k + 1) * hs + h1 -
      qParam ^ (2 * e + 1) * (qParam ^ (N : ℤ)) ^ 2 * h0 -
      (qParam ^ (e + 1) * qParam ^ (N : ℤ)) ^ k *
        (∑ j ∈ Finset.range N, twKernel (e + 1) j N *
          n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloCheb k y j) * qParam ^ (2 * e + 1) *
            (qParam ^ (N : ℤ)) ^ 2 * hqi

end AJConjecture
