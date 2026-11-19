import Mathlib
import AJTwist.Quantum.TwQWindowSbp
import AJTwist.Exist.TwHTarget

/-!
# Adjunction for an arbitrary inner relation

Source: revision 5, Section 3.3: "The adjoint of `𝒵` in the sum against `C_j(N)` is `Z^*` … The
endpoints vanish by `1 - J = 0` and `C_N(N) = 0`." For the window `d ≥ 1` and `N > d` the
library's summation by parts `sum_twKernel_mul_cycloStep` moves one factor `V` across the kernel
`twKernel d` as `twAdjoint d` (no boundary terms, no degree condition on the numerator).

* `twH_sum_twKernel_mul_iterate_cycloStep`: the same for `V^s`
  (induction on `s`: `V^(s+1) y = V (V^s y)`, one summation by parts with the numerator `n`, then
  the induction hypothesis with the numerator `twAdjoint d q n`; `Function.iterate_succ_apply`
  and `Function.iterate_succ_apply'`).
* `twH_sum_twKernel_mul_target`: for the cleared target of `∑_{s ≤ r} ρ_s(J) V^s`,
  `∑_{j<N} G_j(N) 𝒯(q^N, q^j) y_j = (q^d q^N)^r ∑_{j<N} G_j(N) ∑_{s ≤ r} ρ_s(q^j) (V^s y)_j`
  for **every** sequence `y`. In particular the left side vanishes when `y` satisfies the
  relation `∑_s ρ_s(q^j) (V^s y)_j = 0`.

Checked in exact rationals for the windows `d = 1, …, 6` and in a prime field for
`d = 1, 2, 7, 12, 19` (even and odd windows; `N = d + 1, d + 2`, and `d + 3` for `t² = 2`;
random numerators of degree `≤ 4` in `J`, `≤ 9` in the prime field, and `≤ 3` in `x`; random
sequences; `s ≤ 3`; scratch `H/h02_sbp.py`, items (a), (b)).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Iterated summation by parts: the adjoint of `V^s` against the kernel of the window `d` is
the `s`-th iterate of `twAdjoint d`. -/
theorem twH_sum_twKernel_mul_iterate_cycloStep (d : ℕ) (hd : 1 ≤ d) {N : ℕ} (hN : d + 1 ≤ N)
    (s : ℕ) (n : (RatFunc ℚ)[X][X]) (y : ℕ → RatFunc ℚ) :
    (qParam ^ d * qParam ^ (N : ℤ)) ^ s *
        ∑ j ∈ Finset.range N,
          twKernel d j N * n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloStep^[s] y j =
      ∑ j ∈ Finset.range N, twKernel d j N *
        ((twAdjoint d qParam)^[s] n).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j := by
  induction s generalizing n with
  | zero =>
    rw [pow_zero, one_mul]
    rfl
  | succ s ih =>
    have hV : ∀ j : ℕ, cycloStep^[s + 1] y j = cycloStep (cycloStep^[s] y) j := fun j ↦ by
      rw [Function.iterate_succ_apply' cycloStep]
    simp only [hV]
    rw [Function.iterate_succ_apply (twAdjoint d qParam), ← ih (twAdjoint d qParam n),
      ← sum_twKernel_mul_cycloStep d hd hN n (cycloStep^[s] y), pow_succ, mul_assoc]

/-- The cleared target against the kernel: the weight `𝒯 / Δ` implements the inner operator
`∑_s ρ_s(J) V^s`, up to the factor `(q^d q^N)^r`. -/
theorem twH_sum_twKernel_mul_target (d : ℕ) (hd : 1 ≤ d) {N : ℕ} (hN : d + 1 ≤ N) (r : ℕ)
    (ρ : ℕ → (RatFunc ℚ)[X]) (y : ℕ → RatFunc ℚ) :
    ∑ j ∈ Finset.range N, twKernel d j N *
        (twHTarget d qParam r ρ).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j =
      (qParam ^ d * qParam ^ (N : ℤ)) ^ r *
        ∑ j ∈ Finset.range N, twKernel d j N *
          ∑ s ∈ Finset.range (r + 1), (ρ s).eval (qParam ^ j) * cycloStep^[s] y j := by
  have hterm : ∀ s ∈ Finset.range (r + 1),
      ∑ j ∈ Finset.range N, twKernel d j N *
        (C (C (qParam ^ d) * X) ^ (r - s) * (twAdjoint d qParam)^[s] ((ρ s).map C)).evalEval
          (qParam ^ (N : ℤ)) (qParam ^ j) * y j =
      (qParam ^ d * qParam ^ (N : ℤ)) ^ r *
        ∑ j ∈ Finset.range N, twKernel d j N * ((ρ s).eval (qParam ^ j) * cycloStep^[s] y j) := by
    intro s hs
    have hs' : s ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    have h := twH_sum_twKernel_mul_iterate_cycloStep d hd hN s ((ρ s).map C) y
    simp only [evalEval_map_C] at h
    simp only [evalEval_mul, evalEval_pow, evalEval_C, eval_mul, eval_C, eval_X]
    calc ∑ j ∈ Finset.range N, twKernel d j N * ((qParam ^ d * qParam ^ (N : ℤ)) ^ (r - s) *
          ((twAdjoint d qParam)^[s] ((ρ s).map C)).evalEval (qParam ^ (N : ℤ)) (qParam ^ j)) *
            y j
        = (qParam ^ d * qParam ^ (N : ℤ)) ^ (r - s) * ∑ j ∈ Finset.range N, twKernel d j N *
          ((twAdjoint d qParam)^[s] ((ρ s).map C)).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
            y j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          ring
      _ = (qParam ^ d * qParam ^ (N : ℤ)) ^ r * ∑ j ∈ Finset.range N, twKernel d j N *
          ((ρ s).eval (qParam ^ j) * cycloStep^[s] y j) := by
          rw [← h, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hs']
          simp only [mul_assoc]
  simp only [twHTarget, evalEval_finsetSum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.mul_sum]

end AJConjecture
