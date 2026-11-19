import Mathlib
import AJTwist.Quantum.TwQWindowPoly
import AJFamily.Quantum.FamTransferKernel
import AJHandoff.TorusQuantum.PairQFormula

/-!
# The summation kernel and the shifted colours for an arbitrary pole window (Unit Q4)

Source: revision 5, Section 3.3: "The cleared product relation `C_j(N) R_i(q^j) = C_j(N - i)`
implements the shift of the external color, including zero terms for `j ≥ N - i`", and the
denominator checks for `N > d`.

* `twKernel d j N = C_j(N) / P_0(q^N, q^j)` (the library's `famKernel m` for `d = 2m + 3`);
* `twBasisPoly_zero_evalEval_ne_zero`: the common denominator does not vanish for `N > d`;
* `cyclotomicKernel_sub_mul_twBasisPoly`: `C_j(N - i) P_0 = C_j(N) P_i` at `(q^N, q^j)`, `i ≤ d`;
* `twQ_reducedFormula_sub_eq_sum_twKernel`: for every input `u`,
  `F_(N-i) = ∑_{j<N} G_j(N) P_i(q^N, q^j) D_j`.

These are `AJFamily/Quantum/FamKernelShift.lean`, `FamTransferKernel.lean` and
`AJHandoff/TorusQuantum/PairQReducedShift.lean` with `2m + 3` replaced by `d`; nothing in their
proofs uses the parity of the window.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The summation kernel `G_j(N) = C_j(N) / P_0(q^N, q^j)` of the pole window `d`. -/
def twKernel (d : ℕ) (j : ℕ) (N : ℤ) : RatFunc ℚ :=
  cyclotomicKernel j N / (twBasisPoly d qParam 0).evalEval (qParam ^ N) (qParam ^ j)

theorem famKernel_eq_twKernel (m j : ℕ) (N : ℤ) : famKernel m j N = twKernel (2 * m + 3) j N :=
  rfl

/-- The value of a basis polynomial at a point, as a product. -/
theorem evalEval_twBasisPoly_eq {R : Type*} [CommRing R] (d : ℕ) (q x y : R) (i : ℕ) :
    (twBasisPoly d q i).evalEval x y =
      (∏ r ∈ Finset.range i, ((q ^ r - x) * (x - q ^ (r + 1) * y))) *
        ∏ r ∈ Finset.Ico i d, ((x - q ^ (r + 1)) * (q ^ r - x * y)) := by
  simp only [twBasisPoly, evalEval_prod, evalEval_mul, evalEval_sub, evalEval_C,
    evalEval_X, eval_sub, eval_C, eval_X]

/-- The common denominator `P_0(q^N, q^j)` does not vanish for `N > d`. -/
theorem twBasisPoly_zero_evalEval_ne_zero (d : ℕ) {N : ℤ} (hN : (d : ℤ) + 1 ≤ N) (j : ℕ) :
    (twBasisPoly d qParam 0).evalEval (qParam ^ N) (qParam ^ j) ≠ 0 := by
  have hpow : ∀ a b : ℤ, a ≠ b → qParam ^ a - qParam ^ b ≠ 0 := fun a b hab h ↦
    hab (qParam_zpow_injective (sub_eq_zero.mp h))
  rw [evalEval_twBasisPoly_eq, Finset.range_zero, Finset.prod_empty, one_mul,
    Finset.prod_ne_zero_iff]
  intro r hr
  have hr' : r < d := (Finset.mem_Ico.mp hr).2
  refine mul_ne_zero ?_ ?_
  · have h := hpow N ((r + 1 : ℕ) : ℤ) (by omega)
    rwa [zpow_natCast] at h
  · have h := hpow (r : ℤ) (N + j) (by omega)
    rwa [zpow_natCast, zpow_add₀ qParam_ne_zero, zpow_natCast] at h

/-- An integer power of `q` whose exponent is a natural number plus an integer. -/
private theorem qParam_zpow_eq_pow_mul_zpow_windowKernel (n : ℕ) (K e : ℤ) (h : e = n + K) :
    qParam ^ e = qParam ^ n * qParam ^ K := by
  subst h
  rw [zpow_add₀ qParam_ne_zero, zpow_natCast]

/-- The cyclotomic kernel with one more factor. -/
private theorem cyclotomicKernel_succ_eq_mul_windowKernel (j : ℕ) (K : ℤ) :
    cyclotomicKernel (j + 1) K = cyclotomicKernel j K *
      ((1 - qParam ^ (((j + 1 : ℕ) : ℤ) + K)) *
        (1 - qParam ^ (((j + 1 : ℕ) : ℤ) - K))) := by
  unfold cyclotomicKernel
  rw [Finset.prod_Icc_succ_top (by omega)]

/-- The cyclotomic kernels at two consecutive colours. -/
private theorem cyclotomicKernel_sub_one_mul_eq_windowKernel (j : ℕ) (M : ℤ) :
    cyclotomicKernel j (M - 1) *
        ((1 - qParam ^ j * qParam ^ M) * (1 - qParam * qParam ^ (-M))) =
      cyclotomicKernel j M *
        ((1 - qParam ^ M) * (1 - qParam ^ j * qParam * qParam ^ (-M))) := by
  induction j with
  | zero => simp only [cyclotomicKernel, pow_zero, one_mul, zero_lt_one, Finset.Icc_eq_empty_of_lt,
      Finset.prod_empty]
  | succ j ih =>
    rw [cyclotomicKernel_succ_eq_mul_windowKernel, cyclotomicKernel_succ_eq_mul_windowKernel,
      qParam_zpow_eq_pow_mul_zpow_windowKernel j M (((j + 1 : ℕ) : ℤ) + (M - 1))
        (by push_cast; ring),
      qParam_zpow_eq_pow_mul_zpow_windowKernel (j + 2) (-M) (((j + 1 : ℕ) : ℤ) - (M - 1))
        (by push_cast; ring),
      qParam_zpow_eq_pow_mul_zpow_windowKernel (j + 1) M (((j + 1 : ℕ) : ℤ) + M) rfl,
      qParam_zpow_eq_pow_mul_zpow_windowKernel (j + 1) (-M) (((j + 1 : ℕ) : ℤ) - M) (by ring)]
    linear_combination
      (1 - qParam ^ (j + 2) * qParam ^ (-M)) * (1 - qParam ^ (j + 1) * qParam ^ M) * ih

/-- The algebra of one step of the shift of the cyclotomic kernel. -/
private theorem kernelShift_step_algebra_windowKernel {K : Type*} [CommRing K]
    (A' A B P P' p a J u v x : K) (huv : u * v = 1) (hx : x = u * p)
    (hstep : A' * ((1 - J * u) * (1 - a * v)) = A * ((1 - u) * (1 - J * a * v)))
    (ih : A * P = B * P') :
    A' * (P * ((x - p * a) * (p - x * J))) = B * (P' * ((p - x) * (x - p * a * J))) := by
  subst hx
  linear_combination P * p ^ 2 * u * hstep +
    (A' * P * p ^ 2 * (1 - u * J) * a - P * p ^ 2 * A * (1 - u) * a * J) * huv +
    p ^ 2 * (1 - u) * (u - a * J) * ih

/-- The shift of the cyclotomic kernel by `i`, against the first `i` factors. -/
private theorem cyclotomicKernel_sub_mul_prod_range_windowKernel (j : ℕ) (N : ℤ) (i : ℕ) :
    cyclotomicKernel j (N - i) * ∏ r ∈ Finset.range i,
        ((qParam ^ N - qParam ^ (r + 1)) * (qParam ^ r - qParam ^ N * qParam ^ j)) =
      cyclotomicKernel j N * ∏ r ∈ Finset.range i,
        ((qParam ^ r - qParam ^ N) * (qParam ^ N - qParam ^ (r + 1) * qParam ^ j)) := by
  induction i with
  | zero => simp only [Nat.cast_zero, sub_zero, Finset.range_zero, Finset.prod_empty]
  | succ i ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ,
      show N - ((i + 1 : ℕ) : ℤ) = N - i - 1 by push_cast; ring, pow_succ qParam i]
    refine kernelShift_step_algebra_windowKernel _ _ _ _ _ _ _ _ (qParam ^ (N - i))
      (qParam ^ (-(N - i))) _ ?_ ?_ (cyclotomicKernel_sub_one_mul_eq_windowKernel j (N - i)) ih
    · rw [← zpow_add₀ qParam_ne_zero, add_neg_cancel, zpow_zero]
    · rw [← zpow_natCast, ← zpow_add₀ qParam_ne_zero, sub_add_cancel]

/-- The cyclotomic kernel `C_j(M)` vanishes for `1 ≤ M ≤ j`: the factor `s = M` is zero. -/
private theorem cyclotomicKernel_natCast_eq_zero_of_le_windowKernel {j M : ℕ} (hM : 1 ≤ M)
    (hj : M ≤ j) : cyclotomicKernel j (M : ℤ) = 0 := by
  unfold cyclotomicKernel
  refine Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hM, hj⟩) ?_
  rw [sub_self, zpow_zero, sub_self, mul_zero]

/-- `C_j(N - i) P_0(q^N, q^j) = C_j(N) P_i(q^N, q^j)` for `i ≤ d`. -/
theorem cyclotomicKernel_sub_mul_twBasisPoly (d j : ℕ) (N : ℤ) {i : ℕ} (hi : i ≤ d) :
    cyclotomicKernel j (N - i) * (twBasisPoly d qParam 0).evalEval (qParam ^ N) (qParam ^ j) =
      cyclotomicKernel j N * (twBasisPoly d qParam i).evalEval (qParam ^ N) (qParam ^ j) := by
  rw [evalEval_twBasisPoly_eq, evalEval_twBasisPoly_eq,
    Finset.range_zero, Finset.prod_empty, one_mul, ← Nat.Ico_zero_eq_range,
    ← Finset.prod_Ico_consecutive _ (Nat.zero_le i) hi, Nat.Ico_zero_eq_range, ← mul_assoc,
    cyclotomicKernel_sub_mul_prod_range_windowKernel, mul_assoc]

/-- The shifted colours as sums against the kernel: `F_(N-i) = ∑_{j<N} G_j(N) P_i D_j`. -/
theorem twQ_reducedFormula_sub_eq_sum_twKernel (d : ℕ) (u : ℕ → RatFunc ℚ) {N : ℕ}
    (hN : d + 1 ≤ N) {i : ℕ} (hi : i ≤ d) :
    pairQReducedFormula u (N - i) =
      ∑ j ∈ Finset.range N, twKernel d j N *
        (twBasisPoly d qParam i).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          pairQCycloCoeff u j := by
  have hcast : ((N - i : ℕ) : ℤ) = (N : ℤ) - i := by omega
  have hterm : ∀ j : ℕ, twKernel d j N *
      (twBasisPoly d qParam i).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) =
        cyclotomicKernel j ((N - i : ℕ) : ℤ) := by
    intro j
    have hΔ := twBasisPoly_zero_evalEval_ne_zero d (N := (N : ℤ)) (by omega) j
    rw [twKernel, div_mul_eq_mul_div, div_eq_iff hΔ, hcast,
      cyclotomicKernel_sub_mul_twBasisPoly d j N hi]
  simp only [hterm]
  rw [pairQReducedFormula]
  refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.sub_le N i)) fun j _ hj ↦ ?_
  rw [Finset.mem_range, not_lt] at hj
  rw [cyclotomicKernel_natCast_eq_zero_of_le_windowKernel (by omega) hj, zero_mul]

end AJConjecture
