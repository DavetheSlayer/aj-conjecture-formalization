import Mathlib
import AJFamily.Quantum.FamDetNeZero
import AJHandoff.TorusQuantum.PairQFormula

/-!
# The right-hand side of the transfer identity is eventually nonzero

If `e_0 ≠ 0` (and `c ≥ 1`), then `pairQTransferRhs m c e n ≠ 0` for all large `n`. Route (as
`exists_forall_ge_opApplyField_famTransferOp_ne_zero`): `𝒟(q^N) ≠ 0` for `N ≥ 2m + 4`
(`famDet_eval_ne_zero`); clearing the denominators of `∑_{j<c} G_j(N) e_j` gives the value at
`x = q^N` of a polynomial `ρ(x)` times a nonzero factor; at `x = q^(d-1)` every term `j ≠ 0` of `ρ`
vanishes (factor `i = 0, r = d - 1`) and the term `j = 0` is `e_0` times a product of differences
of distinct powers of `q`; so `ρ ≠ 0` and `ρ(q^N) ≠ 0` for all large `N`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The polynomial `∏_{r<d} (q^r - x q^j)`, `d = 2m + 3`: the factor depending on `j` of the
common denominator of the transfer kernel. -/
private noncomputable def pairQRhsDenomPoly (m j : ℕ) : (RatFunc ℚ)[X] :=
  ∏ r ∈ Finset.range (2 * m + 3), (C (qParam ^ r) - X * C (qParam ^ j))

/-- The polynomial `x^(c-1-j) ∏_{s=1}^{j} (1 - q^s x) (x - q^s)`, whose value at `x = q^N` is
`x^(c-1) C_j(N)` for `j ≤ c - 1`. -/
private noncomputable def pairQRhsNumPoly (c j : ℕ) : (RatFunc ℚ)[X] :=
  X ^ (c - 1 - j) * ∏ s ∈ Finset.Icc 1 j, ((1 - C (qParam ^ s) * X) * (X - C (qParam ^ s)))

/-- The right-hand side of the transfer identity with denominators cleared, as a polynomial in
`x = q^N`. -/
private noncomputable def pairQRhsPoly (m c : ℕ) (e : ℕ → RatFunc ℚ) : (RatFunc ℚ)[X] :=
  ∑ j ∈ Finset.range c, C (e j) * pairQRhsNumPoly c j *
    ∏ i ∈ (Finset.range c).erase j, pairQRhsDenomPoly m i

/-- The value of the `j`-dependent factor of the common denominator. -/
private theorem eval_pairQRhsDenomPoly (m j : ℕ) (x : RatFunc ℚ) :
    (pairQRhsDenomPoly m j).eval x =
      ∏ r ∈ Finset.range (2 * m + 3), (qParam ^ r - x * qParam ^ j) := by
  simp only [pairQRhsDenomPoly, eval_prod, eval_sub, eval_mul, eval_C, eval_X]

/-- The value at `x = q^N` of the numerator polynomial is `x^(c-1) C_j(N)`. -/
private theorem eval_pairQRhsNumPoly {c j : ℕ} (hj : j ≤ c - 1) (N : ℤ) :
    (pairQRhsNumPoly c j).eval (qParam ^ N) = (qParam ^ N) ^ (c - 1) * cyclotomicKernel j N := by
  have hq := qParam_ne_zero
  have hx : qParam ^ N ≠ 0 := zpow_ne_zero N hq
  have h5 : (qParam ^ N) ^ (c - 1) =
      (qParam ^ N) ^ (c - 1 - j) * ∏ _s ∈ Finset.Icc 1 j, qParam ^ N := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, ← pow_add, Nat.sub_add_cancel hj]
  simp only [pairQRhsNumPoly, eval_mul, eval_pow, eval_X, eval_prod, eval_sub, eval_one, eval_C]
  rw [h5, cyclotomicKernel, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun s _ ↦ ?_
  rw [zpow_add₀ hq, zpow_sub₀ hq, zpow_natCast]
  field_simp

/-- The common denominator of the transfer kernel splits into a factor independent of `J` and
the factor `∏_{r<d} (q^r - x J)`. -/
private theorem famBasisPoly_zero_evalEval_eq_prod_mul_prod_pairQ (m : ℕ) (x y : RatFunc ℚ) :
    (famBasisPoly m qParam 0).evalEval x y =
      (∏ r ∈ Finset.range (2 * m + 3), (x - qParam ^ (r + 1))) *
        ∏ r ∈ Finset.range (2 * m + 3), (qParam ^ r - x * y) := by
  simp only [famBasisPoly, Finset.range_zero, Finset.prod_empty, one_mul, evalEval_prod,
    evalEval_mul, evalEval_sub, evalEval_C, evalEval_X, eval_sub, eval_C, eval_X]
  rw [Finset.range_eq_Ico, ← Finset.prod_mul_distrib]

/-- The cleared right-hand side at `x = q^N`, `N ≥ 2m + 4`, is a nonzero multiple of
`∑_{j<c} G_j(N) e_j`. -/
private theorem eval_pairQRhsPoly_eq_mul_sum (m c : ℕ) (e : ℕ → RatFunc ℚ) {N : ℤ}
    (hN : 2 * (m : ℤ) + 4 ≤ N) :
    (pairQRhsPoly m c e).eval (qParam ^ N) =
      (qParam ^ N) ^ (c - 1) *
        (∏ r ∈ Finset.range (2 * m + 3), (qParam ^ N - qParam ^ (r + 1))) *
        (∏ i ∈ Finset.range c, (pairQRhsDenomPoly m i).eval (qParam ^ N)) *
        ∑ j ∈ Finset.range c, famKernel m j N * e j := by
  rw [pairQRhsPoly, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj5 : j ≤ c - 1 := by have := Finset.mem_range.mp hj; omega
  have hΔ := famBasisPoly_zero_evalEval_ne_zero m hN j
  rw [famBasisPoly_zero_evalEval_eq_prod_mul_prod_pairQ, ← eval_pairQRhsDenomPoly] at hΔ
  obtain ⟨hA, hD⟩ := mul_ne_zero_iff.mp hΔ
  rw [eval_mul, eval_mul, eval_C, eval_prod, eval_pairQRhsNumPoly hj5, famKernel,
    famBasisPoly_zero_evalEval_eq_prod_mul_prod_pairQ, ← eval_pairQRhsDenomPoly,
    ← Finset.mul_prod_erase _ _ hj]
  field_simp

/-- At `x = q^(2m+2)` only the term `j = 0` of the cleared right-hand side survives, and it is
not zero. -/
private theorem eval_pairQRhsPoly_qParam_pow_ne_zero (m : ℕ) {c : ℕ} (hc : 1 ≤ c)
    {e : ℕ → RatFunc ℚ} (he : e 0 ≠ 0) :
    (pairQRhsPoly m c e).eval (qParam ^ (2 * m + 2)) ≠ 0 := by
  have hq := qParam_ne_zero
  have hpow : ∀ a b : ℕ, a ≠ b → qParam ^ a - qParam ^ b ≠ 0 := fun a b hab h ↦ by
    rw [← zpow_natCast, ← zpow_natCast] at h
    exact hab (Nat.cast_injective (qParam_zpow_injective (sub_eq_zero.mp h)))
  have hD0 : (pairQRhsDenomPoly m 0).eval (qParam ^ (2 * m + 2)) = 0 := by
    rw [eval_pairQRhsDenomPoly]
    exact Finset.prod_eq_zero
      (Finset.mem_range.mpr (by omega : 2 * m + 2 < 2 * m + 3))
      (by rw [pow_zero, mul_one, sub_self])
  rw [pairQRhsPoly, eval_finsetSum, Finset.sum_eq_single 0]
  · rw [eval_mul, eval_mul, eval_C, eval_prod]
    refine mul_ne_zero (mul_ne_zero he ?_) (Finset.prod_ne_zero_iff.mpr fun i hi ↦ ?_)
    · simp only [pairQRhsNumPoly, Nat.sub_zero, Finset.Icc_eq_empty (by norm_num : ¬ 1 ≤ 0),
        Finset.prod_empty, mul_one, eval_pow, eval_X]
      exact pow_ne_zero _ (pow_ne_zero _ hq)
    · rw [eval_pairQRhsDenomPoly, Finset.prod_ne_zero_iff]
      intro r hr
      have hr' : r < 2 * m + 3 := Finset.mem_range.mp hr
      have hi' : i ≠ 0 := Finset.ne_of_mem_erase hi
      rw [← pow_add]
      exact hpow r (2 * m + 2 + i) (by omega)
  · intro j _ hj0
    rw [eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.mpr
      ⟨Ne.symm hj0, Finset.mem_range.mpr (by omega)⟩) hD0, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

set_option linter.unusedVariables false in
theorem pairQ_transferRhs_eventually_ne_zero (m : ℕ) (hm : 1 ≤ m) {c : ℕ} (hc : 1 ≤ c)
    {e : ℕ → RatFunc ℚ} (he : e 0 ≠ 0) :
    ∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n → pairQTransferRhs m c e n ≠ 0 := by
  have hne : pairQRhsPoly m c e ≠ 0 := fun h ↦
    eval_pairQRhsPoly_qParam_pow_ne_zero m hc he (by rw [h, eval_zero])
  have hfin : {N : ℤ | (pairQRhsPoly m c e).eval (qParam ^ N) = 0}.Finite :=
    ((Polynomial.finite_setOfPred_isRoot hne).preimage qParam_zpow_injective.injOn).subset
      fun N hN ↦ hN
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨max 1 B, fun n hn ↦ ?_⟩
  have hn1 : 1 ≤ n := (le_max_left 1 B).trans hn
  have hnB : B ≤ n := (le_max_right 1 B).trans hn
  have hev : (pairQRhsPoly m c e).eval (qParam ^ (n + (2 * m + 3))) ≠ 0 := fun h ↦ by
    have hle : n + (2 * m + 3) ≤ B := hB h
    omega
  rw [eval_pairQRhsPoly_eq_mul_sum m c e (by omega)] at hev
  rw [pairQTransferRhs]
  exact mul_ne_zero (mul_ne_zero (famDet_eval_ne_zero m (by omega))
    (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ qParam_ne_zero)
      (zpow_ne_zero _ qParam_ne_zero)))) (right_ne_zero_of_mul hev)

end AJConjecture
