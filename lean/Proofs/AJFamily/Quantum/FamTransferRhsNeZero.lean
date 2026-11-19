import Mathlib
import AJFamily.Quantum.FamDetNeZero
import AJFamily.Quantum.FamTransferOpApply
import AJFamily.Quantum.TorusCycloDefectZero

/-!
# The family recurrence is inhomogeneous

`exists_forall_ge_opApplyField_famTransferOp_ne_zero`: `famTransferOp (2a)` applied to
`torusReducedFormulaEven a` is nonzero at all large colours.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The polynomial `∏_{r<d} (q^r - x q^j)`, `d = 4a + 3`: the factor depending on `j` of the
common denominator of the family transfer. -/
private noncomputable def famRhsDenomPoly (a j : ℕ) : (RatFunc ℚ)[X] :=
  ∏ r ∈ Finset.range (2 * (2 * a) + 3), (C (qParam ^ r) - X * C (qParam ^ j))

/-- The polynomial `x^(a+2-j) ∏_{s=1}^{j} (1 - q^s x) (x - q^s)`, whose value at `x = q^N` is
`x^(a+2) C_j(N)`. -/
private noncomputable def famRhsNumPoly (a j : ℕ) : (RatFunc ℚ)[X] :=
  X ^ (a + 2 - j) * ∏ s ∈ Finset.Icc 1 j, ((1 - C (qParam ^ s) * X) * (X - C (qParam ^ s)))

/-- The right-hand side of the family recurrence with denominators cleared, as a polynomial in
`x = q^N`. -/
private noncomputable def famRhsPoly (a : ℕ) : (RatFunc ℚ)[X] :=
  ∑ j ∈ Finset.range (a + 3), C (torusCycloDefect a j) * famRhsNumPoly a j *
    ∏ i ∈ (Finset.range (a + 3)).erase j, famRhsDenomPoly a i

/-- The value of the `j`-dependent factor of the common denominator. -/
private theorem eval_famRhsDenomPoly (a j : ℕ) (x : RatFunc ℚ) :
    (famRhsDenomPoly a j).eval x =
      ∏ r ∈ Finset.range (2 * (2 * a) + 3), (qParam ^ r - x * qParam ^ j) := by
  simp only [famRhsDenomPoly, eval_prod, eval_sub, eval_mul, eval_C, eval_X]

/-- The value at `x = q^N` of the numerator polynomial is `x^(a+2) C_j(N)`. -/
private theorem eval_famRhsNumPoly {a j : ℕ} (hj : j ≤ a + 2) (N : ℤ) :
    (famRhsNumPoly a j).eval (qParam ^ N) = (qParam ^ N) ^ (a + 2) * cyclotomicKernel j N := by
  have hq := qParam_ne_zero
  have hx : qParam ^ N ≠ 0 := zpow_ne_zero N hq
  have h5 : (qParam ^ N) ^ (a + 2) =
      (qParam ^ N) ^ (a + 2 - j) * ∏ _s ∈ Finset.Icc 1 j, qParam ^ N := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, ← pow_add, Nat.sub_add_cancel hj]
  simp only [famRhsNumPoly, eval_mul, eval_pow, eval_X, eval_prod, eval_sub, eval_one, eval_C]
  rw [h5, cyclotomicKernel, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun s _ ↦ ?_
  rw [zpow_add₀ hq, zpow_sub₀ hq, zpow_natCast]
  field_simp

/-- The common denominator of the family transfer splits into a factor independent of `J` and
the factor `∏_{r<d} (q^r - x J)`. -/
private theorem famBasisPoly_zero_evalEval_eq_prod_mul_prod (a : ℕ) (x y : RatFunc ℚ) :
    (famBasisPoly (2 * a) qParam 0).evalEval x y =
      (∏ r ∈ Finset.range (2 * (2 * a) + 3), (x - qParam ^ (r + 1))) *
        ∏ r ∈ Finset.range (2 * (2 * a) + 3), (qParam ^ r - x * y) := by
  simp only [famBasisPoly, Finset.range_zero, Finset.prod_empty, one_mul, evalEval_prod,
    evalEval_mul, evalEval_sub, evalEval_C, evalEval_X, eval_sub, eval_C, eval_X]
  rw [Finset.range_eq_Ico, ← Finset.prod_mul_distrib]

/-- The cleared right-hand side at `x = q^N`, `N ≥ 4a + 4`, is a nonzero multiple of
`∑_{j<a+3} G_j(N) e_j`. -/
private theorem eval_famRhsPoly_eq_mul_sum (a : ℕ) {N : ℤ}
    (hN : 2 * ((2 * a : ℕ) : ℤ) + 4 ≤ N) :
    (famRhsPoly a).eval (qParam ^ N) =
      (qParam ^ N) ^ (a + 2) *
        (∏ r ∈ Finset.range (2 * (2 * a) + 3), (qParam ^ N - qParam ^ (r + 1))) *
        (∏ i ∈ Finset.range (a + 3), (famRhsDenomPoly a i).eval (qParam ^ N)) *
        ∑ j ∈ Finset.range (a + 3), famKernel (2 * a) j N * torusCycloDefect a j := by
  rw [famRhsPoly, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj5 : j ≤ a + 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hΔ := famBasisPoly_zero_evalEval_ne_zero (2 * a) hN j
  rw [famBasisPoly_zero_evalEval_eq_prod_mul_prod, ← eval_famRhsDenomPoly] at hΔ
  obtain ⟨hA, hD⟩ := mul_ne_zero_iff.mp hΔ
  rw [eval_mul, eval_mul, eval_C, eval_prod, eval_famRhsNumPoly hj5, famKernel,
    famBasisPoly_zero_evalEval_eq_prod_mul_prod, ← eval_famRhsDenomPoly,
    ← Finset.mul_prod_erase _ _ hj]
  field_simp

/-- At `x = q^(4a+2)` only the term `j = 0` of the cleared right-hand side survives, and it is
not zero. -/
private theorem eval_famRhsPoly_qParam_pow_ne_zero (a : ℕ) (ha : 1 ≤ a) :
    (famRhsPoly a).eval (qParam ^ (2 * (2 * a) + 2)) ≠ 0 := by
  have hq := qParam_ne_zero
  have hpow : ∀ a b : ℕ, a ≠ b → qParam ^ a - qParam ^ b ≠ 0 := fun a b hab h ↦ by
    rw [← zpow_natCast, ← zpow_natCast] at h
    exact hab (Nat.cast_injective (qParam_zpow_injective (sub_eq_zero.mp h)))
  have hD0 : (famRhsDenomPoly a 0).eval (qParam ^ (2 * (2 * a) + 2)) = 0 := by
    rw [eval_famRhsDenomPoly]
    exact Finset.prod_eq_zero
      (Finset.mem_range.mpr (by omega : 2 * (2 * a) + 2 < 2 * (2 * a) + 3))
      (by rw [pow_zero, mul_one, sub_self])
  rw [famRhsPoly, eval_finsetSum, Finset.sum_eq_single 0]
  · rw [eval_mul, eval_mul, eval_C, eval_prod, torusCycloDefect_zero a ha]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_)
      (Finset.prod_ne_zero_iff.mpr fun i hi ↦ ?_)
    · have h := hpow 0 1 (by norm_num)
      rwa [pow_zero, pow_one] at h
    · simp only [famRhsNumPoly, Nat.sub_zero, Finset.Icc_eq_empty (by norm_num : ¬ 1 ≤ 0),
        Finset.prod_empty, mul_one, eval_pow, eval_X]
      exact pow_ne_zero _ (pow_ne_zero _ hq)
    · rw [eval_famRhsDenomPoly, Finset.prod_ne_zero_iff]
      intro r hr
      have hr' : r < 2 * (2 * a) + 3 := Finset.mem_range.mp hr
      have hi' : i ≠ 0 := Finset.ne_of_mem_erase hi
      rw [← pow_add]
      exact hpow r (2 * (2 * a) + 2 + i) (by omega)
  · intro j _ hj0
    rw [eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.mpr
      ⟨Ne.symm hj0, Finset.mem_range.mpr (by omega)⟩) hD0, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The family transfer operator does not annihilate the reduced formula of `T(2, 2a+1)` at
large colours: the right-hand side of the inhomogeneous recurrence is not zero. -/
theorem exists_forall_ge_opApplyField_famTransferOp_ne_zero (a : ℕ) (ha : 1 ≤ a) :
    ∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n →
      opApplyField (famTransferOp (2 * a)) (torusReducedFormulaEven a) n ≠ 0 := by
  have hne : famRhsPoly a ≠ 0 := fun h ↦
    eval_famRhsPoly_qParam_pow_ne_zero a ha (by rw [h, eval_zero])
  have hfin : {N : ℤ | (famRhsPoly a).eval (qParam ^ N) = 0}.Finite :=
    ((Polynomial.finite_setOfPred_isRoot hne).preimage qParam_zpow_injective.injOn).subset
      fun N hN ↦ hN
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨max 1 B, fun n hn ↦ ?_⟩
  have hn1 : 1 ≤ n := (le_max_left 1 B).trans hn
  have hnB : B ≤ n := (le_max_right 1 B).trans hn
  have hev : (famRhsPoly a).eval (qParam ^ (n + (4 * a + 3))) ≠ 0 := fun h ↦ by
    have hle : n + (4 * a + 3) ≤ B := hB h
    omega
  rw [eval_famRhsPoly_eq_mul_sum a (by push_cast; omega)] at hev
  rw [opApplyField_famTransferOp a ha hn1]
  exact mul_ne_zero (mul_ne_zero (famDet_eval_ne_zero (2 * a) (by push_cast; omega))
    (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ qParam_ne_zero)
      (zpow_ne_zero _ qParam_ne_zero)))) (right_ne_zero_of_mul hev)

end AJConjecture
