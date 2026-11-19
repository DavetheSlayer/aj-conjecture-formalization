import Mathlib
import AJFamily.Quantum.TorusFormula
import AJFamily.Quantum.TorusFormulaEven
import AJConjecture.QAlgQParamBasic
import AJHandoff.LocalTheory.LocTailExtension

/-!
# The family's closed formula is a cyclotomic expansion

The unreduced formula `torusWhiteheadFormula a n = [n] F_n`, `F_N = ∑_{j < N} C_j(N) D_j`, extended
oddly, is `[n] ∑_{j < |n|} C_j(n) D_j` at every integer `n` (`[-n] = -[n]`,
`C_j(-n) = C_j(n)`, `[0] = 0`). The pole of `D_j = torusCyclotomicCoeff a j` at `q = 1` has order
at most `j`: in
`q^j (1 - q)(q; q)_j ∑_n (-1)^n q^(n(n+1)/2) u_n / ((q; q)_(j-n) (q; q)_(j+n+1))`
the numerator has `j + 1` factors `1 - q^s` and each denominator `2j + 1`; every `1 - q^s` is
`(1 - q)` times a polynomial with value `s ≠ 0` at `t = 1`, and the odd colours `u_n`
(`torusOddColor`) are Laurent polynomials in `t`. So `(1 - q)^j D_j` is regular at `t = 1`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The subring of rational functions regular at `t = 1`. -/
private def regularAtOneSubring : Subring (RatFunc ℚ) where
  carrier := {f | IsRegularAtOne f}
  mul_mem' := IsRegularAtOne.mul
  one_mem' := by simpa using (isRegularAtOne_basic 1).1
  add_mem' := IsRegularAtOne.add
  zero_mem' := by simpa using (isRegularAtOne_basic 0).1
  neg_mem' := fun {f} hf ↦ by simpa using ((isRegularAtOne_basic (-1)).1).mul hf

/-- Integer powers of `t` are regular at `t = 1`. -/
private theorem X_zpow_mem_regularAtOneSubring (k : ℤ) :
    (RatFunc.X : RatFunc ℚ) ^ k ∈ regularAtOneSubring := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast, ← RatFunc.algebraMap_X, ← map_pow]
    exact (isRegularAtOne_basic _).1
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact Subring.pow_mem _ (isRegularAtOne_basic 0).2.1 m

/-- Integer powers of `q` are regular at `t = 1`. -/
private theorem qParam_zpow_mem_regularAtOneSubring (k : ℤ) :
    qParam ^ k ∈ regularAtOneSubring := by
  rw [qParam_zpow_eq_ratFuncX_zpow]
  exact X_zpow_mem_regularAtOneSubring _

/-- `q` is regular at `t = 1`. -/
private theorem qParam_mem_regularAtOneSubring : qParam ∈ regularAtOneSubring := by
  simpa using qParam_zpow_mem_regularAtOneSubring 1

/-- `[k] = t^(2 - 2k) (1 + q + ⋯ + q^(k-1))` for `k ∈ ℕ`. -/
private theorem quantumInt_natCast_eq_geom (k : ℕ) :
    quantumInt k = RatFunc.X ^ (2 - 2 * (k : ℤ)) * ∑ i ∈ Finset.range k, qParam ^ i := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have e1 : (RatFunc.X : RatFunc ℚ) ^ (2 * (k : ℤ)) = RatFunc.X ^ (2 * k) := by
    rw [← zpow_natCast]
    push_cast
    rfl
  have e3 : (RatFunc.X : RatFunc ℚ) ^ (2 - 2 * (k : ℤ)) =
      RatFunc.X ^ 2 * (RatFunc.X ^ (2 * k))⁻¹ := by
    rw [zpow_sub₀ hX, e1, div_eq_mul_inv]
    rfl
  have e4 : (RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ) = (RatFunc.X ^ 2)⁻¹ := by
    rw [zpow_neg]
    rfl
  have hq1 : (1 - qParam : RatFunc ℚ) ≠ 0 := by
    simpa using one_sub_qParam_zpow_ne_zero (n := 1) one_ne_zero
  have hden : (RatFunc.X : RatFunc ℚ) ^ 2 - (RatFunc.X ^ 2)⁻¹ ≠ 0 := by
    intro h
    apply hq1
    rw [qParam]
    field_simp at h
    linear_combination -h
  have hg := mul_neg_geom_sum qParam k
  have e2 : (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) = RatFunc.X ^ 2 := by
    rw [← zpow_natCast]
    rfl
  rw [quantumInt, e1, zpow_neg, e1, e3, e4, e2, div_eq_iff hden]
  simp only [qParam] at hg ⊢
  field_simp
  linear_combination hg

/-- Quantum integers are Laurent polynomials, hence regular at `t = 1`. -/
private theorem quantumInt_mem_regularAtOneSubring (m : ℤ) :
    quantumInt m ∈ regularAtOneSubring := by
  have hnat : ∀ k : ℕ, quantumInt k ∈ regularAtOneSubring := fun k ↦ by
    rw [quantumInt_natCast_eq_geom]
    exact Subring.mul_mem _ (X_zpow_mem_regularAtOneSubring _)
      (Subring.sum_mem _ fun i _ ↦ Subring.pow_mem _ qParam_mem_regularAtOneSubring i)
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · exact hnat k
  · have hneg : quantumInt (-(k : ℤ)) = -quantumInt k := by
      simp only [quantumInt, mul_neg, neg_neg]
      ring
    rw [hneg]
    exact Subring.neg_mem _ (hnat k)

/-- The odd colours are regular at `t = 1`. -/
private theorem torusOddColor_mem_regularAtOneSubring (a n : ℕ) :
    torusOddColor a n ∈ regularAtOneSubring :=
  Subring.mul_mem _ (qParam_zpow_mem_regularAtOneSubring _) <| Subring.sum_mem _ fun _ _ ↦
    Subring.mul_mem _ (qParam_zpow_mem_regularAtOneSubring _) (quantumInt_mem_regularAtOneSubring _)

/-- The product `∏_{s<k} (1 + q + ⋯ + q^s)`, so that `(q; q)_k = (1 - q)^k` times it. -/
private def qIntProd (k : ℕ) : RatFunc ℚ :=
  ∏ s ∈ Finset.range k, ∑ i ∈ Finset.range (s + 1), qParam ^ i

/-- `(q; q)_k = (1 - q)^k ∏_{s<k} (1 + q + ⋯ + q^s)`. -/
private theorem qPochhammer_qParam_eq_mul_qIntProd (k : ℕ) :
    qPochhammer qParam k = (1 - qParam) ^ k * qIntProd k := by
  rw [qPochhammer, qIntProd, Finset.prod_congr rfl fun s _ ↦ show 1 - qParam * qParam ^ s =
      (1 - qParam) * ∑ i ∈ Finset.range (s + 1), qParam ^ i by
    rw [mul_neg_geom_sum, pow_succ']]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-- `∏_{s<k} (1 + q + ⋯ + q^s)` and its inverse are regular at `t = 1`. -/
private theorem qIntProd_mem_regularAtOneSubring (k : ℕ) :
    qIntProd k ∈ regularAtOneSubring ∧ (qIntProd k)⁻¹ ∈ regularAtOneSubring := by
  have hpoly : qIntProd k = algebraMap ℚ[X] (RatFunc ℚ)
      (∏ s ∈ Finset.range k, ∑ i ∈ Finset.range (s + 1), (X ^ 4) ^ i) := by
    simp [qIntProd, map_prod, map_sum, map_pow, RatFunc.algebraMap_X, qParam]
  have heval : (∏ s ∈ Finset.range k, ∑ i ∈ Finset.range (s + 1), (X ^ 4 : ℚ[X]) ^ i).eval 1 ≠
      0 := by
    simp only [eval_prod, eval_finsetSum, eval_pow, eval_X, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    exact Finset.prod_ne_zero_iff.mpr fun s _ ↦ Nat.cast_ne_zero.mpr (Nat.succ_ne_zero s)
  rw [hpoly]
  exact ⟨(isRegularAtOne_basic _).1, (isRegularAtOne_basic _).2.2 heval⟩

theorem isRegularAtOne_torusCyclotomicCoeff (a j : ℕ) :
    IsRegularAtOne ((1 - qParam) ^ j * torusCyclotomicCoeff a j) := by
  have hE : (1 - qParam : RatFunc ℚ) ≠ 0 := by
    simpa using one_sub_qParam_zpow_ne_zero (n := 1) one_ne_zero
  have hP : ∀ k, qIntProd k ≠ 0 := fun k h ↦ qPochhammer_qParam_ne_zero k <| by
    rw [qPochhammer_qParam_eq_mul_qIntProd, h, mul_zero]
  change _ ∈ regularAtOneSubring
  rw [torusCyclotomicCoeff, Finset.mul_sum, Finset.mul_sum]
  refine Subring.sum_mem _ fun n hn ↦ ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  have hmem : qParam ^ (n + k) * ((-1) ^ n * qParam ^ (n * (n + 1) / 2) * torusOddColor a n) *
      qIntProd (n + k) * (qIntProd k)⁻¹ * (qIntProd (n + k + n + 1))⁻¹ ∈ regularAtOneSubring := by
    refine Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _
      (Subring.pow_mem _ qParam_mem_regularAtOneSubring _) (Subring.mul_mem _ (Subring.mul_mem _
        (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
        (Subring.pow_mem _ qParam_mem_regularAtOneSubring _))
      (torusOddColor_mem_regularAtOneSubring a n))) (qIntProd_mem_regularAtOneSubring _).1)
      (qIntProd_mem_regularAtOneSubring _).2) (qIntProd_mem_regularAtOneSubring _).2
  convert hmem using 1
  rw [qPochhammer_qParam_eq_mul_qIntProd, qPochhammer_qParam_eq_mul_qIntProd,
    qPochhammer_qParam_eq_mul_qIntProd, Nat.add_sub_cancel_left]
  have h1 := hP (n + k)
  have h2 := hP k
  have h3 := hP (n + k + n + 1)
  field_simp
  ring

/-- `C_j(-N) = C_j(N)`. -/
private theorem cyclotomicKernel_neg_eq (j : ℕ) (N : ℤ) :
    cyclotomicKernel j (-N) = cyclotomicKernel j N := by
  refine Finset.prod_congr rfl fun s _ ↦ ?_
  rw [sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

theorem hasCyclotomicExpansion_torusWhiteheadFormula (a : ℕ) :
    HasCyclotomicExpansion (torusWhiteheadFormula a) (torusCyclotomicCoeff a) := by
  refine ⟨fun n ↦ ?_, isRegularAtOne_torusCyclotomicCoeff a⟩
  rw [torusWhiteheadFormula_eq_quantumInt_mul, torusReducedFormulaEven, torusReducedFormula]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rcases le_or_gt 0 n with hn | hn
  · rw [show ((n.natAbs : ℕ) : ℤ) = n by omega]
  · rw [show ((n.natAbs : ℕ) : ℤ) = -n by omega, cyclotomicKernel_neg_eq]

end AJConjecture
