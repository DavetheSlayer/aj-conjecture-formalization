import Mathlib
import AJFamily.Quantum.FamTransferOpApply

/-!
# The right-hand side is rational in `q^N`

`exists_coeff_mul_opApplyField_famTransferOp`: at colours `n ≥ 1`, `famTransferOp (2a)` applied
to `torusReducedFormulaEven a` is a quotient `β(n) / δ(n)` of values of two coefficients.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- Every element of `ℚ(t)` is a quotient of two elements of `ℤ[t]`. -/
private theorem exists_intPoly_mul_eq_of_ratFunc_fam (e : RatFunc ℚ) :
    ∃ a b : ℤ[X], Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X b ≠ 0 ∧
      Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X b * e =
        Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X a := by
  have hφ : Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X =
      (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp
    · simp [RatFunc.algebraMap_X]
  obtain ⟨c, hc, hnum⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) e.num
  obtain ⟨d, hd, hden⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) e.denom
  have hc0 : (c : RatFunc ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hc
  have hd0 : (d : RatFunc ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hd
  have hD : algebraMap ℚ[X] (RatFunc ℚ) e.denom ≠ 0 := RatFunc.algebraMap_ne_zero e.denom_ne_zero
  have hp : Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X
      (C d * IsLocalization.integerNormalization (nonZeroDivisors ℤ) e.num) =
        d * (c * algebraMap ℚ[X] (RatFunc ℚ) e.num) := by
    rw [hφ, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_mul, map_C,
      ← algebraMap_int_eq, hnum, zsmul_eq_mul, map_mul, map_mul, map_intCast]
    simp
  have hq : Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X
      (C c * IsLocalization.integerNormalization (nonZeroDivisors ℤ) e.denom) =
        c * (d * algebraMap ℚ[X] (RatFunc ℚ) e.denom) := by
    rw [hφ, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_mul, map_C,
      ← algebraMap_int_eq, hden, zsmul_eq_mul, map_mul, map_mul, map_intCast]
    simp
  refine ⟨C d * IsLocalization.integerNormalization (nonZeroDivisors ℤ) e.num,
    C c * IsLocalization.integerNormalization (nonZeroDivisors ℤ) e.denom, ?_, ?_⟩
  · rw [hq]
    exact mul_ne_zero hc0 (mul_ne_zero hd0 hD)
  · have hquot : ∀ x : RatFunc ℚ,
        x = algebraMap ℚ[X] (RatFunc ℚ) e.num / algebraMap ℚ[X] (RatFunc ℚ) e.denom →
          c * (d * algebraMap ℚ[X] (RatFunc ℚ) e.denom) * x =
            d * (c * algebraMap ℚ[X] (RatFunc ℚ) e.num) := by
      rintro x rfl
      field_simp
    rw [hq, hp]
    exact hquot e (RatFunc.num_div_denom e).symm

/-- The coefficient `x = t^(4(4a+3)) M²`, whose value at the colour `n` is `q^(n+4a+3)`. -/
private noncomputable def famVar (a : ℕ) : Coeff :=
  C (X ^ (4 * (4 * a + 3))) * X ^ 2

/-- The value of `t^(4(4a+3)) M²` at the colour `n` is `q^(n+4a+3)`. -/
private theorem evalAtField_famVar (a : ℕ) (n : ℤ) :
    evalAtField n (famVar a) = qParam ^ (n + (4 * a + 3)) := by
  rw [famVar, evalAtField, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
    map_pow, coe_eval₂RingHom, eval₂_X, qParam,
    ← zpow_natCast RatFunc.X 4, ← zpow_natCast RatFunc.X (4 * (4 * a + 3)), ← zpow_natCast _ 2,
    ← zpow_mul, ← zpow_mul, ← zpow_add₀ RatFunc.X_ne_zero]
  congr 1
  push_cast
  ring

/-- The value of the constant coefficient `t^(4k)` is `q^k`. -/
private theorem evalAtField_C_X_pow_four_mul_fam (n : ℤ) (k : ℕ) :
    evalAtField n (C (X ^ (4 * k)) : Coeff) = qParam ^ k := by
  rw [evalAtField, coe_eval₂RingHom, eval₂_C, map_pow, coe_eval₂RingHom, eval₂_X, qParam,
    pow_mul]

/-- The numerator `∏_{s=1}^{j} (1 - q^s x)(x - q^s)` of the cyclotomic kernel. -/
private noncomputable def famKernelNumCoeff (a j : ℕ) : Coeff :=
  ∏ s ∈ Finset.Icc 1 j,
    ((1 - C (X ^ (4 * s)) * famVar a) * (famVar a - C (X ^ (4 * s))))

/-- The cyclotomic kernel at `N = n + 4a + 3` is a quotient of values of coefficients. -/
private theorem cyclotomicKernel_eq_evalAtField_div_fam (a j : ℕ) (n : ℤ) :
    cyclotomicKernel j (n + (4 * a + 3)) =
      evalAtField n (famKernelNumCoeff a j) / evalAtField n (famVar a ^ j) := by
  have hx : qParam ^ (n + (4 * a + 3)) ≠ 0 := zpow_ne_zero _ qParam_ne_zero
  have hpow : (qParam ^ (n + (4 * a + 3))) ^ j =
      ∏ _s ∈ Finset.Icc 1 j, qParam ^ (n + (4 * a + 3)) := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [cyclotomicKernel, famKernelNumCoeff, map_prod, map_pow, evalAtField_famVar, hpow,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun s _ ↦ ?_
  rw [map_mul, map_sub, map_sub, map_mul, map_one, evalAtField_famVar,
    evalAtField_C_X_pow_four_mul_fam, zpow_add₀ qParam_ne_zero, zpow_sub₀ qParam_ne_zero,
    zpow_natCast]
  field_simp

/-- The common denominator `Δ(x, q^j)` as a coefficient. -/
private noncomputable def famDenomCoeff (a j : ℕ) : Coeff :=
  ∏ r ∈ Finset.Ico 0 (2 * (2 * a) + 3), ((famVar a - C (X ^ (4 * (r + 1)))) *
    (C (X ^ (4 * r)) - famVar a * C (X ^ (4 * j))))

/-- The value of the common denominator. -/
private theorem evalAtField_famDenomCoeff (a j : ℕ) (n : ℤ) :
    evalAtField n (famDenomCoeff a j) =
      (famBasisPoly (2 * a) qParam 0).evalEval (qParam ^ (n + (4 * a + 3))) (qParam ^ j) := by
  simp only [famBasisPoly, Finset.range_zero, Finset.prod_empty, one_mul, evalEval_prod,
    evalEval_mul, evalEval_sub, evalEval_C, evalEval_X, eval_C, eval_X,
    famDenomCoeff, map_prod, map_mul, map_sub, evalAtField_famVar,
    evalAtField_C_X_pow_four_mul_fam]

/-- The value at the colour `n` of the integral determinant is the determinant over `ℚ(t)` at
`x = q^(n+4a+3)`. -/
private theorem evalAtField_famDet_comp (a : ℕ) (n : ℤ) :
    evalAtField n ((famDet (2 * a) (X ^ 4 : ℤ[X])).comp (famVar a)) =
      (famDet (2 * a) qParam).eval (qParam ^ (n + (4 * a + 3))) := by
  have hφ : Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X (X ^ 4) = qParam := by
    rw [map_pow, coe_eval₂RingHom, eval₂_X, qParam]
  have hx := evalAtField_famVar a n
  rw [evalAtField, coe_eval₂RingHom] at hx
  rw [evalAtField, coe_eval₂RingHom, eval₂_comp, hx, eval₂_eq_eval_map, map_famDet, hφ]

/-- `g` is, at the colours `n ≥ 1`, a quotient of values of two coefficients, the denominator
not vanishing there. -/
private def IsFamTailQuotient (g : ℤ → RatFunc ℚ) : Prop :=
  ∃ β δ : Coeff, ∀ n : ℤ, 1 ≤ n →
    evalAtField n δ ≠ 0 ∧ evalAtField n δ * g n = evalAtField n β

/-- The values of a coefficient form a tail quotient. -/
private theorem isFamTailQuotient_evalAtField (c : Coeff) :
    IsFamTailQuotient fun n ↦ evalAtField n c :=
  ⟨c, 1, fun n _ ↦ ⟨by rw [map_one]; exact one_ne_zero, by rw [map_one, one_mul]⟩⟩

/-- A constant sequence is a tail quotient. -/
private theorem isFamTailQuotient_const (e : RatFunc ℚ) : IsFamTailQuotient fun _ ↦ e := by
  obtain ⟨a, b, hb, hab⟩ := exists_intPoly_mul_eq_of_ratFunc_fam e
  refine ⟨C a, C b, fun n _ ↦ ?_⟩
  have hC : ∀ p : ℤ[X], evalAtField n (C p) =
      Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X p := fun p ↦ by
    rw [evalAtField, coe_eval₂RingHom, eval₂_C]
  rw [hC, hC]
  exact ⟨hb, hab⟩

/-- Tail quotients are stable under products. -/
private theorem isFamTailQuotient_mul {g g' : ℤ → RatFunc ℚ} (hg : IsFamTailQuotient g)
    (hg' : IsFamTailQuotient g') : IsFamTailQuotient fun n ↦ g n * g' n := by
  obtain ⟨β, δ, h⟩ := hg
  obtain ⟨β', δ', h'⟩ := hg'
  refine ⟨β * β', δ * δ', fun n hn ↦ ⟨?_, ?_⟩⟩
  · rw [map_mul]
    exact mul_ne_zero (h n hn).1 (h' n hn).1
  · rw [map_mul, map_mul, ← (h n hn).2, ← (h' n hn).2]
    ring

/-- Tail quotients are stable under sums. -/
private theorem isFamTailQuotient_add {g g' : ℤ → RatFunc ℚ} (hg : IsFamTailQuotient g)
    (hg' : IsFamTailQuotient g') : IsFamTailQuotient fun n ↦ g n + g' n := by
  obtain ⟨β, δ, h⟩ := hg
  obtain ⟨β', δ', h'⟩ := hg'
  refine ⟨β * δ' + β' * δ, δ * δ', fun n hn ↦ ⟨?_, ?_⟩⟩
  · rw [map_mul]
    exact mul_ne_zero (h n hn).1 (h' n hn).1
  · rw [map_add, map_mul, map_mul, map_mul, ← (h n hn).2, ← (h' n hn).2]
    ring

/-- Tail quotients are stable under division by a coefficient that does not vanish at the
colours `n ≥ 1`. -/
private theorem isFamTailQuotient_div_evalAtField {g : ℤ → RatFunc ℚ} (hg : IsFamTailQuotient g)
    {c : Coeff} (hc : ∀ n : ℤ, 1 ≤ n → evalAtField n c ≠ 0) :
    IsFamTailQuotient fun n ↦ g n / evalAtField n c := by
  obtain ⟨β, δ, h⟩ := hg
  refine ⟨β, δ * c, fun n hn ↦ ⟨?_, ?_⟩⟩
  · rw [map_mul]
    exact mul_ne_zero (h n hn).1 (hc n hn)
  · rw [map_mul, ← (h n hn).2]
    have := hc n hn
    field_simp

/-- Tail quotients are stable under finite sums. -/
private theorem isFamTailQuotient_sum_range (N : ℕ) (g : ℕ → ℤ → RatFunc ℚ)
    (h : ∀ j, IsFamTailQuotient (g j)) :
    IsFamTailQuotient fun n ↦ ∑ j ∈ Finset.range N, g j n := by
  induction N with
  | zero =>
    exact ⟨0, 1, fun n _ ↦ ⟨by rw [map_one]; exact one_ne_zero, by simp⟩⟩
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    exact isFamTailQuotient_add ih (h N)

/-- The right-hand side of the family transfer recurrence is a quotient of two coefficients. -/
theorem exists_coeff_mul_opApplyField_famTransferOp (a : ℕ) (ha : 1 ≤ a) :
    ∃ β δ : Coeff, δ ≠ 0 ∧ ∀ n : ℤ, 1 ≤ n →
      evalAtField n δ * opApplyField (famTransferOp (2 * a)) (torusReducedFormulaEven a) n =
        evalAtField n β := by
  have hx : ∀ n : ℤ, 1 ≤ n → evalAtField n (famVar a) ≠ 0 := fun n _ ↦ by
    rw [evalAtField_famVar]
    exact zpow_ne_zero _ qParam_ne_zero
  have hsum := isFamTailQuotient_sum_range (a + 3)
    (fun j n ↦ evalAtField n (famKernelNumCoeff a j) / evalAtField n (famVar a ^ j) /
      evalAtField n (famDenomCoeff a j) * torusCycloDefect a j)
    fun j ↦ isFamTailQuotient_mul
      (isFamTailQuotient_div_evalAtField
        (isFamTailQuotient_div_evalAtField (isFamTailQuotient_evalAtField (famKernelNumCoeff a j))
          (c := famVar a ^ j) fun n hn ↦ by
            rw [map_pow]
            exact pow_ne_zero _ (hx n hn))
        (c := famDenomCoeff a j) fun n hn ↦ by
          rw [evalAtField_famDenomCoeff]
          exact famBasisPoly_zero_evalEval_ne_zero (2 * a) (by push_cast; omega) j)
      (isFamTailQuotient_const (torusCycloDefect a j))
  obtain ⟨β, δ, h⟩ := isFamTailQuotient_mul (isFamTailQuotient_mul
    (isFamTailQuotient_evalAtField ((famDet (2 * a) (X ^ 4 : ℤ[X])).comp (famVar a)))
    (isFamTailQuotient_evalAtField ((C (X ^ (4 * (4 * a + 3))) * famVar a) ^ (2 * a + 1))))
    hsum
  refine ⟨β, δ, fun h0 ↦ (h 1 le_rfl).1 (by rw [h0, map_zero]), fun n hn ↦ ?_⟩
  have h7 : evalAtField n ((C (X ^ (4 * (4 * a + 3))) * famVar a) ^ (2 * a + 1)) =
      (qParam ^ (4 * a + 3) * qParam ^ (n + (4 * a + 3))) ^ (2 * a + 1) := by
    rw [map_pow, map_mul, evalAtField_C_X_pow_four_mul_fam, evalAtField_famVar]
  rw [← (h n hn).2, opApplyField_famTransferOp a ha hn]
  simp only [evalAtField_famDet_comp, h7, famKernel,
    cyclotomicKernel_eq_evalAtField_div_fam, evalAtField_famDenomCoeff]

end AJConjecture
