import Mathlib
import AJConjecture.QAlgOpApplyFieldBasic
import AJFamily.Quantum.FamTransferMap
import AJFamily.Quantum.FamTransferOp
import AJHandoff.TorusQuantum.PairQFormula

/-!
# The right-hand side of the transfer identity is rational in `t` and `M`

For every `m ≥ 1`, cut-off `c` and constants `e_0, …, e_(c-1) ∈ ℚ(t)` there are
`β, δ ∈ ℤ[t][M]`, `δ ≠ 0`, with `ev_n(δ) · pairQTransferRhs m c e n = ev_n(β)` for every `n ≥ 1`.
This is `exists_coeff_mul_opApplyField_famTransferOp` with the defects of `T(2, a)` replaced by
arbitrary constants; its proof (closure of tail quotients under sums and products, the kernel
`G_j(N)` as a quotient of polynomials in `ξ = t^(4d) M²` nonvanishing for `n ≥ 1`, constants of
`ℚ(t)` as quotients of elements of `ℤ[t]`) never uses the values of the defects.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Every element of `ℚ(t)` is a quotient of two elements of `ℤ[t]`. -/
private theorem exists_intPoly_mul_eq_of_ratFunc_pairQ (e : RatFunc ℚ) :
    ∃ a b : ℤ[X],
      Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X b ≠ 0 ∧
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
  have hD : algebraMap ℚ[X] (RatFunc ℚ) e.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero e.denom_ne_zero
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

/-- The coefficient `x = t^(4(2m+3)) M²`, whose value at the colour `n` is `q^(n+2m+3)`. -/
private noncomputable def pairQVar (m : ℕ) : Coeff :=
  C (X ^ (4 * (2 * m + 3))) * X ^ 2

/-- The value of `t^(4(2m+3)) M²` at the colour `n` is `q^(n+2m+3)`. -/
private theorem evalAtField_pairQVar (m : ℕ) (n : ℤ) :
    evalAtField n (pairQVar m) = qParam ^ (n + (2 * m + 3)) := by
  rw [pairQVar, evalAtField, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
    map_pow, coe_eval₂RingHom, eval₂_X, qParam,
    ← zpow_natCast RatFunc.X 4, ← zpow_natCast RatFunc.X (4 * (2 * m + 3)),
    ← zpow_natCast _ 2,
    ← zpow_mul, ← zpow_mul, ← zpow_add₀ RatFunc.X_ne_zero]
  congr 1
  push_cast
  ring

/-- The value of the constant coefficient `t^(4k)` is `q^k`. -/
private theorem evalAtField_C_X_pow_four_mul_pairQ (n : ℤ) (k : ℕ) :
    evalAtField n (C (X ^ (4 * k)) : Coeff) = qParam ^ k := by
  rw [evalAtField, coe_eval₂RingHom, eval₂_C, map_pow, coe_eval₂RingHom, eval₂_X, qParam,
    pow_mul]

/-- The numerator `∏_{s=1}^{j} (1 - q^s x)(x - q^s)` of the cyclotomic kernel. -/
private noncomputable def pairQKernelNumCoeff (m j : ℕ) : Coeff :=
  ∏ s ∈ Finset.Icc 1 j,
    ((1 - C (X ^ (4 * s)) * pairQVar m) * (pairQVar m - C (X ^ (4 * s))))

/-- The cyclotomic kernel at `N = n + 2m + 3` is a quotient of values of coefficients. -/
private theorem cyclotomicKernel_eq_evalAtField_div_pairQ (m j : ℕ) (n : ℤ) :
    cyclotomicKernel j (n + (2 * m + 3)) =
      evalAtField n (pairQKernelNumCoeff m j) / evalAtField n (pairQVar m ^ j) := by
  have hx : qParam ^ (n + (2 * m + 3)) ≠ 0 := zpow_ne_zero _ qParam_ne_zero
  have hpow : (qParam ^ (n + (2 * m + 3))) ^ j =
      ∏ _s ∈ Finset.Icc 1 j, qParam ^ (n + (2 * m + 3)) := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [cyclotomicKernel, pairQKernelNumCoeff, map_prod, map_pow, evalAtField_pairQVar, hpow,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun s _ ↦ ?_
  rw [map_mul, map_sub, map_sub, map_mul, map_one, evalAtField_pairQVar,
    evalAtField_C_X_pow_four_mul_pairQ, zpow_add₀ qParam_ne_zero, zpow_sub₀ qParam_ne_zero,
    zpow_natCast]
  field_simp

/-- The common denominator `Δ(x, q^j)` as a coefficient. -/
private noncomputable def pairQDenomCoeff (m j : ℕ) : Coeff :=
  ∏ r ∈ Finset.Ico 0 (2 * m + 3), ((pairQVar m - C (X ^ (4 * (r + 1)))) *
    (C (X ^ (4 * r)) - pairQVar m * C (X ^ (4 * j))))

/-- The value of the common denominator. -/
private theorem evalAtField_pairQDenomCoeff (m j : ℕ) (n : ℤ) :
    evalAtField n (pairQDenomCoeff m j) =
      (famBasisPoly m qParam 0).evalEval (qParam ^ (n + (2 * m + 3))) (qParam ^ j) := by
  simp only [famBasisPoly, Finset.range_zero, Finset.prod_empty, one_mul, evalEval_prod,
    evalEval_mul, evalEval_sub, evalEval_C, evalEval_X, eval_C, eval_X,
    pairQDenomCoeff, map_prod, map_mul, map_sub, evalAtField_pairQVar,
    evalAtField_C_X_pow_four_mul_pairQ]

/-- The value at the colour `n` of the integral determinant is the determinant over `ℚ(t)` at
`x = q^(n+2m+3)`. -/
private theorem evalAtField_famDet_comp_pairQ (m : ℕ) (n : ℤ) :
    evalAtField n ((famDet m (X ^ 4 : ℤ[X])).comp (pairQVar m)) =
      (famDet m qParam).eval (qParam ^ (n + (2 * m + 3))) := by
  have hφ : Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X (X ^ 4) =
      qParam := by
    rw [map_pow, coe_eval₂RingHom, eval₂_X, qParam]
  have hx := evalAtField_pairQVar m n
  rw [evalAtField, coe_eval₂RingHom] at hx
  rw [evalAtField, coe_eval₂RingHom, eval₂_comp, hx, eval₂_eq_eval_map, map_famDet, hφ]

/-- `g` is, at the colours `n ≥ 1`, a quotient of values of two coefficients, the denominator
not vanishing there. -/
private def IsPairQTailQuotient (g : ℤ → RatFunc ℚ) : Prop :=
  ∃ β δ : Coeff, ∀ n : ℤ, 1 ≤ n →
    evalAtField n δ ≠ 0 ∧ evalAtField n δ * g n = evalAtField n β

/-- The values of a coefficient form a tail quotient. -/
private theorem isPairQTailQuotient_evalAtField (c : Coeff) :
    IsPairQTailQuotient fun n ↦ evalAtField n c :=
  ⟨c, 1, fun n _ ↦ ⟨by rw [map_one]; exact one_ne_zero, by rw [map_one, one_mul]⟩⟩

/-- A constant sequence is a tail quotient. -/
private theorem isPairQTailQuotient_const (e : RatFunc ℚ) : IsPairQTailQuotient fun _ ↦ e := by
  obtain ⟨a, b, hb, hab⟩ := exists_intPoly_mul_eq_of_ratFunc_pairQ e
  refine ⟨C a, C b, fun n _ ↦ ?_⟩
  have hC : ∀ p : ℤ[X], evalAtField n (C p) =
      Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X p := fun p ↦ by
    rw [evalAtField, coe_eval₂RingHom, eval₂_C]
  rw [hC, hC]
  exact ⟨hb, hab⟩

/-- Tail quotients are stable under products. -/
private theorem isPairQTailQuotient_mul {g g' : ℤ → RatFunc ℚ} (hg : IsPairQTailQuotient g)
    (hg' : IsPairQTailQuotient g') : IsPairQTailQuotient fun n ↦ g n * g' n := by
  obtain ⟨β, δ, h⟩ := hg
  obtain ⟨β', δ', h'⟩ := hg'
  refine ⟨β * β', δ * δ', fun n hn ↦ ⟨?_, ?_⟩⟩
  · rw [map_mul]
    exact mul_ne_zero (h n hn).1 (h' n hn).1
  · rw [map_mul, map_mul, ← (h n hn).2, ← (h' n hn).2]
    ring

/-- Tail quotients are stable under sums. -/
private theorem isPairQTailQuotient_add {g g' : ℤ → RatFunc ℚ} (hg : IsPairQTailQuotient g)
    (hg' : IsPairQTailQuotient g') : IsPairQTailQuotient fun n ↦ g n + g' n := by
  obtain ⟨β, δ, h⟩ := hg
  obtain ⟨β', δ', h'⟩ := hg'
  refine ⟨β * δ' + β' * δ, δ * δ', fun n hn ↦ ⟨?_, ?_⟩⟩
  · rw [map_mul]
    exact mul_ne_zero (h n hn).1 (h' n hn).1
  · rw [map_add, map_mul, map_mul, map_mul, ← (h n hn).2, ← (h' n hn).2]
    ring

/-- Tail quotients are stable under division by a coefficient that does not vanish at the
colours `n ≥ 1`. -/
private theorem isPairQTailQuotient_div_evalAtField {g : ℤ → RatFunc ℚ}
    (hg : IsPairQTailQuotient g)
    {c : Coeff} (hc : ∀ n : ℤ, 1 ≤ n → evalAtField n c ≠ 0) :
    IsPairQTailQuotient fun n ↦ g n / evalAtField n c := by
  obtain ⟨β, δ, h⟩ := hg
  refine ⟨β, δ * c, fun n hn ↦ ⟨?_, ?_⟩⟩
  · rw [map_mul]
    exact mul_ne_zero (h n hn).1 (hc n hn)
  · rw [map_mul, ← (h n hn).2]
    have := hc n hn
    field_simp

/-- Tail quotients are stable under finite sums. -/
private theorem isPairQTailQuotient_sum_range (N : ℕ) (g : ℕ → ℤ → RatFunc ℚ)
    (h : ∀ j, IsPairQTailQuotient (g j)) :
    IsPairQTailQuotient fun n ↦ ∑ j ∈ Finset.range N, g j n := by
  induction N with
  | zero =>
    exact ⟨0, 1, fun n _ ↦ ⟨by rw [map_one]; exact one_ne_zero, by simp⟩⟩
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    exact isPairQTailQuotient_add ih (h N)


set_option linter.unusedVariables false in
theorem pairQ_exists_coeff_mul_transferRhs (m : ℕ) (hm : 1 ≤ m) (c : ℕ)
    (e : ℕ → RatFunc ℚ) :
    ∃ β δ : Coeff, δ ≠ 0 ∧ ∀ n : ℤ, 1 ≤ n →
      evalAtField n δ * pairQTransferRhs m c e n = evalAtField n β := by
  have hx : ∀ n : ℤ, 1 ≤ n → evalAtField n (pairQVar m) ≠ 0 := fun n _ ↦ by
    rw [evalAtField_pairQVar]
    exact zpow_ne_zero _ qParam_ne_zero
  have hsum := isPairQTailQuotient_sum_range c
    (fun j n ↦ evalAtField n (pairQKernelNumCoeff m j) / evalAtField n (pairQVar m ^ j) /
      evalAtField n (pairQDenomCoeff m j) * e j)
    fun j ↦ isPairQTailQuotient_mul
      (isPairQTailQuotient_div_evalAtField
        (isPairQTailQuotient_div_evalAtField
          (isPairQTailQuotient_evalAtField (pairQKernelNumCoeff m j))
          (c := pairQVar m ^ j) fun n hn ↦ by
            rw [map_pow]
            exact pow_ne_zero _ (hx n hn))
        (c := pairQDenomCoeff m j) fun n hn ↦ by
          rw [evalAtField_pairQDenomCoeff]
          exact famBasisPoly_zero_evalEval_ne_zero m (by omega) j)
      (isPairQTailQuotient_const (e j))
  obtain ⟨β, δ, h⟩ := isPairQTailQuotient_mul (isPairQTailQuotient_mul
    (isPairQTailQuotient_evalAtField ((famDet m (X ^ 4 : ℤ[X])).comp (pairQVar m)))
    (isPairQTailQuotient_evalAtField ((C (X ^ (4 * (2 * m + 3))) * pairQVar m) ^ (m + 1))))
    hsum
  refine ⟨β, δ, fun h0 ↦ (h 1 le_rfl).1 (by rw [h0, map_zero]), fun n hn ↦ ?_⟩
  have h7 : evalAtField n ((C (X ^ (4 * (2 * m + 3))) * pairQVar m) ^ (m + 1)) =
      (qParam ^ (2 * m + 3) * qParam ^ (n + (2 * m + 3))) ^ (m + 1) := by
    rw [map_pow, map_mul, evalAtField_C_X_pow_four_mul_pairQ, evalAtField_pairQVar]
  rw [← (h n hn).2, pairQTransferRhs]
  simp only [evalAtField_famDet_comp_pairQ, h7, famKernel,
    cyclotomicKernel_eq_evalAtField_div_pairQ, evalAtField_pairQDenomCoeff]

end AJConjecture
