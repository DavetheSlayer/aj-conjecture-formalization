import Mathlib
import AJConjecture.WhiteheadFormula
import AJHandoff.LocalTheory.LocExpandAtOne

/-!
# The cyclotomic kernel at a formal colour

The regularized term `K_j(m) = (1 - q)^(-j) [m] C_j(m)`, with
`C_j(m) = ∏_{s=1}^{j} (1 - q^(s+m))(1 - q^(s-m))`
(`cyclotomicKernel`), `q = t⁴`, vanishes for `|m| ≤ j` (a factor `1 - q⁰`, or `[0] = 0`). With
`t = e^u` and the colour `m` replaced by a formal `x`, each factor `1 - e^(4(s ± x) u)` is `u`
times a power series in `ℚ[x][[u]]`, `1 - e^(4u)` is `u` times a unit, and
`[x] = (e^(2xu) - e^(-2xu))/(e^(2u) - e^(-2u))` lies in `ℚ[x][[u]]`. So the formal term is
`u^j` times an element of `ℚ[x][[u]]` (`2j` factors divisible by `u`, divided by `u^j`), and its
evaluation at every integer `m` is the expansion of `K_j(m)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The regularized cyclotomic term `K_j(m) = (1 - q)^(-j) [m] C_j(m)`. -/
def cycloTerm (j : ℕ) (m : ℤ) : RatFunc ℚ :=
  ((1 - qParam) ^ j)⁻¹ * quantumInt m * cyclotomicKernel j m

theorem cycloTerm_eq_zero {j : ℕ} {m : ℤ} (hm : m.natAbs ≤ j) : cycloTerm j m = 0 := by
  rcases lt_trichotomy m 0 with h | rfl | h
  · have hC : cyclotomicKernel j m = 0 := by
      refine Finset.prod_eq_zero (i := m.natAbs) (Finset.mem_Icc.mpr ⟨by omega, hm⟩) ?_
      have h0 : ((m.natAbs : ℕ) : ℤ) + m = 0 := by omega
      rw [h0, zpow_zero, sub_self, zero_mul]
    rw [cycloTerm, hC, mul_zero]
  · rw [cycloTerm, show quantumInt 0 = 0 by simp [quantumInt], mul_zero, zero_mul]
  · have hC : cyclotomicKernel j m = 0 := by
      refine Finset.prod_eq_zero (i := m.natAbs) (Finset.mem_Icc.mpr ⟨by omega, hm⟩) ?_
      have h0 : ((m.natAbs : ℕ) : ℤ) - m = 0 := by omega
      rw [h0, zpow_zero, sub_self, mul_zero]
    rw [cycloTerm, hC, mul_zero]

section FormalSeries

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The power series `(1 - e^(y u)) / u`. -/
private def oneSubExpDivX (y : R) : PowerSeries R :=
  PowerSeries.mk fun k ↦ -(algebraMap ℚ R (1 / ((k + 1).factorial : ℚ)) * y ^ (k + 1))

/-- The power series `(e^(y u) - e^(-y u)) / u`. -/
private def expSubExpNegDivX (y : R) : PowerSeries R :=
  PowerSeries.mk fun k ↦
    algebraMap ℚ R (1 / ((k + 1).factorial : ℚ)) * (y ^ (k + 1) - (-y) ^ (k + 1))

variable {R}

/-- `1 - e^(y u) = u · (1 - e^(y u)) / u`. -/
private theorem one_sub_rescale_exp_eq_X_mul (y : R) :
    1 - PowerSeries.rescale y (PowerSeries.exp R) = PowerSeries.X * oneSubExpDivX R y := by
  ext k
  rcases k with _ | k
  · simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
      PowerSeries.coeff_zero_X_mul]
    simp
  · simp [oneSubExpDivX, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_rescale,
      PowerSeries.coeff_exp, mul_comm]

/-- `e^(y u) - e^(-y u) = u · (e^(y u) - e^(-y u)) / u`. -/
private theorem rescale_exp_sub_rescale_exp_neg_eq_X_mul (y : R) :
    PowerSeries.rescale y (PowerSeries.exp R) - PowerSeries.rescale (-y) (PowerSeries.exp R) =
      PowerSeries.X * expSubExpNegDivX R y := by
  ext k
  rcases k with _ | k
  · simp only [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
      PowerSeries.coeff_zero_X_mul]
    simp
  · simp only [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
      PowerSeries.coeff_succ_X_mul, expSubExpNegDivX, PowerSeries.coeff_mk]
    ring

/-- Coefficientwise ring maps commute with `(1 - e^(y u)) / u`. -/
private theorem map_oneSubExpDivX {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S) (y : R) :
    PowerSeries.map f (oneSubExpDivX R y) = oneSubExpDivX S (f y) := by
  have hf : f.comp (algebraMap ℚ R) = algebraMap ℚ S := RingHom.ext_rat _ _
  ext k
  simp only [oneSubExpDivX, PowerSeries.coeff_map, PowerSeries.coeff_mk, map_neg, map_mul,
    map_pow, ← RingHom.comp_apply, hf]

/-- Coefficientwise ring maps commute with `(e^(y u) - e^(-y u)) / u`. -/
private theorem map_expSubExpNegDivX {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S) (y : R) :
    PowerSeries.map f (expSubExpNegDivX R y) = expSubExpNegDivX S (f y) := by
  have hf : f.comp (algebraMap ℚ R) = algebraMap ℚ S := RingHom.ext_rat _ _
  ext k
  simp only [expSubExpNegDivX, PowerSeries.coeff_map, PowerSeries.coeff_mk, map_sub, map_mul,
    map_pow, map_neg, ← RingHom.comp_apply, hf]

end FormalSeries

/-- Inversion commutes with `ℚ[[u]] → ℚ((u))` on series with nonzero constant coefficient. -/
private theorem ofPowerSeries_inv_of_constantCoeff_ne_zero {g : PowerSeries ℚ}
    (hg : PowerSeries.constantCoeff g ≠ 0) :
    HahnSeries.ofPowerSeries ℤ ℚ g⁻¹ = (HahnSeries.ofPowerSeries ℤ ℚ g)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, PowerSeries.inv_mul_cancel _ hg, map_one]

/-- The expansion of `1 - q^k` is `u · (1 - e^(4 k u)) / u`. -/
private theorem expandAtOne_one_sub_qParam_zpow (k : ℤ) :
    expandAtOne (1 - qParam ^ k) = HahnSeries.ofPowerSeries ℤ ℚ PowerSeries.X *
      HahnSeries.ofPowerSeries ℤ ℚ (oneSubExpDivX ℚ (4 * (k : ℚ))) := by
  have hq : qParam ^ k = (RatFunc.X : RatFunc ℚ) ^ (4 * k) := by
    rw [qParam, ← zpow_natCast, ← zpow_mul]
    rfl
  rw [map_sub, map_one, hq, expandAtOne_X_zpow, ← map_one
    (HahnSeries.ofPowerSeries ℤ ℚ), ← map_sub, ← map_mul, ← one_sub_rescale_exp_eq_X_mul]
  push_cast
  rfl

/-- The expansion of `[m]`. -/
private theorem expandAtOne_quantumInt (m : ℤ) :
    expandAtOne (quantumInt m) =
      HahnSeries.ofPowerSeries ℤ ℚ (expSubExpNegDivX ℚ (2 * (m : ℚ))) /
        HahnSeries.ofPowerSeries ℤ ℚ (expSubExpNegDivX ℚ 2) := by
  have hX : HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X : PowerSeries ℚ) ≠ 0 := by
    rw [HahnSeries.ofPowerSeries_X]
    exact HahnSeries.single_ne_zero one_ne_zero
  rw [quantumInt, map_div₀, map_sub, map_sub, expandAtOne_X_zpow, expandAtOne_X_zpow,
    expandAtOne_X_zpow, expandAtOne_X_zpow]
  have h1 := rescale_exp_sub_rescale_exp_neg_eq_X_mul (2 * (m : ℚ))
  have h2 := rescale_exp_sub_rescale_exp_neg_eq_X_mul (2 : ℚ)
  push_cast
  rw [← map_sub (HahnSeries.ofPowerSeries ℤ ℚ), ← map_sub (HahnSeries.ofPowerSeries ℤ ℚ), h1,
    h2, map_mul, map_mul, mul_div_mul_left _ _ hX]

/-- The formal-colour version of `K_j`: divisible by `u^j`, with the right integer values. -/
theorem exists_formal_cycloTerm (j : ℕ) :
    ∃ T : PowerSeries ℚ[X], (∀ r < j, PowerSeries.coeff r T = 0) ∧
      ∀ m : ℤ, HahnSeries.ofPowerSeries ℤ ℚ (T.map (Polynomial.evalRingHom (m : ℚ))) =
        expandAtOne (cycloTerm j m) := by
  set c₁ : PowerSeries ℚ := oneSubExpDivX ℚ 4 with hc₁
  set σ₁ : PowerSeries ℚ := expSubExpNegDivX ℚ 2 with hσ₁
  have hc₁0 : PowerSeries.constantCoeff c₁ ≠ 0 := by
    simp [c₁, oneSubExpDivX, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hσ₁0 : PowerSeries.constantCoeff σ₁ ≠ 0 := by
    simp [σ₁, expSubExpNegDivX, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  refine ⟨PowerSeries.X ^ j * (PowerSeries.map Polynomial.C (c₁⁻¹ ^ j * σ₁⁻¹) *
      expSubExpNegDivX ℚ[X] (2 * X) * ∏ s ∈ Finset.Icc 1 j,
        (oneSubExpDivX ℚ[X] (4 * (C (s : ℚ) + X)) * oneSubExpDivX ℚ[X] (4 * (C (s : ℚ) - X)))),
    fun r hr ↦ ?_, fun m ↦ ?_⟩
  · simp [PowerSeries.coeff_X_pow_mul', show ¬j ≤ r by omega]
  have hmap : ∀ g : PowerSeries ℚ, PowerSeries.map (Polynomial.evalRingHom (m : ℚ))
      (PowerSeries.map Polynomial.C g) = g := fun g ↦ by
    ext k
    simp [PowerSeries.coeff_map]
  have h1q : expandAtOne (1 - qParam) = HahnSeries.ofPowerSeries ℤ ℚ PowerSeries.X *
      HahnSeries.ofPowerSeries ℤ ℚ c₁ := by
    simpa [c₁] using expandAtOne_one_sub_qParam_zpow 1
  simp only [map_mul, map_pow, map_prod, PowerSeries.map_X, hmap, map_oneSubExpDivX,
    map_expSubExpNegDivX, Polynomial.coe_evalRingHom, eval_add, eval_sub, eval_C,
    eval_X, eval_ofNat, ofPowerSeries_inv_of_constantCoeff_ne_zero hc₁0,
    ofPowerSeries_inv_of_constantCoeff_ne_zero hσ₁0, cycloTerm, cyclotomicKernel, map_inv₀,
    h1q, expandAtOne_quantumInt, expandAtOne_one_sub_qParam_zpow]
  push_cast
  rw [← hσ₁]
  have hU : HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X : PowerSeries ℚ) ≠ 0 := by
    rw [HahnSeries.ofPowerSeries_X]
    exact HahnSeries.single_ne_zero one_ne_zero
  have hne : ∀ g : PowerSeries ℚ, PowerSeries.constantCoeff g ≠ 0 →
      HahnSeries.ofPowerSeries ℤ ℚ g ≠ 0 := fun g hg h ↦ hg <| by
    rw [HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm), map_zero]
  have hA := hne c₁ hc₁0
  have hB := hne σ₁ hσ₁0
  have hprod : ∀ (U : LaurentSeries ℚ) (a b : ℕ → LaurentSeries ℚ),
      ∏ x ∈ Finset.Icc 1 j, (U * a x * (U * b x)) =
        U ^ j * U ^ j * ∏ x ∈ Finset.Icc 1 j, (a x * b x) := fun U a b ↦ by
    rw [Finset.prod_congr rfl fun x _ ↦ show U * a x * (U * b x) = (U * U) * (a x * b x) by ring,
      Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, mul_pow]
  simp only [hprod]
  generalize ∏ x ∈ Finset.Icc 1 j,
    HahnSeries.ofPowerSeries ℤ ℚ (oneSubExpDivX ℚ (4 * ((x : ℚ) + m))) *
      HahnSeries.ofPowerSeries ℤ ℚ (oneSubExpDivX ℚ (4 * ((x : ℚ) - m))) = P
  rw [inv_pow]
  field_simp
  ring

end AJConjecture
