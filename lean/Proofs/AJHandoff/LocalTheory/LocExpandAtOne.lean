import Mathlib

/-!
# Expansion of `ℚ(t)` at `t = 1` through `t = e^u`

`e^u ∈ ℚ[[u]]` is transcendental over `ℚ`: a nonzero `p ∈ ℚ[t]` is `(t - 1)^k p₁` with
`p₁(1) ≠ 0`, `e^u - 1 = u (1 + …) ≠ 0` and `p₁(e^u)` has constant coefficient `p₁(1) ≠ 0`. Hence
`t ↦ e^u` extends to an (injective) field homomorphism `ℚ(t) → ℚ((u))`. A rational function is
regular at `t = 1` when its expansion has no negative powers of `u`; such functions form a subring
containing `t^(±1)` and the inverses of polynomials not vanishing at `1`.

The variable `u` here is a formal parameter of the colour interpolation, unrelated to the
classical-specialization point `t = -1`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `e^u` as a Laurent series. -/
def expU : LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.exp ℚ)

/-- Evaluating a polynomial at `e^u` in `ℚ((u))` is the image of its evaluation in `ℚ[[u]]`. -/
private theorem eval₂_expU (p : ℚ[X]) :
    p.eval₂ (algebraMap ℚ (LaurentSeries ℚ)) expU =
      HahnSeries.ofPowerSeries ℤ ℚ (aeval (PowerSeries.exp ℚ) p) := by
  rw [aeval_def, hom_eval₂]
  congr 1

/-- The constant coefficient of `p(e^u)` is `p(1)`. -/
private theorem constantCoeff_aeval_exp (p : ℚ[X]) :
    PowerSeries.constantCoeff (aeval (PowerSeries.exp ℚ) p) = p.eval 1 := by
  rw [aeval_def, hom_eval₂, PowerSeries.constantCoeff_exp]
  have h : (PowerSeries.constantCoeff (R := ℚ)).comp (algebraMap ℚ (PowerSeries ℚ)) =
      RingHom.id ℚ := RingHom.ext_rat _ _
  rw [h]
  rfl

/-- `e^u` is transcendental over `ℚ`: `p(e^u) ≠ 0` for `p ≠ 0`. -/
private theorem aeval_exp_ne_zero {p : ℚ[X]} (hp : p ≠ 0) : aeval (PowerSeries.exp ℚ) p ≠ 0 := by
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1
  have hq1 : q.eval 1 ≠ 0 := fun h ↦ hq (dvd_iff_isRoot.mpr h)
  have hexp : PowerSeries.exp ℚ - 1 ≠ 0 := fun h ↦ by
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp [PowerSeries.coeff_exp] at h1
  have hqe : aeval (PowerSeries.exp ℚ) q ≠ 0 := fun h ↦ hq1 <| by
    rw [← constantCoeff_aeval_exp, h, map_zero]
  rw [hpq]
  simp only [map_mul, map_pow, map_sub, aeval_X, map_one]
  exact mul_ne_zero (pow_ne_zero _ hexp) hqe

theorem nonZeroDivisors_le_comap_expU :
    nonZeroDivisors ℚ[X] ≤ (nonZeroDivisors (LaurentSeries ℚ)).comap
      (Polynomial.eval₂RingHom (algebraMap ℚ (LaurentSeries ℚ)) expU) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, coe_eval₂RingHom, eval₂_expU]
  exact fun h ↦ aeval_exp_ne_zero (nonZeroDivisors.ne_zero hp)
    (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))

/-- The expansion `ℚ(t) → ℚ((u))`, `t ↦ e^u`. -/
def expandAtOne : RatFunc ℚ →+* LaurentSeries ℚ :=
  RatFunc.liftRingHom (Polynomial.eval₂RingHom (algebraMap ℚ (LaurentSeries ℚ)) expU)
    nonZeroDivisors_le_comap_expU

/-- `f ∈ ℚ(t)` is regular at `t = 1`: its expansion lies in `ℚ[[u]]`. -/
def IsRegularAtOne (f : RatFunc ℚ) : Prop :=
  ∃ g : PowerSeries ℚ, expandAtOne f = HahnSeries.ofPowerSeries ℤ ℚ g

theorem IsRegularAtOne.add {f g : RatFunc ℚ} (hf : IsRegularAtOne f) (hg : IsRegularAtOne g) :
    IsRegularAtOne (f + g) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩

theorem IsRegularAtOne.mul {f g : RatFunc ℚ} (hf : IsRegularAtOne f) (hg : IsRegularAtOne g) :
    IsRegularAtOne (f * g) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨a * b, by rw [map_mul, map_mul, ha, hb]⟩

/-- Polynomials, `t⁻¹`, and inverses of polynomials not vanishing at `1` are regular at `1`. -/
theorem isRegularAtOne_basic (p : ℚ[X]) :
    IsRegularAtOne (algebraMap ℚ[X] (RatFunc ℚ) p) ∧ IsRegularAtOne RatFunc.X⁻¹ ∧
      (p.eval 1 ≠ 0 → IsRegularAtOne (algebraMap ℚ[X] (RatFunc ℚ) p)⁻¹) := by
  have hp : expandAtOne (algebraMap ℚ[X] (RatFunc ℚ) p) =
      HahnSeries.ofPowerSeries ℤ ℚ (aeval (PowerSeries.exp ℚ) p) := by
    rw [expandAtOne, RatFunc.liftRingHom_algebraMap, coe_eval₂RingHom, eval₂_expU]
  refine ⟨⟨_, hp⟩, ⟨(PowerSeries.exp ℚ)⁻¹, ?_⟩,
    fun h1 ↦ ⟨(aeval (PowerSeries.exp ℚ) p)⁻¹, ?_⟩⟩
  · rw [map_inv₀, ← RatFunc.algebraMap_X, expandAtOne, RatFunc.liftRingHom_algebraMap,
      coe_eval₂RingHom, eval₂_X, expU]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← map_mul, PowerSeries.inv_mul_cancel _ (by simp), map_one]
  · rw [map_inv₀, hp]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← map_mul, PowerSeries.inv_mul_cancel _ (by rwa [constantCoeff_aeval_exp]), map_one]

/-- The expansion of a polynomial is its evaluation at `e^u` in `ℚ[[u]]`. -/
theorem expandAtOne_algebraMap (p : ℚ[X]) :
    expandAtOne (algebraMap ℚ[X] (RatFunc ℚ) p) =
      HahnSeries.ofPowerSeries ℤ ℚ (aeval (PowerSeries.exp ℚ) p) := by
  rw [expandAtOne, RatFunc.liftRingHom_algebraMap, coe_eval₂RingHom, eval₂_expU]

/-- `e^(m u) = (e^u)^m` for every integer `m`. -/
theorem ofPowerSeries_rescale_exp (m : ℤ) :
    HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.rescale (m : ℚ) (PowerSeries.exp ℚ)) = expU ^ m := by
  have hmul : ∀ a : ℚ, HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.rescale a (PowerSeries.exp ℚ)) *
      HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.rescale (-a) (PowerSeries.exp ℚ)) = 1 :=
    fun a ↦ by
      rw [← map_mul, PowerSeries.exp_mul_exp_eq_exp_add, add_neg_cancel, PowerSeries.rescale_zero]
      simp
  have hnat : ∀ k : ℕ, HahnSeries.ofPowerSeries ℤ ℚ
      (PowerSeries.rescale (k : ℚ) (PowerSeries.exp ℚ)) = expU ^ k := fun k ↦ by
    rw [← PowerSeries.exp_pow_eq_rescale_exp, map_pow, expU]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [Int.cast_natCast, hnat, zpow_natCast]
  · rw [zpow_neg, zpow_natCast, ← hnat, Int.cast_neg, Int.cast_natCast]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [mul_comm]
    exact hmul k

/-- The expansion of `t^m` is `e^(m u)`. -/
theorem expandAtOne_X_zpow (m : ℤ) :
    expandAtOne (RatFunc.X ^ m) =
      HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.rescale (m : ℚ) (PowerSeries.exp ℚ)) := by
  rw [ofPowerSeries_rescale_exp, map_zpow₀, ← RatFunc.algebraMap_X, expandAtOne,
    RatFunc.liftRingHom_algebraMap, coe_eval₂RingHom, eval₂_X]

end AJConjecture
