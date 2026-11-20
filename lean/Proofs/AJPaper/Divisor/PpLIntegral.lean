import Mathlib
import AJConjecture.QAlgPseudoFactorNormalize
import AJTwist.Factor.TwFZeroIntegral
import AJPaper.Divisor.PpLNormal
import AJPaper.Divisor.PpLJetRules

/-!
# The normal form of the adjoint over `ℤ[t][x]`, normalised at `t = -1` (Unit PpL, node
`PpL_Integral`)

Source: Section 5.6 of the paper: "Normalize `g` by a scalar parameter power so its reduction is
a nonzero rational function `g_0(x)`." Mirror of `AJTwist/Factor/TwFZeroIntegral.lean`.

`ppl_adjoint_integralForm`: if `(e₀, e₁)` solves the Riccati equation of `pplAdjOpX` and
`e₀(-1, x) ≠ 0`, `e₁(-1, x) ≠ 0`, the normal form holds with polynomial data: `c_n, c_d ∈ ℤ[t]`
nonzero at `t = -1` and `g ∈ ℤ[t][x]` with `g(-1, x) ≠ 0`:

`e₀ · c_d · t⁶⁸ x² ℓ₃ ℓ₅ · τ(g) = c_n · x^μ ∏_{j<4} ℓ_{pplIdx j}^{ε_j} · τ²(e₁) · g` in `ℤ[t][x]`.

Route: verbatim the template. `exists_twfIota_eq_C_mul` (public) writes `g = C γ * twfIota g'`
with `g'(-1, x) ≠ 0`, and `γ` cancels (`twfTau (C γ * f) = C γ * twfTau f`); write
`c = twTHom c_n / twTHom c_d` and descend along the injective `twfIota`; split off the powers of
`t + 1` from `c_n`, `c_d`. Both sides of the identity have nonzero value at `t = -1`
(`ppl_map_evalRingHom_twfLin`-type facts: `ℓ_j ↦ x - 1`, `t⁶⁸ ↦ 1`, `x ↦ x`,
`map_evalRingHom_twfShiftX`), so the two powers of `t + 1` agree (`eq_of_pow_mul_eq_pow_mul`).

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The coefficient map `ℤ[t] → ℚ(t)` factors through `ℚ[t]`. -/
private theorem twTHom_apply_pplIntegral (x : ℤ[X]) :
    twTHom x = algebraMap ℚ[X] (RatFunc ℚ) (x.map (Int.castRingHom ℚ)) := by
  have h : twTHom =
      (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp [twTHom]
    · simp [twTHom, RatFunc.algebraMap_X]
  rw [h]
  rfl

/-- The coefficient map `ℤ[t] → ℚ(t)` is injective. -/
private theorem twTHom_injective_pplIntegral : Function.Injective twTHom := by
  intro x y h
  rw [twTHom_apply_pplIntegral, twTHom_apply_pplIntegral] at h
  exact Polynomial.map_injective _ Int.cast_injective (RatFunc.algebraMap_injective ℚ h)

/-- The coefficient map `ℤ[t][x] → ℚ(t)[x]` is injective. -/
private theorem twfIota_injective_pplIntegral : Function.Injective twfIota :=
  Polynomial.map_injective _ twTHom_injective_pplIntegral

/-- A rational polynomial has a nonzero integer multiple with integer coefficients. -/
private theorem exists_int_mul_eq_map_pplIntegral (p : ℚ[X]) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ p' : ℤ[X], p'.map (Int.castRingHom ℚ) = (N : ℚ[X]) * p := by
  obtain ⟨b, hb, h⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  refine ⟨b, nonZeroDivisors.ne_zero hb,
    IsLocalization.integerNormalization (nonZeroDivisors ℤ) p, ?_⟩
  rw [← zsmul_eq_mul, ← h, algebraMap_int_eq]

/-- An element of `ℚ(t)` is a quotient of images of elements of `ℤ[t]`. -/
private theorem exists_twTHom_mul_eq_pplIntegral (a : RatFunc ℚ) :
    ∃ b : ℤ[X], b ≠ 0 ∧ ∃ a' : ℤ[X], twTHom b * a = twTHom a' := by
  obtain ⟨N₁, hN₁, n', hn'⟩ := exists_int_mul_eq_map_pplIntegral a.num
  obtain ⟨N₂, hN₂, d', hd'⟩ := exists_int_mul_eq_map_pplIntegral a.denom
  have hden : algebraMap ℚ[X] (RatFunc ℚ) a.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero a.denom_ne_zero
  have ha : algebraMap ℚ[X] (RatFunc ℚ) a.num = a * algebraMap ℚ[X] (RatFunc ℚ) a.denom :=
    (div_eq_iff hden).mp (RatFunc.num_div_denom a)
  have hd'0 : d' ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hd'
    exact mul_ne_zero (Int.cast_ne_zero.mpr hN₂) a.denom_ne_zero hd'.symm
  have hTC : ∀ N : ℤ, twTHom (C N) = (N : RatFunc ℚ) := fun N ↦ by simp [twTHom]
  refine ⟨C N₁ * d', mul_ne_zero (C_ne_zero.mpr hN₁) hd'0, C N₂ * n', ?_⟩
  rw [map_mul, map_mul, twTHom_apply_pplIntegral d', twTHom_apply_pplIntegral n', hd',
    hn', hTC, hTC, map_mul, map_mul, map_intCast, map_intCast]
  linear_combination (-((N₁ : RatFunc ℚ) * (N₂ : RatFunc ℚ))) * ha

/-- A nonzero element of `ℤ[t]` is a power of `t + 1` times an element nonzero at `t = -1`. -/
private theorem exists_pow_mul_eval_ne_zero_pplIntegral {p : ℤ[X]} (hp : p ≠ 0) :
    ∃ (a : ℕ) (p' : ℤ[X]), p'.eval (-1) ≠ 0 ∧ p = (X + 1) ^ a * p' := by
  obtain ⟨n, p', hn, h⟩ := WfDvdMonoid.max_power_factor' hp not_isUnit_X_add_one
  refine ⟨n, p', fun h0 ↦ hn ?_, h⟩
  have hX : (X + 1 : ℤ[X]) = X - C (-1) := by rw [map_neg, sub_neg_eq_add, map_one]
  rw [hX]
  exact dvd_iff_isRoot.mpr h0

/-- The normal form of a solution of the Riccati equation of the adjoint of `P_0` over
`ℤ[t][x]`, normalised at `t = -1`. -/
theorem ppl_adjoint_integralForm {e₀ e₁ : Coeff}
    (h₀ : e₀.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (h₁ : e₁.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (hric : oreRiccati twfShiftX 3 pplAdjOpX e₀ e₁ = 0) :
    ∃ (cn cd : ℤ[X]) (μ : ℕ) (ε : Fin 4 → ℕ) (g : Coeff),
      cn.eval (-1) ≠ 0 ∧ cd.eval (-1) ≠ 0 ∧ g.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 ∧
      μ ≤ 2 ∧ (∀ j, ε j ≤ 1) ∧
      e₀ * C cd * (C (X ^ 68) * X ^ 2 * twfLin 3 * twfLin 5) * twfShiftX g =
        C cn * X ^ μ * (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j) *
          twfShiftX (twfShiftX e₁) * g := by
  have he₀ : e₀ ≠ 0 := fun h ↦ h₀ (by rw [h, Polynomial.map_zero])
  have he₁ : e₁ ≠ 0 := fun h ↦ h₁ (by rw [h, Polynomial.map_zero])
  obtain ⟨c, μ, ε, g, hc, hg, hμ, hε, hN⟩ := ppl_adjoint_normalForm he₀ he₁ hric
  obtain ⟨γ, g', hγ, hg', rfl⟩ := exists_twfIota_eq_C_mul hg
  obtain ⟨cd₀, hcd₀, cn₀, hcn₀⟩ := exists_twTHom_mul_eq_pplIntegral c
  have hcd₀' : twTHom cd₀ ≠ 0 :=
    (map_ne_zero_iff twTHom twTHom_injective_pplIntegral).mpr hcd₀
  have hcn₀0 : cn₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hcn₀
    exact mul_ne_zero hcd₀' hc hcn₀
  have hιC : ∀ b : ℤ[X], twfIota (C b) = C (twTHom b) := fun b ↦ Polynomial.map_C twTHom
  have hιX : twfIota X = X := Polynomial.map_X twTHom
  have hτ : twfTau (C γ * twfIota g') = C γ * twfIota (twfShiftX g') := by
    rw [map_mul, twfIota_twfShiftX]
    congr 1
    exact C_comp
  rw [hτ] at hN
  have hI₀ : e₀ * C cd₀ * (C (X ^ 68) * X ^ 2 * twfLin 3 * twfLin 5) * twfShiftX g' =
      C cn₀ * X ^ μ * (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j) *
        twfShiftX (twfShiftX e₁) * g' := by
    apply twfIota_injective_pplIntegral
    apply mul_left_cancel₀ (C_ne_zero.mpr hγ)
    simp only [map_mul, map_prod, map_pow, hιC, hιX] at hN ⊢
    rw [← hcn₀, C_mul]
    linear_combination C (twTHom cd₀) * hN
  obtain ⟨a, cn, hcn, rfl⟩ := exists_pow_mul_eval_ne_zero_pplIntegral hcn₀0
  obtain ⟨b, cd, hcd, rfl⟩ := exists_pow_mul_eval_ne_zero_pplIntegral hcd₀
  have hx1 : (X - 1 : ℤ[X]) ≠ 0 := X_sub_C_ne_zero 1
  have hU : (e₀ * C cd * (C (X ^ 68) * X ^ 2 * twfLin 3 * twfLin 5) * twfShiftX g').map
      (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 := by
    simp only [Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, coe_evalRingHom,
      map_evalRingHom_twfShiftX, ppl_map_evalRingHom_twfLin]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero h₀ (C_ne_zero.mpr hcd))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr ?_) (pow_ne_zero 2 X_ne_zero)) hx1)
        hx1)) hg'
    rw [eval_pow, eval_X]
    norm_num
  have hV : (C cn * X ^ μ * (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j) *
      twfShiftX (twfShiftX e₁) * g').map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 := by
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod, map_C, map_X,
      coe_evalRingHom, map_evalRingHom_twfShiftX, ppl_map_evalRingHom_twfLin]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hcn)
      (pow_ne_zero _ X_ne_zero)) (Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ hx1))
      h₁) hg'
  have hsC : ∀ c : Coeff, specialize (C c) = C (c.map (Polynomial.evalRingHom (-1 : ℤ))) :=
    fun c ↦ Polynomial.map_C _
  have hUV : (C (C ((X + 1 : ℤ[X]) ^ b)) : RecOp) *
      C (e₀ * C cd * (C (X ^ 68) * X ^ 2 * twfLin 3 * twfLin 5) * twfShiftX g') =
      C (C ((X + 1 : ℤ[X]) ^ a)) *
        C (C cn * X ^ μ * (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j) *
          twfShiftX (twfShiftX e₁) * g') := by
    rw [← C_mul, ← C_mul]
    refine congrArg C ?_
    rw [C_mul, C_mul] at hI₀
    linear_combination hI₀
  have hfin := C_injective (eq_of_pow_mul_eq_pow_mul
    (by rw [hsC]; exact C_ne_zero.mpr hU) (by rw [hsC]; exact C_ne_zero.mpr hV) hUV)
  exact ⟨cn, cd, μ, ε, g', hcn, hcd, hg', hμ, hε, hfin⟩

end AJConjecture
