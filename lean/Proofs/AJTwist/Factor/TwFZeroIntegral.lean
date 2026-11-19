import Mathlib
import AJConjecture.QAlgPseudoFactorNormalize
import AJTwist.Factor.TwFZeroNormal

/-!
# The normal form over `ℤ[t][x]`, normalised at `t = -1` (TwF, unit F4)

Source: revision 5, Section 5.6: "Normalize `g` by a scalar parameter power so its reduction is a
nonzero rational function `g_0(x)`."

`twf_zero_integralForm`: if `(e₀, e₁)` solves the Riccati equation of `twfZeroOpX` and
`e₀(-1, x) ≠ 0`, `e₁(-1, x) ≠ 0`, then the normal form of `twf_zero_normalForm` holds with
polynomial data: `c = c_n/c_d` with `c_n, c_d ∈ ℤ[t]` nonzero at `t = -1`, and `g ∈ ℤ[t][x]` with
`g(-1, x) ≠ 0`:

`-e₀ · c_d · t²⁸ ℓ₁ ℓ₃ · τ(g) = c_n · x^μ ∏_{j<4} ℓ_j^{ε_j} · τ²(e₁) · g`   in `ℤ[t][x]`,

`τ = twfShiftX`.

Route. (i) A nonzero `g ∈ ℚ(t)[x]` is `C γ * twfIota g'` with `γ ∈ ℚ(t)^×`, `g' ∈ ℤ[t][x]`,
`g'(-1, x) ≠ 0`: clear the denominators of the coefficients
(`IsLocalization.integerNormalization` for `ℚ[t] ⊂ ℚ(t)`, then an integer for `ℤ[t] ⊂ ℚ[t]`) and
split off the power of `t + 1` (`exists_pow_mul_map_ne_zero` in
`AJConjecture/QAlgPseudoFactorNormalize.lean`). The scalar `γ` cancels from the identity because
`twfTau (C γ * f) = C γ * twfTau f`. (ii) Write `c = twTHom c_n / twTHom c_d`; `twfIota` is
injective, so the identity descends to `ℤ[t][x]`. (iii) Split `c_n = (t+1)^a c_n'`,
`c_d = (t+1)^b c_d'` with `c_n'(-1), c_d'(-1) ≠ 0`. Every other factor of the identity has
nonzero value at `t = -1` (`ℓ_j ↦ x - 1`, `t²⁸ ↦ 1`, the shift is the identity at `t = -1`:
`map_evalRingHom_iterate_coeffShift`-type lemma for `twfShiftX`), and `C (t + 1)` is prime in
`ℤ[t][x]`, so `a = b` and the powers cancel.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- At `t = -1` the shift `x ↦ t⁴ x` is the identity. -/
theorem map_evalRingHom_twfShiftX (c : Coeff) :
    (twfShiftX c).map (Polynomial.evalRingHom (-1 : ℤ)) =
      c.map (Polynomial.evalRingHom (-1 : ℤ)) := by
  change (c.comp (C (X ^ 4) * X)).map (Polynomial.evalRingHom (-1 : ℤ)) = _
  rw [map_comp, Polynomial.map_mul, map_C, map_X, coe_evalRingHom, eval_pow, eval_X]
  norm_num

/-- The coefficient map `ℤ[t] → ℚ(t)` factors through `ℚ[t]`. -/
private theorem twTHom_apply_twfZeroIntegral (x : ℤ[X]) :
    twTHom x = algebraMap ℚ[X] (RatFunc ℚ) (x.map (Int.castRingHom ℚ)) := by
  have h : twTHom =
      (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp [twTHom]
    · simp [twTHom, RatFunc.algebraMap_X]
  rw [h]
  rfl

/-- The coefficient map `ℤ[t] → ℚ(t)` is injective. -/
private theorem twTHom_injective_twfZeroIntegral : Function.Injective twTHom := by
  intro x y h
  rw [twTHom_apply_twfZeroIntegral, twTHom_apply_twfZeroIntegral] at h
  exact Polynomial.map_injective _ Int.cast_injective (RatFunc.algebraMap_injective ℚ h)

/-- The coefficient map `ℤ[t][x] → ℚ(t)[x]` is injective. -/
private theorem twfIota_injective_twfZeroIntegral : Function.Injective twfIota :=
  Polynomial.map_injective _ twTHom_injective_twfZeroIntegral

/-- A rational polynomial has a nonzero integer multiple with integer coefficients. -/
private theorem exists_int_mul_eq_map_twfZeroIntegral (p : ℚ[X]) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ p' : ℤ[X], p'.map (Int.castRingHom ℚ) = (N : ℚ[X]) * p := by
  obtain ⟨b, hb, h⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  refine ⟨b, nonZeroDivisors.ne_zero hb,
    IsLocalization.integerNormalization (nonZeroDivisors ℤ) p, ?_⟩
  rw [← zsmul_eq_mul, ← h, algebraMap_int_eq]

/-- An element of `ℚ(t)` is a quotient of images of elements of `ℤ[t]`. -/
private theorem exists_twTHom_mul_eq_twfZeroIntegral (a : RatFunc ℚ) :
    ∃ b : ℤ[X], b ≠ 0 ∧ ∃ a' : ℤ[X], twTHom b * a = twTHom a' := by
  obtain ⟨N₁, hN₁, n', hn'⟩ := exists_int_mul_eq_map_twfZeroIntegral a.num
  obtain ⟨N₂, hN₂, d', hd'⟩ := exists_int_mul_eq_map_twfZeroIntegral a.denom
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
  rw [map_mul, map_mul, twTHom_apply_twfZeroIntegral d', twTHom_apply_twfZeroIntegral n', hd',
    hn', hTC, hTC, map_mul, map_mul, map_intCast, map_intCast]
  linear_combination (-((N₁ : RatFunc ℚ) * (N₂ : RatFunc ℚ))) * ha

/-- A polynomial over `ℚ(t)` has a multiple by a nonzero element of `ℤ[t]` with coefficients in
`ℤ[t]`. -/
private theorem exists_C_mul_eq_twfIota_twfZeroIntegral (g : (RatFunc ℚ)[X]) :
    ∃ b : ℤ[X], b ≠ 0 ∧ ∃ g' : Coeff, C (twTHom b) * g = twfIota g' := by
  have hC : ∀ b : ℤ[X], twfIota (C b) = C (twTHom b) := fun b ↦ Polynomial.map_C twTHom
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨b₁, hb₁, p', hp'⟩ := hp
    obtain ⟨b₂, hb₂, q', hq'⟩ := hq
    refine ⟨b₁ * b₂, mul_ne_zero hb₁ hb₂, C b₂ * p' + C b₁ * q', ?_⟩
    rw [map_add twfIota, map_mul twfIota, map_mul twfIota, hC, hC, ← hp', ← hq',
      map_mul twTHom, C_mul]
    ring
  | monomial n a =>
    obtain ⟨b, hb, a', ha'⟩ := exists_twTHom_mul_eq_twfZeroIntegral a
    refine ⟨b, hb, monomial n a', ?_⟩
    rw [C_mul_monomial, ha']
    exact (Polynomial.map_monomial twTHom).symm

/-- A nonzero element of `ℤ[t]` is a power of `t + 1` times an element nonzero at `t = -1`. -/
private theorem exists_pow_mul_eval_ne_zero_twfZeroIntegral {p : ℤ[X]} (hp : p ≠ 0) :
    ∃ (a : ℕ) (p' : ℤ[X]), p'.eval (-1) ≠ 0 ∧ p = (X + 1) ^ a * p' := by
  obtain ⟨n, p', hn, h⟩ := WfDvdMonoid.max_power_factor' hp not_isUnit_X_add_one
  refine ⟨n, p', fun h0 ↦ hn ?_, h⟩
  have hX : (X + 1 : ℤ[X]) = X - C (-1) := by rw [map_neg, sub_neg_eq_add, map_one]
  rw [hX]
  exact dvd_iff_isRoot.mpr h0

/-- At `t = -1` the linear forms `ℓ_j` become `x - 1`. -/
private theorem map_evalRingHom_twfLin_twfZeroIntegral (j : ℕ) :
    (twfLin j).map (Polynomial.evalRingHom (-1 : ℤ)) = X - 1 := by
  rw [twfLin, Polynomial.map_sub, Polynomial.map_mul, map_C, map_X, Polynomial.map_one,
    coe_evalRingHom, eval_pow, eval_X, pow_mul]
  norm_num

/-- A nonzero polynomial over `ℚ(t)` is a constant times the image of a polynomial over `ℤ[t]`
with nonzero value at `t = -1`. -/
theorem exists_twfIota_eq_C_mul {g : (RatFunc ℚ)[X]} (hg : g ≠ 0) :
    ∃ (γ : RatFunc ℚ) (g' : Coeff), γ ≠ 0 ∧ g'.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 ∧
      g = C γ * twfIota g' := by
  obtain ⟨b, hb, g'', hg''⟩ := exists_C_mul_eq_twfIota_twfZeroIntegral g
  have hb' : twTHom b ≠ 0 := (map_ne_zero_iff twTHom twTHom_injective_twfZeroIntegral).mpr hb
  have hg''0 : g'' ≠ 0 := by
    rintro rfl
    rw [map_zero] at hg''
    exact mul_ne_zero (C_ne_zero.mpr hb') hg hg''
  obtain ⟨a, g', hg', rfl⟩ := exists_pow_mul_map_ne_zero hg''0
  have ha' : twTHom ((X + 1) ^ a) ≠ 0 :=
    (map_ne_zero_iff twTHom twTHom_injective_twfZeroIntegral).mpr
      (pow_ne_zero _ (X_add_C_ne_zero (1 : ℤ)))
  refine ⟨(twTHom b)⁻¹ * twTHom ((X + 1) ^ a), g', mul_ne_zero (inv_ne_zero hb') ha', hg', ?_⟩
  have hC : twfIota (C ((X + 1 : ℤ[X]) ^ a)) = C (twTHom ((X + 1) ^ a)) :=
    Polynomial.map_C twTHom
  rw [map_mul, hC] at hg''
  refine mul_left_cancel₀ (C_ne_zero.mpr hb') ?_
  rw [hg'', C_mul, ← mul_assoc, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hb', C_1, one_mul]

/-- The normal form of a solution of the Riccati equation of `P_0` over `ℤ[t][x]`, normalised at
`t = -1`. -/
theorem twf_zero_integralForm {e₀ e₁ : Coeff}
    (h₀ : e₀.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (h₁ : e₁.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (hric : oreRiccati twfShiftX 3 twfZeroOpX e₀ e₁ = 0) :
    ∃ (cn cd : ℤ[X]) (μ : ℕ) (ε : Fin 4 → ℕ) (g : Coeff),
      cn.eval (-1) ≠ 0 ∧ cd.eval (-1) ≠ 0 ∧ g.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 ∧
      μ ≤ 2 ∧ (∀ j, ε j ≤ 1) ∧
      -e₀ * C cd * (C (X ^ 28) * twfLin 1 * twfLin 3) * twfShiftX g =
        C cn * X ^ μ * (∏ j : Fin 4, twfLin j ^ ε j) * twfShiftX (twfShiftX e₁) * g := by
  have he₀ : e₀ ≠ 0 := fun h ↦ h₀ (by rw [h, Polynomial.map_zero])
  have he₁ : e₁ ≠ 0 := fun h ↦ h₁ (by rw [h, Polynomial.map_zero])
  obtain ⟨c, μ, ε, g, hc, hg, hμ, hε, hN⟩ := twf_zero_normalForm he₀ he₁ hric
  obtain ⟨γ, g', hγ, hg', rfl⟩ := exists_twfIota_eq_C_mul hg
  obtain ⟨cd₀, hcd₀, cn₀, hcn₀⟩ := exists_twTHom_mul_eq_twfZeroIntegral c
  have hcd₀' : twTHom cd₀ ≠ 0 :=
    (map_ne_zero_iff twTHom twTHom_injective_twfZeroIntegral).mpr hcd₀
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
  have hI₀ : -e₀ * C cd₀ * (C (X ^ 28) * twfLin 1 * twfLin 3) * twfShiftX g' =
      C cn₀ * X ^ μ * (∏ j : Fin 4, twfLin j ^ ε j) * twfShiftX (twfShiftX e₁) * g' := by
    apply twfIota_injective_twfZeroIntegral
    apply mul_left_cancel₀ (C_ne_zero.mpr hγ)
    simp only [map_mul, map_neg, map_prod, map_pow, hιC, hιX] at hN ⊢
    rw [← hcn₀, C_mul]
    linear_combination C (twTHom cd₀) * hN
  obtain ⟨a, cn, hcn, rfl⟩ := exists_pow_mul_eval_ne_zero_twfZeroIntegral hcn₀0
  obtain ⟨b, cd, hcd, rfl⟩ := exists_pow_mul_eval_ne_zero_twfZeroIntegral hcd₀
  have hx1 : (X - 1 : ℤ[X]) ≠ 0 := X_sub_C_ne_zero 1
  have hU : (-e₀ * C cd * (C (X ^ 28) * twfLin 1 * twfLin 3) * twfShiftX g').map
      (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 := by
    simp only [Polynomial.map_mul, Polynomial.map_neg, map_C, coe_evalRingHom,
      map_evalRingHom_twfShiftX, map_evalRingHom_twfLin_twfZeroIntegral]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h₀) (C_ne_zero.mpr hcd))
      (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr ?_) hx1) hx1)) hg'
    rw [eval_pow, eval_X]
    norm_num
  have hV : (C cn * X ^ μ * (∏ j : Fin 4, twfLin j ^ ε j) * twfShiftX (twfShiftX e₁) * g').map
      (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 := by
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod, map_C, map_X,
      coe_evalRingHom, map_evalRingHom_twfShiftX, map_evalRingHom_twfLin_twfZeroIntegral]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hcn)
      (pow_ne_zero _ X_ne_zero)) (Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ hx1))
      h₁) hg'
  have hsC : ∀ c : Coeff, specialize (C c) = C (c.map (Polynomial.evalRingHom (-1 : ℤ))) :=
    fun c ↦ Polynomial.map_C _
  have hUV : (C (C ((X + 1 : ℤ[X]) ^ b)) : RecOp) *
      C (-e₀ * C cd * (C (X ^ 28) * twfLin 1 * twfLin 3) * twfShiftX g') =
      C (C ((X + 1 : ℤ[X]) ^ a)) *
        C (C cn * X ^ μ * (∏ j : Fin 4, twfLin j ^ ε j) * twfShiftX (twfShiftX e₁) * g') := by
    rw [← C_mul, ← C_mul]
    refine congrArg C ?_
    rw [C_mul, C_mul] at hI₀
    linear_combination hI₀
  have hfin := C_injective (eq_of_pow_mul_eq_pow_mul
    (by rw [hsC]; exact C_ne_zero.mpr hU) (by rw [hsC]; exact C_ne_zero.mpr hV) hUV)
  exact ⟨cn, cd, μ, ε, g', hcn, hcd, hg', hμ, hε, hfin⟩

end AJConjecture
