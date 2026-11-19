import Mathlib
import AJTwist.Select.TwSSelects
import AJTwist.Select.TwSPeriodOrder
import AJTwist.Select.TwSCutoffZero
import AJTwist.Select.TwSCoefActualPos
import AJTwist.Select.TwSCoefBoundPos
import AJTwist.Select.TwSCtrlDivision
import AJTwist.Select.TwSCtrlLead
import AJTwist.Select.TwSLeadZero

/-!
# Selection by controlled coefficients: the right-handed companion at `a ≤ 0`

Source: Section 6.5 of `selection.tex` (revision 5), the rows `η = +1, a = 0` and
`η = +1, a < 0` of Table 1. Here `ℓ = γ = r s - a ≥ r s`.

Every Gaussian period satisfies `(1 - M⁴) G_c = t^(4N-4) · (1 - q^N) Y_{0,N}(w^{(ℓ,c)})`
(`tws_reducedFormula_eq_twsY`), and the cleared kernel sum has a controlled expansion
(`tws_ctrl_clearedY_zero`).

* `a = 0`: the class is `TwsCtrlAll`; `F_N` has order `4 (N-1)` and leading coefficient `N`
  (`tws_lead_reducedFormula_zero`, `tws_not_sat_ctrlAll_of_leadingCoeff`).
* `a = -b < 0`: the class is `TwsCtrlB (2 (2γ+1))` (`tws_bound_coef_zero_of_input`); the
  coefficient of `M^(2 (2b+1) k)` of the cleared actual sequence has order
  `-2 ((2b+1) k² - (2b-1) k)` (`tws_order_coef_zero_of_input`), and
  `2 (2γ+1) · 2 (2b+1) k² > (2 (2b+1) k)²` because `γ > b` (the quadratic gap
  `4 (2b+1)(γ - b) / (2γ+1)` of the manuscript); `tws_not_sat_ctrlB` concludes.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The coefficient `1 - M²`, evaluated at `M = t^(2n)`, is `1 - q^n`. -/
private theorem evalAtField_one_sub_sq_rangeGaussPos (n : ℤ) :
    evalAtField n (1 - X ^ 2 : Coeff) = 1 - (RatFunc.X : RatFunc ℚ) ^ (4 * n) := by
  rw [evalAtField, coe_eval₂RingHom, eval₂_sub, eval₂_one, eval₂_pow, eval₂_X, ← zpow_natCast,
    ← zpow_mul]
  congr 2
  push_cast
  ring

/-- The coefficient `1 - M²` is not zero. -/
private theorem one_sub_sq_ne_zero_rangeGaussPos : (1 - X ^ 2 : Coeff) ≠ 0 := fun h ↦ by
  have h1 := congrArg (Polynomial.eval 0) h
  simp at h1

/-- On positive colours the finite transform is `q^(n-1) Y_{0,n}` and the cleared kernel sum is
`(1 - q^n) Y_{0,n}`. -/
private theorem formula_and_clearedY_rangeGaussPos (u : ℕ → RatFunc ℚ) {n : ℤ} (hn : 1 ≤ n) :
    pairQReducedFormulaEven u n =
        (RatFunc.X : RatFunc ℚ) ^ (4 * n - 4) * twsY false u n.toNat ∧
      twsClearedY false u n = (1 - (RatFunc.X : RatFunc ℚ) ^ (4 * n)) * twsY false u n.toNat := by
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n by omega)
  have hN : 1 ≤ N := by omega
  have h1 : (4 * (N : ℤ) - 4) = 4 * ((N - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hN]
    push_cast
    ring
  rw [pairQReducedFormulaEven, Int.natAbs_natCast, twsClearedY, Int.toNat_natCast,
    tws_reducedFormula_eq_twsY u hN, h1, ← qParam_zpow_eq_ratFuncX_zpow,
    ← qParam_zpow_eq_ratFuncX_zpow, zpow_natCast, zpow_natCast]
  exact ⟨rfl, rfl⟩

/-- If the cleared kernel sum of an input belongs to a growth class, its finite transform belongs
to the saturation. -/
private theorem twsSat_formula_of_clearedY_rangeGaussPos {U : (ℤ → RatFunc ℚ) → Prop}
    (hU : TwsGrowthClass U) {w : ℕ → RatFunc ℚ} (h : U (twsClearedY false w)) :
    TwsSat U (pairQReducedFormulaEven w) := by
  refine ⟨1 - X ^ 2, one_sub_sq_ne_zero_rangeGaussPos,
    hU.congr_tail (hU.monomial (-4) 2 h) (n₀ := 1) fun n hn ↦ ?_⟩
  obtain ⟨h1, h2⟩ := formula_and_clearedY_rangeGaussPos w hn
  have h3 : (-4 + 2 * n * 2 : ℤ) = 4 * n - 4 := by ring
  rw [h1, h2, evalAtField_one_sub_sq_rangeGaussPos, h3]
  ring

/-- If a coefficient multiple of the finite transform of an input belongs to a growth class, so
does the same multiple of its cleared kernel sum. -/
private theorem clearedY_mem_of_formula_rangeGaussPos {U : (ℤ → RatFunc ℚ) → Prop}
    (hU : TwsGrowthClass U) {u : ℕ → RatFunc ℚ} {κ : Coeff}
    (h : U fun n ↦ evalAtField n κ * pairQReducedFormulaEven u n) :
    U fun n ↦ evalAtField n κ * twsClearedY false u n := by
  refine hU.congr_tail (hU.monomial 4 (-2) (hU.sub h (hU.monomial 0 2 h))) (n₀ := 1)
    fun n hn ↦ ?_
  obtain ⟨h1, h2⟩ := formula_and_clearedY_rangeGaussPos u hn
  have e1 : (RatFunc.X : RatFunc ℚ) ^ (4 + 2 * n * (-2)) * RatFunc.X ^ (4 * n - 4) = 1 := by
    have h0 : (4 + 2 * n * (-2) + (4 * n - 4) : ℤ) = 0 := by ring
    rw [← zpow_add₀ RatFunc.X_ne_zero, h0, zpow_zero]
  have e2 : (0 + 2 * n * 2 : ℤ) = 4 * n := by ring
  rw [h1, h2, e2]
  linear_combination
    (evalAtField n κ * twsY false u n.toNat * (1 - (RatFunc.X : RatFunc ℚ) ^ (4 * n))) * e1

/-- An input of order at least `4 (γ n(n+1) - B (n+1))`, `γ ≥ 1`, has order at least
`4 (n² - |B| n - |B|)`. -/
private theorem input_bound_rangeGaussPos {w : ℕ → RatFunc ℚ} {γ B : ℤ} (hγ : 1 ≤ γ)
    (hw : ∀ n : ℕ, w n = 0 ∨
      4 * (γ * n * ((n : ℤ) + 1) - B * ((n : ℤ) + 1)) ≤ pairQTOrder (w n)) (n : ℕ) :
    w n = 0 ∨ 4 * ((n : ℤ) ^ 2 - |B| * n - |B|) ≤ pairQTOrder (w n) := by
  refine (hw n).imp_right fun h ↦ le_trans ?_ h
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have h1 : (0 : ℤ) ≤ (γ - 1) * ((n : ℤ) * n) := mul_nonneg (by linarith) (mul_nonneg hn0 hn0)
  have h2 : (0 : ℤ) ≤ γ * n := mul_nonneg (by linarith) hn0
  have h3 : (0 : ℤ) ≤ (|B| - B) * ((n : ℤ) + 1) :=
    mul_nonneg (sub_nonneg.mpr (le_abs_self B)) (by linarith)
  nlinarith

/-- The bound for the coefficients `A'_d` gives the bound of the class `TwsCtrlB D`,
`D = 2 (2γ + 1)`, for the coefficients indexed by the `M`-degree. -/
private theorem coefM_bound_rangeGaussPos {w : ℕ → RatFunc ℚ} {γ : ℤ} {D : ℕ}
    (hD : (D : ℤ) = 2 * (2 * γ + 1))
    (h : ∃ C : ℤ, ∀ d : ℕ, twsCoef false w d = 0 ∨
      -((2 * (d : ℤ)) ^ 2 + C * (2 * (d : ℤ)) + C) ≤
        2 * (2 * γ + 1) * (twsCoef false w d).order) :
    ∃ C : ℤ, ∀ j : ℤ, twsCoefM false w j = 0 ∨
      -(j ^ 2 + C * |j| + C) ≤ (D : ℤ) * (twsCoefM false w j).order := by
  obtain ⟨C, hC⟩ := h
  refine ⟨|C|, fun j ↦ ?_⟩
  rw [twsCoefM]
  split_ifs with hc
  · have hj : j = 2 * ((j / 2).toNat : ℤ) := by lia
    have hj0 : (0 : ℤ) ≤ ((j / 2).toNat : ℤ) := Int.natCast_nonneg _
    refine (hC (j / 2).toNat).imp_right fun h ↦ le_trans ?_ (hD ▸ h)
    rw [abs_of_nonneg hc.1, ← hj]
    have h1 := le_abs_self C
    have h2 : C * j ≤ |C| * j := mul_le_mul_of_nonneg_right h1 hc.1
    linarith
  · exact Or.inl rfl

/-- The quadratic gap: for `γ > b ≥ 1` the exact order of the coefficient of degree
`d = (2b+1) k` violates the bound with the constant `C` when `k` is large. -/
private theorem gap_ineq_rangeGaussPos {γ b C k : ℤ} (hb : 1 ≤ b) (hγ : b < γ)
    (hk : k = 4 * (2 * γ + 1) * (2 * b - 1) + 2 * |C| * (2 * b + 1) + |C| + 1) :
    2 * (2 * γ + 1) * (-2 * ((2 * b + 1) * k ^ 2 - (2 * b - 1) * k)) <
      -((2 * ((2 * b + 1) * k)) ^ 2 + C * (2 * ((2 * b + 1) * k)) + C) := by
  have hC := abs_nonneg C
  have hC' := le_abs_self C
  have hL : 0 ≤ 4 * (2 * γ + 1) * (2 * b - 1) := mul_nonneg (by linarith) (by linarith)
  have hP : 0 ≤ |C| * (2 * b + 1) := mul_nonneg hC (by linarith)
  have hk1 : 1 ≤ k := by linarith
  have h1 : k * k = k * (4 * (2 * γ + 1) * (2 * b - 1) + 2 * |C| * (2 * b + 1) + |C| + 1) := by
    rw [← hk]
  have h2 : 1 ≤ (2 * b + 1) * (γ - b) := by nlinarith
  have h3 : 0 ≤ (8 * ((2 * b + 1) * (γ - b)) - 1) * (k * k) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have h4 : 0 ≤ (|C| - C) * ((2 * b + 1) * k) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have h5 : 0 ≤ |C| * (k - 1) := mul_nonneg hC (by linarith)
  nlinarith

/-- For an input of exact order `4 b n(n+1)`, `1 ≤ b < γ`, the coefficients of the cleared
kernel sum violate every bound of the class `TwsCtrlB (2 (2γ + 1))`. -/
private theorem coefM_unbounded_rangeGaussPos {u : ℕ → RatFunc ℚ} {b : ℕ} (hb : 1 ≤ b)
    (hu : ∀ n : ℕ, u n ≠ 0 ∧ pairQTOrder (u n) = 4 * (b : ℤ) * n * ((n : ℤ) + 1)) {γ : ℤ}
    (hγ : (b : ℤ) < γ) {D : ℕ} (hD : (D : ℤ) = 2 * (2 * γ + 1)) (C : ℤ) :
    ∃ j : ℤ, twsCoefM false u j ≠ 0 ∧
      (D : ℤ) * (twsCoefM false u j).order < -(j ^ 2 + C * |j| + C) := by
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hk0 : 0 ≤ 4 * (2 * γ + 1) * (2 * (b : ℤ) - 1) + 2 * |C| * (2 * (b : ℤ) + 1) + |C| := by
    have h1 : 0 ≤ 4 * (2 * γ + 1) * (2 * (b : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ |C| * (2 * (b : ℤ) + 1) := mul_nonneg (abs_nonneg C) (by linarith)
    linarith [abs_nonneg C]
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le
    (show 0 ≤ 4 * (2 * γ + 1) * (2 * (b : ℤ) - 1) + 2 * |C| * (2 * (b : ℤ) + 1) + |C| + 1 by
      linarith)
  have hk1 : 1 ≤ k := by
    have : (1 : ℤ) ≤ k := by linarith
    exact_mod_cast this
  obtain ⟨h0, ho⟩ := tws_order_coef_zero_of_input hb hu hk1
  have hj0 : (0 : ℤ) ≤ 2 * (((2 * b + 1) * k : ℕ) : ℤ) := by positivity
  have hM : twsCoefM false u (2 * (((2 * b + 1) * k : ℕ) : ℤ)) =
      twsCoef false u ((2 * b + 1) * k) := by
    have h1 : (2 * (((2 * b + 1) * k : ℕ) : ℤ) / 2).toNat = (2 * b + 1) * k := by lia
    rw [twsCoefM, ite_eq_left ⟨hj0, dvd_mul_right 2 _⟩, h1]
  refine ⟨2 * (((2 * b + 1) * k : ℕ) : ℤ), by rwa [hM], ?_⟩
  rw [hM, ho, hD, abs_of_nonneg hj0]
  push_cast
  exact gap_ineq_rangeGaussPos hb' hγ hk.symm

/-- Selection for the right-handed companion at `a = 0` (Section 6.5, varying leading
coefficient). -/
theorem tws_selects_pos_zero (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (ℓ : ℤ)
    (ha : twIndex true r s ℓ = 0) : TwsSelects ℓ (twsInput true r s ℓ) := by
  have hrs : (0 : ℤ) < ((r * s : ℕ) : ℤ) := by exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hidx : twIndex true r s ℓ = ((r * s : ℕ) : ℤ) - ℓ := by
    simp only [twIndex, ↓reduceIte]
  have hℓ : 1 ≤ ℓ := by omega
  refine ⟨TwsCtrlAll, twsCtrlAll_growthClass, fun c ↦ ?_, ?_⟩
  · exact twsSat_formula_of_clearedY_rangeGaussPos twsCtrlAll_growthClass
      ⟨_, tws_ctrl_clearedY_zero
        (input_bound_rangeGaussPos hℓ (tws_tOrder_periodInput_ge ℓ c))⟩
  · refine tws_not_sat_ctrlAll_of_leadingCoeff ⟨4, -4, 1, fun n hn ↦ ?_⟩
    obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n by omega)
    have h := tws_lead_reducedFormula_zero r s hr hs ℓ ha (N := N) (by omega)
    rw [pairQReducedFormulaEven, Int.natAbs_natCast, Int.cast_natCast]
    exact ⟨h.1, h.2.1.trans (by ring), h.2.2⟩

/-- Selection for the right-handed companion at `a < 0` (Section 6.5, quadratic gap of the
controlled coefficients). -/
theorem tws_selects_pos_lt_zero (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (ℓ : ℤ)
    (ha : twIndex true r s ℓ < 0) : TwsSelects ℓ (twsInput true r s ℓ) := by
  have hrs : (0 : ℤ) < ((r * s : ℕ) : ℤ) := by exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hidx : twIndex true r s ℓ = ((r * s : ℕ) : ℤ) - ℓ := by
    simp only [twIndex, ↓reduceIte]
  have hℓ : 1 ≤ ℓ := by omega
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -twIndex true r s ℓ by omega)
  obtain ⟨g, hg⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ ℓ by omega)
  have hb1 : 1 ≤ b := by omega
  have hD : ((2 * (2 * g + 1) : ℕ) : ℤ) = 2 * (2 * ℓ + 1) := by
    push_cast
    rw [hg]
  have hu : ∀ n : ℕ, twsInput true r s ℓ n ≠ 0 ∧
      pairQTOrder (twsInput true r s ℓ n) = 4 * (b : ℤ) * n * ((n : ℤ) + 1) := fun n ↦ by
    have h := tws_tOrder_input_true r s hr hs ℓ n
    exact ⟨h.1, h.2.trans (by rw [← hb]; ring)⟩
  have hu' : ∀ n : ℕ, twsInput true r s ℓ n = 0 ∨
      4 * ((b : ℤ) * n * ((n : ℤ) + 1) - 0 * ((n : ℤ) + 1)) ≤
        pairQTOrder (twsInput true r s ℓ n) := fun n ↦ Or.inr (by
    rw [(hu n).2]
    linarith)
  refine ⟨TwsCtrlB (2 * (2 * g + 1)), twsCtrlB_growthClass _, fun c ↦ ?_, fun hsat ↦ ?_⟩
  · exact twsSat_formula_of_clearedY_rangeGaussPos (twsCtrlB_growthClass _)
      ⟨_, tws_ctrl_clearedY_zero (input_bound_rangeGaussPos hℓ (tws_tOrder_periodInput_ge ℓ c)),
        coefM_bound_rangeGaussPos hD
          (tws_bound_coef_zero_of_input hℓ (tws_tOrder_periodInput_ge ℓ c))⟩
  · obtain ⟨κ, hκ, h⟩ := hsat
    exact tws_not_sat_ctrlB
      (tws_ctrl_clearedY_zero (input_bound_rangeGaussPos (by exact_mod_cast hb1) hu'))
      (coefM_unbounded_rangeGaussPos hb1 hu (by omega) hD)
      ⟨κ, hκ, clearedY_mem_of_formula_rangeGaussPos (twsCtrlB_growthClass _) h⟩

end AJConjecture
