import Mathlib
import AJTwist.Select.TwSSelects
import AJTwist.Select.TwSPeriodOrder
import AJTwist.Select.TwSCutoffOne
import AJTwist.Select.TwSCoefActualNeg
import AJTwist.Select.TwSCoefBoundNeg
import AJTwist.Select.TwSCtrlDivision
import AJTwist.Select.TwSInvClass
import AJTwist.Select.TwSInvFormula

/-!
# Selection by controlled coefficients: the mirror companion at `a ≥ 0`

Source: Section 6.6 of `selection.tex` (revision 5), the row `η = -1, a ≥ 0` of Table 1. Here
`ℓ = -γ`, `γ = r s + a`.

The class is the pullback under the normalized inversion `𝓑` of `TwsCtrlB (4 (γ+1))`.
`𝓑 G_c = Y_{1,N}` of the inverted period input `twsPeriodInput γ (-c)`
(`tws_inv_reducedFormula`, `twsInv_twsPeriodInput`), whose cleared form has a controlled
expansion with coefficients of order at least `-(j² + O(j)) / (4 (γ+1))`
(`tws_ctrl_clearedY_one`, `tws_bound_coef_one_of_input`). `𝓑 F = Y_{1,N}` of the inverted actual
input `q^(a n(n+1)) V_n(q)` (`twsInv_twsInput_false`), whose coefficient of `M^(4 (a+1) k)` has
order `4 (-(a+1) k² + a k)` (`tws_order_coef_one_of_input`); the gap
`1 / (4 (a+1)) - 1 / (4 (γ+1)) = r s / (4 (a+1)(γ+1)) > 0` overcomes every linear loss
(`tws_not_sat_ctrlB`, `tws_not_sat_bPull`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- On the positive colours the normalized inversion of the finite transform is `Y_{1,N}` of
the inverted input. -/
private theorem twsB_reducedFormulaEven_twsRangeGaussNeg (u : ℕ → RatFunc ℚ) {n : ℤ}
    (hn : 1 ≤ n) :
    twsB (pairQReducedFormulaEven u) n = twsY true (fun k ↦ twsInv (u k)) n.toNat := by
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
  have hN : 1 ≤ N := by omega
  rw [twsB, pairQReducedFormulaEven, Int.natAbs_natCast, Int.toNat_natCast,
    ← tws_inv_reducedFormula u hN, ← zpow_natCast qParam (N * (N - 1)), Nat.cast_mul,
    Nat.cast_sub hN, Nat.cast_one]

/-- The power `M² = t^(4n)` is `q^n`. -/
private theorem ratFuncX_zpow_eq_qParam_pow_twsRangeGaussNeg (N : ℕ) :
    (RatFunc.X : RatFunc ℚ) ^ (0 + 2 * (N : ℤ) * 2) = qParam ^ N := by
  rw [← zpow_natCast qParam, qParam_zpow_eq_ratFuncX_zpow]
  congr 1
  ring

/-- On the positive colours, `(1 - M²)` times the normalized inversion of the finite transform
is the cleared kernel sum of the inverted input. -/
private theorem twsB_sub_eq_clearedY_twsRangeGaussNeg (u : ℕ → RatFunc ℚ) {n : ℤ}
    (hn : 1 ≤ n) :
    twsB (pairQReducedFormulaEven u) n -
        (RatFunc.X : RatFunc ℚ) ^ (0 + 2 * n * 2) * twsB (pairQReducedFormulaEven u) n =
      twsClearedY true (fun k ↦ twsInv (u k)) n := by
  rw [twsB_reducedFormulaEven_twsRangeGaussNeg u hn, twsClearedY]
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
  rw [ratFuncX_zpow_eq_qParam_pow_twsRangeGaussNeg, Int.toNat_natCast]
  ring

/-- If the saturation of a growth class contains the normalized inversion of a finite transform,
it contains the cleared kernel sum of the inverted input. -/
private theorem twsSat_clearedY_of_twsB_twsRangeGaussNeg {U : (ℤ → RatFunc ℚ) → Prop}
    (hU : TwsGrowthClass U) {u : ℕ → RatFunc ℚ}
    (h : TwsSat U (twsB (pairQReducedFormulaEven u))) :
    TwsSat U (twsClearedY true fun k ↦ twsInv (u k)) :=
  hU.sat.congr_tail (hU.sat.sub h (hU.sat.monomial 0 2 h)) (n₀ := 1) fun _ hn ↦
    twsB_sub_eq_clearedY_twsRangeGaussNeg u hn

/-- If a growth class contains the cleared kernel sum of the inverted input, its saturation
contains the normalized inversion of the finite transform. -/
private theorem twsSat_twsB_of_clearedY_twsRangeGaussNeg {U : (ℤ → RatFunc ℚ) → Prop}
    (hU : TwsGrowthClass U) {u : ℕ → RatFunc ℚ}
    (h : U (twsClearedY true fun k ↦ twsInv (u k))) :
    TwsSat U (twsB (pairQReducedFormulaEven u)) := by
  have hκ : (1 - X ^ 2 : Coeff) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun p : Coeff ↦ p.coeff 0) h0
    simp at h1
  refine ⟨1 - X ^ 2, hκ, hU.congr_tail h (n₀ := 1) fun n hn ↦ ?_⟩
  have he : evalAtField n (1 - X ^ 2 : Coeff) =
      1 - (RatFunc.X : RatFunc ℚ) ^ (0 + 2 * n * 2) := by
    simp only [evalAtField, map_sub, map_one, map_pow, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
    rw [zero_add, zpow_mul (RatFunc.X : RatFunc ℚ) (2 * n) 2, zpow_ofNat]
  rw [he, ← twsB_sub_eq_clearedY_twsRangeGaussNeg u hn]
  ring

/-- The bound on the coefficients `A'_d` in terms of the `M`-degree. -/
private theorem twsCoefM_bound_twsRangeGaussNeg {w : ℕ → RatFunc ℚ} {D : ℤ}
    (h : ∃ C : ℤ, ∀ d : ℕ, twsCoef true w d = 0 ∨
      -((2 * (d : ℤ)) ^ 2 + C * (2 * (d : ℤ)) + C) ≤ D * (twsCoef true w d).order) :
    ∃ C : ℤ, ∀ j : ℤ, twsCoefM true w j = 0 ∨
      -(j ^ 2 + C * |j| + C) ≤ D * (twsCoefM true w j).order := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun j ↦ ?_⟩
  by_cases hj : 0 ≤ j ∧ 2 ∣ j
  · have h1 : 2 * (((j / 2).toNat : ℕ) : ℤ) = j := by omega
    have h2 : |j| = j := abs_of_nonneg hj.1
    have h3 := hC (j / 2).toNat
    rw [h1] at h3
    rw [twsCoefM, ite_eq_left hj, h2]
    exact h3
  · exact Or.inl (by rw [twsCoefM, ite_eq_right hj])

/-- The inverted period inputs of a negative twist have order bounded below. -/
private theorem tOrder_periodInput_ge_twsRangeGaussNeg {γ c : ℤ} (hγ : 1 ≤ γ) (n : ℕ) :
    twsPeriodInput γ c n = 0 ∨ -(4 * c ^ 2) ≤ pairQTOrder (twsPeriodInput γ c n) := by
  rcases tws_tOrder_periodInput_ge γ c n with h | h
  · exact Or.inl h
  refine Or.inr (le_trans ?_ h)
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hc := abs_nonneg c
  have hsq : |c| * |c| = c ^ 2 := by rw [abs_mul_abs_self, sq]
  rcases le_or_gt |c| (γ * n) with h1 | h1
  · have := mul_nonneg (sub_nonneg.mpr h1) (by omega : (0 : ℤ) ≤ (n : ℤ) + 1)
    nlinarith [sq_nonneg c]
  · have h2 : (n : ℤ) + 1 ≤ |c| := by nlinarith
    have h3 : 0 ≤ γ * (n : ℤ) * ((n : ℤ) + 1) := mul_nonneg (mul_nonneg (by omega) hn) (by omega)
    have h4 : |c| * ((n : ℤ) + 1) ≤ |c| * |c| := mul_le_mul_of_nonneg_left h2 hc
    linarith

/-- The normalized inversions of the Gaussian periods of a negative twist `ℓ = -γ` lie in the
saturation of the class of controlled expansions with the bound `4 (γ + 1)`. -/
private theorem twsSat_twsB_period_twsRangeGaussNeg {ℓ : ℤ} (hℓ : ℓ ≤ -1) {D : ℕ}
    (hD : (D : ℤ) = 4 * (-ℓ + 1)) (c : ℤ) : TwsSat (TwsCtrlB D) (twsB (twsPeriod ℓ c)) := by
  refine twsSat_twsB_of_clearedY_twsRangeGaussNeg (twsCtrlB_growthClass D) ?_
  have hw : (fun k ↦ twsInv (twsPeriodInput ℓ c k)) = twsPeriodInput (-ℓ) (-c) :=
    funext fun k ↦ twsInv_twsPeriodInput ℓ c k
  rw [hw]
  refine ⟨twsCoefM true (twsPeriodInput (-ℓ) (-c)),
    tws_ctrl_clearedY_one (C := 4 * (-c) ^ 2) fun n ↦
      tOrder_periodInput_ge_twsRangeGaussNeg (by omega) n, ?_⟩
  rw [hD]
  exact twsCoefM_bound_twsRangeGaussNeg
    (tws_bound_coef_one_of_input (by omega) (tws_tOrder_periodInput_ge (-ℓ) (-c)))

/-- The gap `1 / (4 (a+1)) - 1 / (4 (γ+1)) > 0`, `γ = m + a`, overcomes every linear loss: at
the degree `4 (a+1) k` with `k` large, the order `4 (-(a+1) k² + a k)` violates the bound with
constant `C`. -/
private theorem gap_twsRangeGaussNeg {a m C k : ℤ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    (hk : |C| + 16 * (m + a + 1) * a + 1 ≤ k) :
    4 * (m + a + 1) * (4 * (-(a + 1) * k ^ 2 + a * k)) <
      -((4 * (a + 1) * k) ^ 2 + C * |4 * (a + 1) * k| + C) := by
  have hC := le_abs_self C
  have hC0 := abs_nonneg C
  have hma : 0 ≤ (m + a + 1) * a := mul_nonneg (by omega) ha
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 ≤ k := by omega
  have habs : |4 * (a + 1) * k| = 4 * (a + 1) * k :=
    abs_of_nonneg (mul_nonneg (by omega) hk0)
  have hkk : k ≤ k * k := by nlinarith
  have h1 : C * (4 * (a + 1) * k) ≤ 4 * (a + 1) * (k * k) := by
    have h := mul_le_mul_of_nonneg_right (by linarith : C ≤ k)
      (mul_nonneg (by omega : (0 : ℤ) ≤ 4 * (a + 1)) hk0)
    linarith
  have h2 : C < k * k := by linarith
  have h3 : 16 * (m + a + 1) * a * k ≤ k * k :=
    mul_le_mul_of_nonneg_right (by linarith) hk0
  have h4 : 0 ≤ a * (k * k) := mul_nonneg ha (mul_nonneg hk0 hk0)
  have h5 : (a + 1) * (k * k) ≤ (a + 1) * m * (k * k) := by
    have := mul_le_mul_of_nonneg_left hm (mul_nonneg (by omega : (0 : ℤ) ≤ a + 1)
      (mul_nonneg hk0 hk0))
    linarith
  rw [habs]
  nlinarith

/-- The normalized inversion of the actual sequence of the mirror companion at `a ≥ 0` is not in
the saturation of the class of controlled expansions with the bound `4 (γ + 1)`, `γ = r s + a`. -/
private theorem not_twsSat_twsB_actual_twsRangeGaussNeg (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s)
    {ℓ : ℤ} {a : ℕ} (ha : twIndex false r s ℓ = a) {D : ℕ}
    (hD : (D : ℤ) = 4 * (((r * s : ℕ) : ℤ) + a + 1)) :
    ¬ TwsSat (TwsCtrlB D) (twsB (pairQReducedFormulaEven (twsInput false r s ℓ))) := by
  intro hsat
  have hv : ∀ n : ℕ, twsInv (twsInput false r s ℓ n) ≠ 0 ∧
      pairQTOrder (twsInv (twsInput false r s ℓ n)) = 4 * (a : ℤ) * n * ((n : ℤ) + 1) := by
    intro n
    have h := pairQTOrder_mul_eq
      (pairQTOrder_qParam_zpow_eq (twIndex false r s ℓ * n * ((n : ℤ) + 1)))
      (tws_tOrder_torusSum_true r s hr hs n)
    rw [← twsInv_twsInput_false, ha] at h
    exact ⟨h.1, h.2.trans (by ring)⟩
  have ha0 : (0 : ℤ) ≤ a := Int.natCast_nonneg a
  have hctrl := tws_ctrl_clearedY_one (w := fun k ↦ twsInv (twsInput false r s ℓ k)) (C := 0)
    fun n ↦ Or.inr (by
      rw [(hv n).2]
      have := mul_nonneg (mul_nonneg ha0 (Int.natCast_nonneg n))
        (by omega : (0 : ℤ) ≤ (n : ℤ) + 1)
      linarith)
  refine tws_not_sat_ctrlB hctrl (fun C ↦ ?_)
    (twsSat_clearedY_of_twsB_twsRangeGaussNeg (twsCtrlB_growthClass D) hsat)
  have hm : (1 : ℤ) ≤ ((r * s : ℕ) : ℤ) := by
    have : 1 ≤ r * s := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  set k : ℕ := (|C| + 16 * (((r * s : ℕ) : ℤ) + a + 1) * a + 1).toNat with hk
  have hk' : |C| + 16 * (((r * s : ℕ) : ℤ) + a + 1) * a + 1 ≤ (k : ℤ) := by
    rw [hk]
    exact Int.self_le_toNat _
  have hord := tws_order_coef_one_of_input hv k
  have hj : (0 : ℤ) ≤ 4 * ((a : ℤ) + 1) * k ∧ (2 : ℤ) ∣ 4 * ((a : ℤ) + 1) * k :=
    ⟨by positivity, ⟨2 * ((a : ℤ) + 1) * k, by ring⟩⟩
  have hd : (4 * ((a : ℤ) + 1) * k / 2).toNat = 2 * (a + 1) * k := by
    have h1 : 4 * ((a : ℤ) + 1) * k = 2 * ((2 * (a + 1) * k : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h1]
    omega
  refine ⟨4 * ((a : ℤ) + 1) * k, ?_, ?_⟩
  · rw [twsCoefM, ite_eq_left hj, hd]
    exact hord.1
  · rw [twsCoefM, ite_eq_left hj, hd, hord.2, hD]
    exact gap_twsRangeGaussNeg ha0 hm hk'

/-- Selection for the mirror companion at `a ≥ 0` (Section 6.6). -/
theorem tws_selects_neg_ge_zero (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (ℓ : ℤ)
    (ha : 0 ≤ twIndex false r s ℓ) : TwsSelects ℓ (twsInput false r s ℓ) := by
  obtain ⟨a, ha'⟩ := Int.eq_ofNat_of_zero_le ha
  have hm : (1 : ℤ) ≤ ((r * s : ℕ) : ℤ) := by
    have : 1 ≤ r * s := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hℓ : ℓ = -((r * s : ℕ) : ℤ) - a := by
    rw [twIndex] at ha'
    simp only [Bool.false_eq_true, ↓reduceIte] at ha'
    linarith
  have hD : ((4 * (r * s + a + 1) : ℕ) : ℤ) = 4 * (((r * s : ℕ) : ℤ) + a + 1) := by
    push_cast
    ring
  have hU := twsCtrlB_growthClass (4 * (r * s + a + 1))
  exact ⟨TwsBPull (TwsCtrlB (4 * (r * s + a + 1))), twsGrowthClass_bPull hU,
    fun c ↦ twsSat_bPull hU (twsSat_twsB_period_twsRangeGaussNeg (by omega)
      (by rw [hD, hℓ]; ring) c),
    tws_not_sat_bPull hU (not_twsSat_twsB_actual_twsRangeGaussNeg r s hr hs ha' hD)⟩

end AJConjecture
