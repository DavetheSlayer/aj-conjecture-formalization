import Mathlib

/-!
# An arithmetic–geometric sum (Unit PpZ, node `PpZ_P41Geom`)

Source: Zheng, (4.25).

For `ϱ ≠ 1` with `ϱ^T = -1`:
`∑_{t<T} (c₀ - d t) ϱ^t = (2c₀ - dT - 2dϱ/(1-ϱ))/(1-ϱ)`
(`∑ ϱ^t = 2/(1-ϱ)`, `∑ t ϱ^t = T/(1-ϱ) + 2ϱ/(1-ϱ)²`; induction on `T` for the polynomial
identity `(1-ϱ)² ∑_{t<T} (c₀ - dt) ϱ^t = (1-ϱ)(c₀ - (c₀ - dT)ϱ^T) - dϱ(1 - ϱ^T)`, then `hT`).

If moreover `|ϱ| = 1` and `c₀, d` are real with `d ≠ 0`, then
`ϱ/(1-ϱ) = -1/2 + (i/2) cot(θ/2)` (`ϱ = e^{iθ}`), so the numerator is
`(2c₀ - dT + d) - i d cot(θ/2)`: it vanishes only if `2c₀ - dT + d = 0` and `ϱ = -1`.
(Concretely: `Re(ϱ/(1-ϱ)) = -1/2` because `|ϱ| = 1`, and `Im(ϱ/(1-ϱ)) = Im ϱ/|1-ϱ|²`, which is
`0` only for `ϱ = ±1`.)
-/

noncomputable section

namespace AJConjecture

/-- The polynomial identity behind the arithmetic–geometric sum. -/
private theorem arithGeom_poly_P41Geom (T : ℕ) (ϱ c₀ d : ℂ) :
    (1 - ϱ) ^ 2 * ∑ t ∈ Finset.range T, (c₀ - d * t) * ϱ ^ t =
      (1 - ϱ) * (c₀ - (c₀ - d * T) * ϱ ^ T) - d * ϱ * (1 - ϱ ^ T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- `∑_{t<T} (c₀ - d t) ϱ^t = (2c₀ - dT - 2dϱ/(1-ϱ))/(1-ϱ)` when `ϱ^T = -1`, `ϱ ≠ 1`. -/
theorem ppZ_arithGeom_sum (T : ℕ) {ϱ : ℂ} (hϱ : ϱ ≠ 1) (hT : ϱ ^ T = -1) (c₀ d : ℂ) :
    ∑ t ∈ Finset.range T, (c₀ - d * t) * ϱ ^ t =
      (2 * c₀ - d * T - 2 * d * ϱ / (1 - ϱ)) / (1 - ϱ) := by
  have h1 : 1 - ϱ ≠ 0 := sub_ne_zero.mpr (Ne.symm hϱ)
  have h := arithGeom_poly_P41Geom T ϱ c₀ d
  rw [hT] at h
  rw [eq_div_iff h1]
  field_simp
  linear_combination h

set_option linter.unusedVariables false in
/-- The sum is nonzero unless `2c₀ - dT + d = 0` and `ϱ = -1`. -/
theorem ppZ_arithGeom_ne_zero (T : ℕ) {ϱ : ℂ} (hn : ‖ϱ‖ = 1) (hϱ : ϱ ≠ 1) (hT : ϱ ^ T = -1)
    {c₀ d : ℝ} (hd : d ≠ 0) (h : 2 * c₀ - d * T + d ≠ 0 ∨ ϱ ≠ -1) :
    ∑ t ∈ Finset.range T, ((c₀ : ℂ) - d * t) * ϱ ^ t ≠ 0 := by
  intro hsum
  have hpoly := arithGeom_poly_P41Geom T ϱ c₀ d
  rw [hsum, hT, mul_zero] at hpoly
  have hrel : ((2 * c₀ - d * T : ℝ) : ℂ) = ((2 * c₀ - d * T + 2 * d : ℝ) : ℂ) * ϱ := by
    push_cast
    linear_combination -hpoly
  have hnorm : |2 * c₀ - d * T| = |2 * c₀ - d * T + 2 * d| := by
    have hc := congrArg norm hrel
    rwa [norm_mul, hn, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs] at hc
  rcases abs_eq_abs.mp hnorm with h1 | h1
  · exact hd (by linarith)
  · have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
    have hK : 2 * c₀ - d * T = -d := by linarith
    have hmul : (d : ℂ) * (ϱ + 1) = 0 := by
      rw [hK] at hrel
      push_cast at hrel
      linear_combination -hrel
    have hϱ1 : ϱ = -1 := eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hmul).resolve_left hd')
    rcases h with h | h
    · exact h (by linarith)
    · exact h hϱ1

end AJConjecture
