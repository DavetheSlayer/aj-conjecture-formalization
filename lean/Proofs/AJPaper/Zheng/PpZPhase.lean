import Mathlib
import AJHandoff.Geometry.GeoPhysDefs

/-!
# The phase `a_n^β` near `n = N/2` (Unit PpZ, node `PpZ_Phase`)

Source: Zheng, (3.32): `a_n = e^{(n'²/(2N) - N/8 + n/(2N))πi}`, `n' = n - N/2`, and
`n/(2N) = 1/4 + n'/(2N)`.

`ppZ_phasePow_approx`: `‖a_n^β - e^{iβπ(n'²/(2N) - N/8 + 1/4)}‖ ≤ |β| π |n'|/(2N)`.

Route. `geoPhaseArg N n = π(n'²/(2N) - N/8 + 1/4) + π n'/(2N)` (`field_simp; ring`, `N ≠ 0`);
`‖e^{ix} - e^{iy}‖ ≤ |x - y|` (`Complex.norm_exp_I_mul_ofReal_sub_one_le` or
`Real.norm_exp_I_mul_ofReal_sub_one_le` after factoring `e^{iy}`).
-/

noncomputable section

namespace AJConjecture

/-- `‖a_n^β - e^{iβπ((n-N/2)²/(2N) - N/8 + 1/4)}‖ ≤ |β| π |n - N/2|/(2N)`. -/
theorem ppZ_phasePow_approx (N n : ℕ) (hN : 1 ≤ N) (β : ℝ) :
    ‖geoPhasePow N n β -
        Complex.exp (((β * Real.pi * (((n : ℝ) - N / 2) ^ 2 / (2 * N) - N / 8 + 1 / 4) : ℝ) : ℂ) *
          Complex.I)‖ ≤
      |β| * Real.pi * |(n : ℝ) - N / 2| / (2 * N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set y : ℝ := β * Real.pi * (((n : ℝ) - N / 2) ^ 2 / (2 * N) - N / 8 + 1 / 4) with hy
  set d : ℝ := β * Real.pi * ((n : ℝ) - N / 2) / (2 * N) with hd
  have hx : β * geoPhaseArg N n = y + d := by
    rw [hy, hd, geoPhaseArg]; field_simp; ring
  have e : geoPhasePow N n β - Complex.exp ((y : ℂ) * Complex.I) =
      Complex.exp ((y : ℂ) * Complex.I) * (Complex.exp (Complex.I * (d : ℂ)) - 1) := by
    rw [geoPhasePow, hx, mul_sub, mul_one, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [hd, Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * N)]

end AJConjecture
