import Mathlib
import AJPaper.Zheng.PpZModelFull

/-!
# The value of the Gaussian model sum over `ℤ²` (Unit PpZ, node `PpZ_ModelTsum`)

Source: Zheng, (3.30) and the constant (3.34): the Riemann sum of
`e^{-π(x² + 2xy + 2y²) + βπi x²/2}` with mesh `N^{-1/2}` is `N ∫_{ℝ²} = N (1 - iβ)^{-1/2}`.

`ppZ_model_tsum`: `‖∑_n ∑_i ppZModel N β n i - N (1 - iβ)^{-1/2}‖ ≤ K` for all `N ≥ 1`
(`K` depends on `β`).

Route. Inner sum (`ppZ_model_inner_tsum`): by `ppZ_tsum_gauss_shift` with `c = 2/N` it is
`e^{-(π/(2N))(1 - iβ)(n-N/2)²} · √(N/2)(1 + η_n)`, `|η_n| ≤ 2/(e^{πN/2} - 1) ≤ 4/(πN)`.
Outer sum: `ppZ_tsum_gauss_shift` with `c = (1 - iβ)/(2N)`, `t = N/2`:
`c^{-1/2} = √(2N) (1 - iβ)^{-1/2}` (`Complex.mul_cpow_ofReal_nonneg`, `Complex.cpow_neg`),
`Re(1/c) = 2N/(1 + β²)`, error factor `2/(e^{2πN/(1+β²)} - 1) ≤ (1 + β²)/(πN)`; so the main part
is `N (1 - iβ)^{-1/2}` up to `‖(1 - iβ)^{-1/2}‖ (1 + β²)/π`. The cross term is at most
`√(N/2) · (4/(πN)) · ∑_n e^{-(π/(2N))(n-N/2)²} ≤ √(N/2) · (4/(πN)) · (√(2N) + 1) ≤ 4`
(`ppZ_tsum_gauss_real_le` with `c = 1/(2N)`).
Numerically the difference is `≤ 7` for `β = -25` and `≤ 32` for `β = -41`, `N ≤ 3000`
(`model.py`); the bound above gives `(1 + β²)^{3/4}/π + 4`.
-/

noncomputable section

namespace AJConjecture

/-- Splitting a sum of products whose second factor is nearly constant. -/
private theorem norm_tsum_mul_sub_le_modelTsum {E G : ℤ → ℂ} {g A : ℂ} {ε : ℝ}
    (hE : Summable fun n ↦ ‖E n‖) (hG : ∀ n, ‖G n - g‖ ≤ ε) :
    ‖(∑' n, E n * G n) - g * A‖ ≤ ‖g‖ * ‖(∑' n, E n) - A‖ + ε * ∑' n, ‖E n‖ := by
  have hE' : Summable E := hE.of_norm
  have hb : ∀ n, ‖E n * (G n - g)‖ ≤ ‖E n‖ * ε := fun n ↦ by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hG n) (norm_nonneg _)
  have hs : Summable fun n ↦ E n * (G n - g) := Summable.of_norm_bounded (hE.mul_right ε) hb
  have hsn : Summable fun n ↦ ‖E n * (G n - g)‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb (hE.mul_right ε)
  have e : (∑' n, E n * G n) - g * A = g * ((∑' n, E n) - A) + ∑' n, E n * (G n - g) := by
    have e1 : (∑' n, E n * G n) = g * (∑' n, E n) + ∑' n, E n * (G n - g) := by
      rw [← tsum_mul_left, ← (hE'.mul_left g).tsum_add hs]
      congr 1 with n
      ring
    rw [e1]
    ring
  rw [e]
  calc ‖g * ((∑' n, E n) - A) + ∑' n, E n * (G n - g)‖
      ≤ ‖g * ((∑' n, E n) - A)‖ + ‖∑' n, E n * (G n - g)‖ := norm_add_le _ _
    _ ≤ ‖g‖ * ‖(∑' n, E n) - A‖ + ε * ∑' n, ‖E n‖ := by
      rw [norm_mul]
      gcongr
      calc ‖∑' n, E n * (G n - g)‖ ≤ ∑' n, ‖E n * (G n - g)‖ := norm_tsum_le_tsum_norm hsn
        _ ≤ ∑' n, ‖E n‖ * ε := hsn.tsum_le_tsum hb (hE.mul_right ε)
        _ = ε * ∑' n, ‖E n‖ := by rw [tsum_mul_right, mul_comm]

/-- A real shifted Gaussian lattice sum is `1/√c` up to the Poisson error. -/
private theorem abs_tsum_gauss_real_sub_modelTsum {c : ℝ} (hc : 0 < c) (t : ℝ) :
    |(∑' k : ℤ, Real.exp (-Real.pi * c * ((k : ℝ) - t) ^ 2)) - 1 / Real.sqrt c| ≤
      1 / Real.sqrt c * (2 / (Real.exp (Real.pi * (1 / c)) - 1)) := by
  have hc' : 0 < ((c : ℝ) : ℂ).re := by simpa using hc
  have h := ppZ_tsum_gauss_shift hc' t
  have hS : (∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) * c * ((k : ℂ) - t) ^ 2)) =
      ((∑' k : ℤ, Real.exp (-Real.pi * c * ((k : ℝ) - t) ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1 with k
    push_cast
    ring_nf
  have hre : (1 / (c : ℂ)).re = 1 / c := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hval : 1 / (c : ℂ) ^ (1 / 2 : ℂ) = ((1 / Real.sqrt c : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow hc.le]
    norm_num
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  rw [hS, hre, hval, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (a := 1 / Real.sqrt c) (by positivity)] at h
  exact h

/-- The inner Gaussian sum (`c = 2/N`) is `√(N/2)` up to `√(N/2) · 4/(πN)`. -/
private theorem abs_inner_gauss_sub_modelTsum {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    |(∑' k : ℤ, Real.exp (-Real.pi * (2 / N) * ((k : ℝ) - t) ^ 2)) - Real.sqrt (N / 2)| ≤
      Real.sqrt (N / 2) * (4 / (Real.pi * N)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := abs_tsum_gauss_real_sub_modelTsum (c := 2 / N) (by positivity) t
  have e1 : 1 / Real.sqrt (2 / (N : ℝ)) = Real.sqrt (N / 2) := by
    rw [one_div, ← Real.sqrt_inv, inv_div]
  have e2 : Real.pi * (1 / (2 / (N : ℝ))) = Real.pi * N / 2 := by
    field_simp
  rw [e1, e2] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  have hx := Real.add_one_le_exp (Real.pi * N / 2)
  have hpos : 0 < Real.pi * N / 2 := by positivity
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith

/-- `1/c^{1/2}` for `c = (1 - iβ)/(2N)`. -/
private theorem inv_sqrt_scaled_modelTsum (β : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    1 / (((1 / (2 * N) : ℝ) : ℂ) * (1 - β * Complex.I)) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (2 * N) : ℝ) : ℂ) * (1 - β * Complex.I) ^ (-(1 / 2 : ℂ)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : (0 : ℝ) ≤ 1 / (2 * N) := by positivity
  have hmem : (((1 / (2 * N) : ℝ) : ℂ)).arg + (1 - β * Complex.I).arg ∈
      Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr, zero_add]
    exact Complex.arg_mem_Ioc _
  have hs : ((1 / (2 * N) : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((1 / Real.sqrt (2 * N) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hr,
      ← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, one_div]
  have hsq : 0 < Real.sqrt (2 * N) := Real.sqrt_pos.mpr (by positivity)
  have hsq' : ((Real.sqrt (2 * N) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq.ne'
  rw [Complex.mul_cpow hmem, hs, Complex.cpow_neg]
  push_cast
  field_simp

/-- Real shifted Gaussians are summable over `ℤ`. -/
private theorem summable_gauss_real_modelTsum {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Summable fun k : ℤ ↦ Real.exp (-Real.pi * c * ((k : ℝ) - t) ^ 2) := by
  have h := ppZ_summable_gauss_shift (c := (c : ℂ)) (by simpa using hc) t
  rw [← Complex.summable_ofReal]
  convert h using 2 with k
  push_cast
  ring_nf

/-- The outer Gaussian sum (`c = (1 - iβ)/(2N)`, `t = N/2`) is `√(2N) (1 - iβ)^{-1/2}` up to
a relative error `(1 + β²)/(πN)`. -/
private theorem outer_gauss_modelTsum (β : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ‖(∑' n : ℤ, Complex.exp (-(Real.pi / (2 * N) : ℝ) * (1 - β * Complex.I) *
          ((n : ℂ) - N / 2) ^ 2)) -
        ((Real.sqrt (2 * N) : ℝ) : ℂ) * (1 - β * Complex.I) ^ (-(1 / 2 : ℂ))‖ ≤
      Real.sqrt (2 * N) * ‖(1 - β * Complex.I) ^ (-(1 / 2 : ℂ))‖ *
        ((1 + β ^ 2) / (Real.pi * N)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set c : ℂ := ((1 / (2 * N) : ℝ) : ℂ) * (1 - β * Complex.I) with hc
  have hcre : c.re = 1 / (2 * N) := by
    rw [hc, Complex.re_ofReal_mul]
    simp
  have hinv : (1 / c).re = 2 * N / (1 + β ^ 2) := by
    rw [one_div, Complex.inv_re, hcre, hc, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero, Complex.sub_im,
      Complex.one_im, Complex.mul_im, zero_sub, mul_neg, neg_mul, neg_neg, add_zero]
    field_simp
  have P := ppZ_tsum_gauss_shift (c := c) (by rw [hcre]; positivity) ((N : ℝ) / 2)
  have hE : ∀ n : ℤ, Complex.exp (-(Real.pi : ℂ) * c * ((n : ℂ) - ((N / 2 : ℝ) : ℂ)) ^ 2) =
      Complex.exp (-(Real.pi / (2 * N) : ℝ) * (1 - β * Complex.I) *
        ((n : ℂ) - N / 2) ^ 2) := fun n ↦ by
    congr 1
    rw [hc]
    push_cast
    ring
  simp only [hE] at P
  rw [inv_sqrt_scaled_modelTsum β hN, hinv, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)] at P
  refine P.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hx := Real.add_one_le_exp (Real.pi * (2 * N / (1 + β ^ 2)))
  have hpos : 0 < Real.pi * (2 * N / (1 + β ^ 2)) := by positivity
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  have e : (1 + β ^ 2) * (Real.pi * (2 * N / (1 + β ^ 2))) = 2 * (Real.pi * N) := by
    field_simp
  have := mul_le_mul_of_nonneg_left
    (by linarith : Real.pi * (2 * N / (1 + β ^ 2)) ≤
      Real.exp (Real.pi * (2 * N / (1 + β ^ 2))) - 1) (by positivity : 0 ≤ 1 + β ^ 2)
  linarith

/-- The model sum over `ℤ²` is `N (1 - iβ)^{-1/2} + O(1)`. -/
theorem ppZ_model_tsum (β : ℝ) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      ‖(∑' n : ℤ, ∑' i : ℤ, ppZModel N β n i) -
          (N : ℂ) * (1 - β * Complex.I) ^ (-(1 / 2 : ℂ))‖ ≤ K := by
  refine ⟨‖(1 - β * Complex.I) ^ (-(1 / 2 : ℂ))‖ * ((1 + β ^ 2) / Real.pi) + 4, fun N hN ↦ ?_⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set w : ℂ := (1 - β * Complex.I) ^ (-(1 / 2 : ℂ)) with hw
  set E : ℤ → ℂ := fun n ↦ Complex.exp (-(Real.pi / (2 * N) : ℝ) * (1 - β * Complex.I) *
    ((n : ℂ) - N / 2) ^ 2) with hE
  set G : ℤ → ℂ := fun n ↦ ((∑' i : ℤ, Real.exp (-Real.pi * (2 / N) *
    ((i : ℝ) - (N / 4 - ((n : ℝ) - N / 2) / 2)) ^ 2) : ℝ) : ℂ) with hG
  have hS : (∑' n : ℤ, ∑' i : ℤ, ppZModel N β n i) = ∑' n, E n * G n :=
    tsum_congr (ppZ_model_inner_tsum N hN β)
  have hEn : ∀ n, ‖E n‖ = Real.exp (-Real.pi * (1 / (2 * N)) * ((n : ℝ) - N / 2) ^ 2) :=
    fun n ↦ by
    have e : -(((Real.pi / (2 * N) : ℝ)) : ℂ) * (1 - β * Complex.I) * ((n : ℂ) - N / 2) ^ 2 =
        ((-Real.pi * (1 / (2 * N)) * ((n : ℝ) - N / 2) ^ 2 : ℝ) : ℂ) * (1 - β * Complex.I) := by
      push_cast
      ring
    simp only [hE]
    rw [Complex.norm_exp, e, Complex.re_ofReal_mul]
    simp
  have hc : (0 : ℝ) < 1 / (2 * N) := by positivity
  have hEs : Summable fun n ↦ ‖E n‖ := by
    simp only [hEn]
    exact summable_gauss_real_modelTsum hc _
  have hGb : ∀ n, ‖G n - ((Real.sqrt (N / 2) : ℝ) : ℂ)‖ ≤
      Real.sqrt (N / 2) * (4 / (Real.pi * N)) := fun n ↦ by
    simp only [hG]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_inner_gauss_sub_modelTsum hN _
  have key := norm_tsum_mul_sub_le_modelTsum (A := ((Real.sqrt (2 * N) : ℝ) : ℂ) * w) hEs hGb
  have hab : Real.sqrt (N / 2) * Real.sqrt (2 * N) = N := by
    rw [← Real.sqrt_mul (by positivity), show (N : ℝ) / 2 * (2 * N) = N * N by ring,
      Real.sqrt_mul_self hN'.le]
  have hgA : ((Real.sqrt (N / 2) : ℝ) : ℂ) * (((Real.sqrt (2 * N) : ℝ) : ℂ) * w) =
      (N : ℂ) * w := by
    rw [← mul_assoc, ← Complex.ofReal_mul, hab]
    simp
  rw [hS, ← hgA]
  refine key.trans ?_
  have h1 := outer_gauss_modelTsum β hN
  have hb1 : 1 ≤ Real.sqrt (2 * N) := Real.one_le_sqrt.mpr (by linarith)
  have ha0 : 0 ≤ Real.sqrt (N / 2) := Real.sqrt_nonneg _
  have h2 : ∑' n, ‖E n‖ ≤ Real.sqrt (2 * N) + 1 := by
    simp only [hEn]
    refine (ppZ_tsum_gauss_real_le hc _).trans ?_
    rw [one_div (2 * (N : ℝ)), Real.sqrt_inv, one_div, inv_inv]
    gcongr
    exact inv_le_one_of_one_le₀ hb1
  rw [Complex.norm_real, Real.norm_of_nonneg ha0]
  have hπ := Real.pi_gt_three
  have t1 : Real.sqrt (N / 2) * ‖(∑' n, E n) - ((Real.sqrt (2 * N) : ℝ) : ℂ) * w‖ ≤
      ‖w‖ * ((1 + β ^ 2) / Real.pi) := by
    refine (mul_le_mul_of_nonneg_left h1 ha0).trans (le_of_eq ?_)
    rw [← mul_assoc, ← mul_assoc, hab]
    field_simp
    rfl
  have ha : Real.sqrt (N / 2) ≤ N := by
    nlinarith
  have t2 : Real.sqrt (N / 2) * (4 / (Real.pi * N)) * ∑' n, ‖E n‖ ≤ 4 := by
    refine (mul_le_mul_of_nonneg_left h2 (by positivity)).trans ?_
    rw [show Real.sqrt (N / 2) * (4 / (Real.pi * N)) * (Real.sqrt (2 * N) + 1) =
      4 * (Real.sqrt (N / 2) * Real.sqrt (2 * N) + Real.sqrt (N / 2)) / (Real.pi * N) by ring,
      hab, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end AJConjecture
