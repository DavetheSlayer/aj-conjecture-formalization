import Mathlib
import AJPaper.Zheng.PpZNormLocal
import AJPaper.Zheng.PpZPhase
import AJPaper.Zheng.PpZModelWindow

/-!
# The window sum against the Gaussian model (Unit PpZ, node `PpZ_WindowCompare`)

Source: Zheng, (3.31)–(3.33).

`ppZ_windowSum_compare`: for `1/2 < δ < 2/3` there are `K`, `N₁` such that for `N ≥ N₁`

  `‖geoWindowSum N δ β - e^{iβπ(1/4 - N/8)} · S₀ · ppZModelWindowSum N δ β‖ ≤ K N^{3δ-2} · N S₀`.

Route. Take `N₁` with `40 (N^δ + 1) ≤ N` for `N ≥ N₁` (`N^{1-δ} → ∞`). For `(n, i)` in the window,
with `r = N^δ + 1`, `n' = n - N/2`:
* `S_{n,i} = S₀ e^{V(n,i)} e^{θ}`, `|θ| ≤ 5000 r(r² + N)/N² ≤ K₁ N^{3δ-2}`
  (`ppZ_log_normFactor_local`, `Real.exp_log`, `ppZ_normFactor_pos`; `N ≤ r²` because `δ > 1/2`);
  for `N ≥ N₁` large `K₁ N^{3δ-2} ≤ 1`, so `|e^θ - 1| ≤ 2|θ|` (`Real.abs_exp_sub_one_le`);
* `a_n^β = e^{iβπ(1/4 - N/8)} e^{iβπ n'²/(2N)} (1 + ρ)`, `|ρ| ≤ |β|π N^{δ-1}/2 ≤ |β|π N^{3δ-2}`
  (`ppZ_phasePow_approx`, `δ - 1 ≤ 3δ - 2`);
* so the summand differs from `e^{iβπ(1/4-N/8)} S₀ · ppZModel N β n i` by at most
  `S₀ e^{V(n,i)} · K₂ N^{3δ-2}` (`ppZ_model_norm`), and `∑ e^{V} ≤ K₃ N` (`ppZ_modelWindow_abs_le`).
Both sums run over the same index set with the same `if`, so compare termwise
(`Finset.sum_sub_distrib`, `norm_sum_le`).
-/

noncomputable section

namespace AJConjecture

open Classical in
/-- Termwise comparison of two window sums over the triangle. -/
private theorem norm_windowSum_sub_le_windowCompare {N : ℕ} {ρ : ℝ} (c : ℂ) (f g : ℕ → ℕ → ℂ)
    (b : ℕ → ℕ → ℝ) (hb : ∀ n i, 0 ≤ b n i)
    (h : ∀ n i, n < N → i < N - n → GeoInWindow N ρ n i → ‖f n i - c * g n i‖ ≤ b n i) :
    ‖(∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
          if GeoInWindow N ρ n i then f n i else 0) -
        c * ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
          if GeoInWindow N ρ n i then g n i else 0‖ ≤
      ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n), b n i := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn ↦ ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  split_ifs with hw
  · exact h n i (Finset.mem_range.mp hn) (Finset.mem_range.mp hi) hw
  · rw [mul_zero, sub_zero, norm_zero]
    exact hb n i

/-- On the box of radius `r`, `S_{n,i} = S₀ e^{V}(1 + O(Θ))` when the bound `Θ` of
`ppZ_log_normFactor_local` is at most `1`. -/
private theorem normFactor_sub_le_windowCompare {N n i : ℕ} {r Θ : ℝ}
    (hr1 : 1 ≤ r) (hr : 40 * r ≤ N) (hn : |(n : ℝ) - N / 2| ≤ r) (hi : |(i : ℝ) - N / 4| ≤ r)
    (hni : n + i < N) (hΘ : 5000 * r * (r ^ 2 + N) / (N : ℝ) ^ 2 ≤ Θ) (hΘ1 : Θ ≤ 1) :
    0 < geoNormFactor0 N * Real.exp (ppZPot N n i) ∧ 0 < geoNormFactor N n i ∧
      |geoNormFactor N n i - geoNormFactor0 N * Real.exp (ppZPot N n i)| ≤
        2 * Θ * (geoNormFactor0 N * Real.exp (ppZPot N n i)) ∧
      geoNormFactor N n i ≤ 3 * (geoNormFactor0 N * Real.exp (ppZPot N n i)) := by
  have hS := ppZ_normFactor_pos hni
  have hS0 : 0 < geoNormFactor0 N :=
    ppZ_normFactor_pos (N := N) (n := N / 2) (i := N / 4) (by omega)
  have L := ppZ_log_normFactor_local hr1 hr hn hi
  set θ : ℝ := Real.log (geoNormFactor N n i) - Real.log (geoNormFactor0 N) - ppZPot N n i
    with hθ
  have hθ1 : |θ| ≤ Θ := L.trans hΘ
  have hE : Real.exp θ =
      geoNormFactor N n i / geoNormFactor0 N / Real.exp (ppZPot N n i) := by
    rw [hθ, Real.exp_sub, Real.exp_sub, Real.exp_log hS, Real.exp_log hS0]
  set B : ℝ := geoNormFactor0 N * Real.exp (ppZPot N n i) with hB
  have hB0 : 0 < B := mul_pos hS0 (Real.exp_pos _)
  have hSB : geoNormFactor N n i = B * Real.exp θ := by
    rw [hE, hB]
    field_simp
  have hab := Real.abs_exp_sub_one_le (hθ1.trans hΘ1)
  have hΘ0 : 0 ≤ Θ := (abs_nonneg θ).trans hθ1
  have h1 : |geoNormFactor N n i - B| ≤ 2 * Θ * B := by
    rw [hSB, show B * Real.exp θ - B = B * (Real.exp θ - 1) by ring, abs_mul, abs_of_pos hB0,
      mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) hB0.le
  refine ⟨hB0, hS, h1, ?_⟩
  have h2 : Θ * B ≤ 1 * B := mul_le_mul_of_nonneg_right hΘ1 hB0.le
  linarith [le_abs_self (geoNormFactor N n i - B)]

/-- One summand of the window sum against the corresponding summand of the model. -/
private theorem term_sub_le_windowCompare (N n i : ℕ) (β : ℝ) {Θ : ℝ}
    (hS : 0 < geoNormFactor N n i)
    (h1 : |geoNormFactor N n i - geoNormFactor0 N * Real.exp (ppZPot N n i)| ≤
      2 * Θ * (geoNormFactor0 N * Real.exp (ppZPot N n i)))
    (h2 : geoNormFactor N n i ≤ 3 * (geoNormFactor0 N * Real.exp (ppZPot N n i)))
    {φ : ℝ} (hφ : ‖geoPhasePow N n β -
        Complex.exp (((β * Real.pi * (((n : ℝ) - N / 2) ^ 2 / (2 * N) - N / 8 + 1 / 4) : ℝ) : ℂ) *
          Complex.I)‖ ≤ φ) :
    ‖geoPhasePow N n β * (geoNormFactor N n i : ℂ) -
        Complex.exp (((β * Real.pi * (1 / 4 - (N : ℝ) / 8) : ℝ) : ℂ) * Complex.I) *
          (geoNormFactor0 N : ℂ) * ppZModel N β n i‖ ≤
      (2 * Θ + 3 * φ) * (geoNormFactor0 N * Real.exp (ppZPot N n i)) := by
  set Y : ℂ := Complex.exp
    (((β * Real.pi * (((n : ℝ) - N / 2) ^ 2 / (2 * N) - N / 8 + 1 / 4) : ℝ) : ℂ) * Complex.I)
    with hY
  set B : ℝ := geoNormFactor0 N * Real.exp (ppZPot N n i) with hB
  have hYn : ‖Y‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hYe : Y = Complex.exp (((β * Real.pi * (1 / 4 - (N : ℝ) / 8) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (β * Real.pi * Complex.I * ((n : ℂ) - N / 2) ^ 2 / (2 * N)) := by
    rw [hY, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hM : Complex.exp (((β * Real.pi * (1 / 4 - (N : ℝ) / 8) : ℝ) : ℂ) * Complex.I) *
      (geoNormFactor0 N : ℂ) * ppZModel N β n i = Y * (B : ℂ) := by
    rw [ppZModel, Complex.exp_add, hYe, hB]
    push_cast
    ring
  have e : geoPhasePow N n β * (geoNormFactor N n i : ℂ) - Y * (B : ℂ) =
      (geoPhasePow N n β - Y) * (geoNormFactor N n i : ℂ) +
        Y * (((geoNormFactor N n i - B : ℝ)) : ℂ) := by
    push_cast
    ring
  have hφ0 : 0 ≤ φ := (norm_nonneg _).trans hφ
  rw [hM, e]
  calc ‖(geoPhasePow N n β - Y) * (geoNormFactor N n i : ℂ) +
        Y * (((geoNormFactor N n i - B : ℝ)) : ℂ)‖
      ≤ ‖geoPhasePow N n β - Y‖ * geoNormFactor N n i + |geoNormFactor N n i - B| := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul, hYn, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hS]
    _ ≤ φ * (3 * B) + 2 * Θ * B :=
        add_le_add (mul_le_mul hφ h2 hS.le hφ0) h1
    _ = (2 * Θ + 3 * φ) * B := by ring

/-- The parameters of the window: with `r = N^δ + 1`, the box of radius `r` is admissible for
`ppZ_log_normFactor_local` and its error is `O(N^{3δ-2})`. -/
private theorem window_params_windowCompare {N : ℕ} {δ : ℝ} (hδ : 1 / 2 < δ) (hN : 1 ≤ N)
    (h80 : 80 ≤ (N : ℝ) ^ (1 - δ)) :
    40 * ((N : ℝ) ^ δ + 1) ≤ N ∧
      5000 * ((N : ℝ) ^ δ + 1) * (((N : ℝ) ^ δ + 1) ^ 2 + N) / (N : ℝ) ^ 2 ≤
        50000 * (N : ℝ) ^ (3 * δ - 2) ∧
      (N : ℝ) ^ δ / N ≤ (N : ℝ) ^ (3 * δ - 2) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN' : (0 : ℝ) < N := by linarith
  have e3 : (N : ℝ) ^ (3 * δ - 2) = ((N : ℝ) ^ δ) ^ 3 / (N : ℝ) ^ 2 := by
    rw [Real.rpow_sub hN', Real.rpow_two, ← Real.rpow_natCast ((N : ℝ) ^ δ),
      ← Real.rpow_mul hN'.le]
    congr 2
    push_cast
    ring
  have e2 : ((N : ℝ) ^ δ) ^ 2 = (N : ℝ) ^ (δ * 2) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ δ), ← Real.rpow_mul hN'.le]
    norm_num
  have e1 : (N : ℝ) ^ (1 - δ) = N / (N : ℝ) ^ δ := by
    rw [Real.rpow_sub hN', Real.rpow_one]
  have h3 : (N : ℝ) ^ δ / N ≤ (N : ℝ) ^ (3 * δ - 2) := by
    rw [← Real.rpow_sub_one hN'.ne']
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hNx : (N : ℝ) ≤ ((N : ℝ) ^ δ) ^ 2 := by
    rw [e2]
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (δ * 2) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hx1 : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1 (by linarith)
  rw [e1] at h80
  rw [e3] at h3 ⊢
  set x : ℝ := (N : ℝ) ^ δ
  have hx0 : 0 < x := by linarith
  have hxN : 80 * x ≤ N := (le_div_iff₀ hx0).mp h80
  refine ⟨by linarith, ?_, h3⟩
  rw [mul_div_assoc']
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have ha : x + 1 ≤ 2 * x := by linarith
  have hb : (x + 1) ^ 2 + N ≤ 5 * x ^ 2 := by nlinarith
  calc 5000 * (x + 1) * ((x + 1) ^ 2 + N) ≤ 5000 * (2 * x) * (5 * x ^ 2) := by gcongr
    _ = 50000 * x ^ 3 := by ring

/-- The window sum is the model window sum up to a relative error `O(N^{3δ-2})`. -/
theorem ppZ_windowSum_compare (β : ℝ) {δ : ℝ} (hδ : 1 / 2 < δ) (hδ' : δ < 2 / 3) :
    ∃ K : ℝ, ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ‖geoWindowSum N δ β -
          Complex.exp (((β * Real.pi * (1 / 4 - (N : ℝ) / 8) : ℝ) : ℂ) * Complex.I) *
            (geoNormFactor0 N : ℂ) * ppZModelWindowSum N δ β‖ ≤
        K * (N : ℝ) ^ (3 * δ - 2) * (N * geoNormFactor0 N) := by
  obtain ⟨K₃, hK₃⟩ := ppZ_modelWindow_abs_le
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      80 ≤ (N : ℝ) ^ (1 - δ) ∧ 50000 ≤ (N : ℝ) ^ (2 - 3 * δ) ∧ 1 ≤ N :=
    (((tendsto_rpow_atTop (by linarith : 0 < 1 - δ)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 80).and
    ((((tendsto_rpow_atTop (by linarith : 0 < 2 - 3 * δ)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 50000).and
      (Filter.eventually_ge_atTop 1))
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨(100000 + 3 * (|β| * Real.pi)) * K₃, N₁, fun N hN ↦ ?_⟩
  obtain ⟨h80, h5, hN1⟩ := hN₁ N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨p1, p2, p3⟩ := window_params_windowCompare hδ hN1 h80
  have hp : 0 < (N : ℝ) ^ (3 * δ - 2) := Real.rpow_pos_of_pos hN' _
  have hΘ1 : 50000 * (N : ℝ) ^ (3 * δ - 2) ≤ 1 := by
    rw [show 3 * δ - 2 = -(2 - 3 * δ) by ring, Real.rpow_neg hN'.le, ← div_eq_mul_inv,
      div_le_one (Real.rpow_pos_of_pos hN' _)]
    exact h5
  have hS0 : 0 < geoNormFactor0 N :=
    ppZ_normFactor_pos (N := N) (n := N / 2) (i := N / 4) (by omega)
  have hx0 : 0 ≤ (N : ℝ) ^ δ := Real.rpow_nonneg hN'.le _
  set Cc : ℝ := (100000 + 3 * (|β| * Real.pi)) * (N : ℝ) ^ (3 * δ - 2) * geoNormFactor0 N
    with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  rw [geoWindowSum, ppZModelWindowSum]
  refine (norm_windowSum_sub_le_windowCompare
    (Complex.exp (((β * Real.pi * (1 / 4 - (N : ℝ) / 8) : ℝ) : ℂ) * Complex.I) *
      (geoNormFactor0 N : ℂ))
    (fun n i ↦ geoPhasePow N n β * (geoNormFactor N n i : ℂ)) (fun n i ↦ ppZModel N β n i)
    (fun n i ↦ Cc * Real.exp (ppZPot N n i)) (fun n i ↦ by positivity) ?_).trans ?_
  · intro n i _ hi hw
    rw [GeoInWindow] at hw
    have hn' : |(n : ℝ) - N / 2| ≤ (N : ℝ) ^ δ + 1 := by
      linarith [abs_nonneg ((i : ℝ) - N / 4)]
    have hi' : |(i : ℝ) - N / 4| ≤ (N : ℝ) ^ δ + 1 := by
      linarith [abs_nonneg ((n : ℝ) - N / 2)]
    obtain ⟨hB0, hS, q1, q2⟩ := normFactor_sub_le_windowCompare (by linarith) p1 hn' hi'
      (by omega) p2 hΘ1
    have hφ : |β| * Real.pi * |(n : ℝ) - N / 2| / (2 * N) ≤
        |β| * Real.pi * (N : ℝ) ^ (3 * δ - 2) := by
      have h1 : |(n : ℝ) - N / 2| / (2 * N) ≤ (N : ℝ) ^ δ / N := by
        rw [div_le_div_iff₀ (by positivity) hN']
        nlinarith [abs_nonneg ((n : ℝ) - N / 2), abs_nonneg ((i : ℝ) - N / 4)]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (h1.trans p3) (by positivity)
    refine (term_sub_le_windowCompare N n i β hS q1 q2
      ((ppZ_phasePow_approx N n hN1 β).trans hφ)).trans (le_of_eq ?_)
    rw [hCc]
    ring
  · simp only [← Finset.mul_sum]
    refine (mul_le_mul_of_nonneg_left (hK₃ N hN1) hCc0).trans (le_of_eq ?_)
    rw [hCc]
    ring

end AJConjecture
