import Mathlib
import AJPaper.Zheng.PpZRidgeStep

/-!
# Gaussian decay along the ridge (Unit PpZ, node `PpZ_RidgeBound`)

`T_n ≤ C · exp(-(c/N)(n - N/2)²) · S₀` for all `n < N`, with absolute constants.

* `ppZ_ridge_le_left` (`n ≤ ⌊N/2⌋`): `T_n ≤ S₀ · exp(-(π/(2N)) (k² - k))`, `k = ⌊N/2⌋ - n`.
  From `ppZ_ridge_step_ge`: `T_l ≤ T_{l+1} tan φ_{l+1}`, and for `l + 1 ≤ N/2`,
  `tan φ_{l+1} = tan(π/4 - t) ≤ exp(-2t)` with `t = (N/2 - l - 1)π/(2N) ≥ 0`
  (`tan(π/4 - t) = (1 - tan t)/(1 + tan t)`, `log((1-u)/(1+u)) ≤ -2u`, `tan t ≥ t`);
  `∑_{l=n}^{n_c-1} (N/2 - l - 1) ≥ ∑ (n_c - l - 1) = k(k-1)/2`; then `ppZ_ridge_center`.
* `ppZ_ridge_le_right` (`⌊N/2⌋ ≤ n < N`): `T_n ≤ 8 · S₀ · exp(-(π/(2N)) ((k - 3)² - (k - 3)))`
  for `k = n - ⌊N/2⌋ ≥ 3`, and `T_n ≤ 8 · S₀` for `k ≤ 3`. From `ppZ_ridge_step_le`:
  `T_{l+1} ≤ T_l cot φ_{l-2}`, `cot φ_{l-2} = tan(π/4 - t) ≤ exp(-2t)`,
  `t = (l - 2 - N/2)π/(2N) ≥ 0` for `l ≥ N/2 + 2`; the first three steps from `⌊N/2⌋` cost at most
  a factor `2` each (`cot φ_{l-2} ≤ cot(π/4 - π/N·…)`; for small `N` use the trivial bounds).
  The statement below leaves the constant to the prover.
* `ppZ_ridge_le`: the two-sided statement.

Numerically `T_n ≤ 2 exp(-0.2 (n - N/2)²/N) S₀` for all `n < N ≤ 520` (`ridge.py`).
-/

noncomputable section

namespace AJConjecture

/-- `1 - u ≤ (1 + u) e^{-2u}` for `0 ≤ u < 1` (i.e. `log((1-u)/(1+u)) ≤ -2u`). -/
private theorem one_sub_le_one_add_mul_exp_neg_ridgeBound {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    1 - u ≤ (1 + u) * Real.exp (-2 * u) := by
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (x := u)
    (by rw [abs_lt]; constructor <;> linarith)
  have hle := le_hasSum hs 0 (fun k _ ↦ by positivity)
  have h2 : Real.log (1 - u) ≤ Real.log (1 + u) + -2 * u := by
    simp only [Nat.cast_zero, mul_zero, zero_add, div_one, mul_one, pow_one] at hle
    linarith
  have h3 := Real.exp_le_exp.mpr h2
  rwa [Real.exp_add, Real.exp_log (by linarith), Real.exp_log (by linarith)] at h3

/-- `cos(π/4 + t) ≤ cos(π/4 - t) e^{-2t}` for `0 ≤ t < π/4` (i.e. `tan(π/4 - t) ≤ e^{-2t}`). -/
private theorem cos_quarter_add_le_ridgeBound {t : ℝ} (ht : 0 ≤ t) (ht1 : t < Real.pi / 4) :
    Real.cos (Real.pi / 4 + t) ≤ Real.cos (Real.pi / 4 - t) * Real.exp (-2 * t) := by
  have hπ := Real.pi_pos
  have hct : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcs : 0 < Real.cos (Real.pi / 4 + t) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have htt : t ≤ Real.tan t := Real.le_tan ht (by linarith)
  have hq : 0 < Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four]
    positivity
  have hsq : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have e1 : Real.cos (Real.pi / 4 + t) =
      Real.cos (Real.pi / 4) * Real.cos t * (1 - Real.tan t) := by
    rw [Real.cos_add, hsq, Real.tan_eq_sin_div_cos]
    field_simp
  have e2 : Real.cos (Real.pi / 4 - t) =
      Real.cos (Real.pi / 4) * Real.cos t * (1 + Real.tan t) := by
    rw [Real.cos_sub, hsq, Real.tan_eq_sin_div_cos]
    field_simp
  have hu0 : 0 ≤ Real.tan t := ht.trans htt
  have hu1 : Real.tan t < 1 := by
    rw [e1] at hcs
    by_contra hge
    nlinarith [mul_pos hq hct]
  have h1 := one_sub_le_one_add_mul_exp_neg_ridgeBound hu0 hu1
  have h2 : Real.exp (-2 * Real.tan t) ≤ Real.exp (-2 * t) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : 1 - Real.tan t ≤ (1 + Real.tan t) * Real.exp (-2 * t) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
  rw [e1, e2]
  calc Real.cos (Real.pi / 4) * Real.cos t * (1 - Real.tan t)
      ≤ Real.cos (Real.pi / 4) * Real.cos t * ((1 + Real.tan t) * Real.exp (-2 * t)) :=
        mul_le_mul_of_nonneg_left h3 (mul_pos hq hct).le
    _ = _ := by ring

/-- The ridge value is positive for `n < N`. -/
private theorem ridge_pos_ridgeBound {N n : ℕ} (hn : n < N) : 0 < ppZRidge N n := by
  refine ppZ_normFactor_pos ?_
  unfold ppZRidgeIdx
  omega

/-- `S₀ > 0` for `1 ≤ N`. -/
private theorem normFactor0_pos_ridgeBound {N : ℕ} (hN : 1 ≤ N) : 0 < geoNormFactor0 N := by
  rw [← ppZ_ridge_center]
  exact ridge_pos_ridgeBound (by omega)

/-- One step towards the centre from the left: `T_n ≤ T_{n+1} e^{-(π/N)(N/2 - n - 1)}`. -/
private theorem ridge_step_left_ridgeBound {N n : ℕ} (h : 2 * (n + 1) ≤ N) :
    ppZRidge N n ≤ ppZRidge N (n + 1) *
      Real.exp (-(Real.pi / N) * ((N : ℝ) / 2 - n - 1)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hle : 2 * ((n : ℝ) + 1) ≤ N := by exact_mod_cast h
  have hπ := Real.pi_pos
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hge := ppZ_ridge_step_ge (N := N) (n := n) (by omega)
  have hT := (ridge_pos_ridgeBound (N := N) (n := n + 1) (by omega)).le
  set t := ((N : ℝ) / 2 - n - 1) * Real.pi / (2 * N) with ht
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg (by linarith) hπ.le) (by positivity)
  have ht1 : t < Real.pi / 4 := by
    rw [ht, div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hπ (by linarith : (0 : ℝ) < n + 1)]
  have hφ : ((n : ℝ) + 1) * Real.pi / (2 * N) = Real.pi / 4 - t := by
    rw [ht]
    field_simp
    ring
  have key := cos_quarter_add_le_ridgeBound ht0 ht1
  have es : Real.sin (Real.pi / 4 - t) = Real.cos (Real.pi / 4 + t) := by
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    ring
  have hc : 0 < Real.cos (Real.pi / 4 - t) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  rw [hφ, es] at hge
  have ee : -(Real.pi / N) * ((N : ℝ) / 2 - n - 1) = -2 * t := by
    rw [ht]
    field_simp
  rw [ee]
  refine le_of_mul_le_mul_right ?_ hc
  calc ppZRidge N n * Real.cos (Real.pi / 4 - t)
      ≤ ppZRidge N (n + 1) * Real.cos (Real.pi / 4 + t) := hge
    _ ≤ ppZRidge N (n + 1) * (Real.cos (Real.pi / 4 - t) * Real.exp (-2 * t)) :=
        mul_le_mul_of_nonneg_left key hT
    _ = _ := by ring

/-- One step away from the centre on the right, for `N/2 + 2 ≤ l`:
`T_{l+1} ≤ T_l e^{-(π/N)(l - 2 - N/2)}`. -/
private theorem ridge_step_right_ridgeBound {N l : ℕ} (h : l + 1 < N) (h2 : N + 4 ≤ 2 * l) :
    ppZRidge N (l + 1) ≤ ppZRidge N l *
      Real.exp (-(Real.pi / N) * ((l : ℝ) - 2 - (N : ℝ) / 2)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlN : (l : ℝ) + 1 < N := by exact_mod_cast h
  have hl2 : (N : ℝ) + 4 ≤ 2 * l := by exact_mod_cast h2
  have hπ := Real.pi_pos
  have hle := ppZ_ridge_step_le (N := N) (n := l) (by omega) h
  have hT := (ridge_pos_ridgeBound (N := N) (n := l) (by omega)).le
  set t := ((l : ℝ) - 2 - (N : ℝ) / 2) * Real.pi / (2 * N) with ht
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg (by linarith) hπ.le) (by positivity)
  have ht1 : t < Real.pi / 4 := by
    rw [ht, div_lt_iff₀ (by positivity)]
    nlinarith
  have hφ : ((l : ℝ) - 2) * Real.pi / (2 * N) = Real.pi / 4 + t := by
    rw [ht]
    field_simp
    ring
  have key := cos_quarter_add_le_ridgeBound ht0 ht1
  have es : Real.cos (Real.pi / 4 - t) = Real.sin (Real.pi / 4 + t) := by
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    ring
  have hs : 0 < Real.sin (Real.pi / 4 + t) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [hφ] at hle
  rw [es] at key
  have ee : -(Real.pi / N) * ((l : ℝ) - 2 - (N : ℝ) / 2) = -2 * t := by
    rw [ht]
    field_simp
  rw [ee]
  refine le_of_mul_le_mul_right ?_ hs
  calc ppZRidge N (l + 1) * Real.sin (Real.pi / 4 + t)
      ≤ ppZRidge N l * Real.cos (Real.pi / 4 + t) := hle
    _ ≤ ppZRidge N l * (Real.sin (Real.pi / 4 + t) * Real.exp (-2 * t)) :=
        mul_le_mul_of_nonneg_left key hT
    _ = _ := by ring

/-- A crude step right of the centre: `T_{l+1} ≤ 2 T_l` for `N ≤ 2l + 1`. -/
private theorem ridge_step_two_ridgeBound {N l : ℕ} (h : l + 1 < N) (h2 : N ≤ 2 * l + 1) :
    ppZRidge N (l + 1) ≤ 2 * ppZRidge N l := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlN : (l : ℝ) + 2 ≤ N := by exact_mod_cast (by omega : l + 2 ≤ N)
  have hl2 : (N : ℝ) ≤ 2 * l + 1 := by exact_mod_cast h2
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hπ := Real.pi_pos
  have hT := (ridge_pos_ridgeBound (N := N) (n := l) (by omega)).le
  set x := Real.pi / (2 * N) with hx
  have hx0 : 0 < x := by positivity
  have hxN : x * (2 * N) = Real.pi := by
    rw [hx]
    field_simp
  have hφ1 : ((l : ℝ) + 1) * Real.pi / (2 * N) = (l + 1) * x := by
    rw [hx]
    ring
  have hφ0 : (l : ℝ) * Real.pi / (2 * N) = (l + 1) * x - x := by
    rw [hx]
    ring
  have hb1 : ((l : ℝ) + 1) * x + x ≤ Real.pi / 2 := by nlinarith
  have hb2 : Real.pi / 2 ≤ ((l : ℝ) + 1) * x + ((l : ℝ) + 1) * x - x := by nlinarith
  have hb3 : 0 < ((l : ℝ) + 1) * x := by positivity
  have hs : 0 < Real.sin (((l : ℝ) + 1) * x) :=
    Real.sin_pos_of_pos_of_lt_pi hb3 (by linarith)
  have hc : 0 < Real.cos (((l : ℝ) + 1) * x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcs : Real.cos (((l : ℝ) + 1) * x) ≤ Real.sin (((l : ℝ) + 1) * x) := by
    rw [← Real.sin_pi_div_two_sub]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  rcases Nat.mod_two_eq_zero_or_one (N - l) with hp | hp
  · have he := ppZ_ridge_succ_even h hp
    rw [hφ1, hφ0] at he
    have h1 : Real.cos (((l : ℝ) + 1) * x - x) ≤ Real.sin (((l : ℝ) + 1) * x) := by
      rw [← Real.sin_pi_div_two_sub]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    have h2 : Real.cos (((l : ℝ) + 1) * x - x) ≤ 2 * Real.cos (((l : ℝ) + 1) * x) := by
      have hsx : Real.sin x ≤ Real.cos (((l : ℝ) + 1) * x) := by
        rw [← Real.sin_pi_div_two_sub]
        exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
      have hsx0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0.le (by linarith)
      rw [Real.cos_sub]
      nlinarith [Real.cos_le_one x, Real.sin_le_one (((l : ℝ) + 1) * x)]
    have h0 : 0 ≤ Real.cos (((l : ℝ) + 1) * x - x) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    refine le_of_mul_le_mul_right ?_ (mul_pos hs hc)
    rw [he]
    have h3 : Real.cos (((l : ℝ) + 1) * x - x) ^ 2 ≤
        Real.sin (((l : ℝ) + 1) * x) * (2 * Real.cos (((l : ℝ) + 1) * x)) := by
      rw [sq]
      exact mul_le_mul h1 h2 h0 hs.le
    calc ppZRidge N l * Real.cos (((l : ℝ) + 1) * x - x) ^ 2
        ≤ ppZRidge N l * (Real.sin (((l : ℝ) + 1) * x) *
            (2 * Real.cos (((l : ℝ) + 1) * x))) := mul_le_mul_of_nonneg_left h3 hT
      _ = _ := by ring
  · have ho := ppZ_ridge_succ_odd h hp
    rw [hφ1] at ho
    refine le_of_mul_le_mul_right ?_ hs
    rw [ho]
    nlinarith [mul_le_mul_of_nonneg_left hcs hT, mul_nonneg hT hs.le]

/-- Left of the centre, in terms of `k = ⌊N/2⌋ - n`. -/
private theorem ridge_le_left_aux_ridgeBound {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    ∀ n : ℕ, n + k = N / 2 → ppZRidge N n ≤ geoNormFactor0 N *
      Real.exp (-(Real.pi / (2 * N)) * ((k : ℝ) ^ 2 - k)) := by
  induction k with
  | zero =>
    intro n hn
    rw [add_zero] at hn
    rw [hn, ppZ_ridge_center]
    simp
  | succ k ih =>
    intro n hn
    have ih' := ih (n + 1) (by omega)
    have hstep := ridge_step_left_ridgeBound (N := N) (n := n) (by omega)
    have hS0 := (normFactor0_pos_ridgeBound hN).le
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    refine hstep.trans ?_
    refine (mul_le_mul_of_nonneg_right ih' (Real.exp_pos _).le).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hS0
    have hnk : (n : ℝ) + k + 1 ≤ (N : ℝ) / 2 := by
      have h2 : 2 * ((n : ℝ) + k + 1) ≤ N := by exact_mod_cast (by omega : 2 * (n + k + 1) ≤ N)
      linarith
    have e : -(Real.pi / (2 * N)) * ((k : ℝ) ^ 2 - k) +
        -(Real.pi / N) * ((N : ℝ) / 2 - n - 1) -
        -(Real.pi / (2 * N)) * (((k + 1 : ℕ) : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ)) =
        -(Real.pi / N * ((N : ℝ) / 2 - n - 1 - k)) := by
      push_cast
      ring
    have h3 : 0 ≤ Real.pi / N * ((N : ℝ) / 2 - n - 1 - k) :=
      mul_nonneg (by positivity) (by linarith)
    linarith

/-- Left of the centre: `T_n ≤ S₀ · exp(-(π/(2N)) (k² - k))`, `k = ⌊N/2⌋ - n`. -/
theorem ppZ_ridge_le_left {N n : ℕ} (hN : 1 ≤ N) (hn : n ≤ N / 2) :
    ppZRidge N n ≤ geoNormFactor0 N *
      Real.exp (-(Real.pi / (2 * N)) *
        ((((N / 2 : ℕ) : ℝ) - n) ^ 2 - (((N / 2 : ℕ) : ℝ) - n))) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have e : ((N / 2 : ℕ) : ℝ) - n = k := by
    rw [hk]
    push_cast
    ring
  rw [e]
  exact ridge_le_left_aux_ridgeBound hN k n hk.symm

/-- Right of the centre, crude bound: `T_{⌊N/2⌋+d} ≤ 2^d S₀`. -/
private theorem ridge_le_two_pow_ridgeBound {N : ℕ} (d : ℕ) (h : N / 2 + d < N) :
    ppZRidge N (N / 2 + d) ≤ 2 ^ d * geoNormFactor0 N := by
  induction d with
  | zero => simp [ppZ_ridge_center]
  | succ d ih =>
    have ih' := ih (by omega)
    have hstep := ridge_step_two_ridgeBound (N := N) (l := N / 2 + d) (by omega) (by omega)
    rw [← add_assoc, pow_succ]
    linarith

/-- Right of the centre, Gaussian bound from `⌊N/2⌋ + 3` on. -/
private theorem ridge_le_right_aux_ridgeBound {N : ℕ} (hN : 1 ≤ N) (j : ℕ)
    (h : N / 2 + 3 + j < N) :
    ppZRidge N (N / 2 + 3 + j) ≤ 8 * geoNormFactor0 N *
      Real.exp (-(Real.pi / (2 * N)) * ((j : ℝ) ^ 2 - j)) := by
  induction j with
  | zero =>
    have h3 := ridge_le_two_pow_ridgeBound (N := N) 3 h
    norm_num at h3 ⊢
    exact h3
  | succ j ih =>
    have ih' := ih (by omega)
    have hstep := ridge_step_right_ridgeBound (N := N) (l := N / 2 + 3 + j) (by omega) (by omega)
    have hS0 := (normFactor0_pos_ridgeBound hN).le
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    rw [← add_assoc]
    refine hstep.trans ?_
    refine (mul_le_mul_of_nonneg_right ih' (Real.exp_pos _).le).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have hnc : (N : ℝ) / 2 ≤ ((N / 2 : ℕ) : ℝ) + 1 / 2 := by
      have h2 : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (by omega : N ≤ 2 * (N / 2) + 1)
      linarith
    have e : -(Real.pi / (2 * N)) * ((j : ℝ) ^ 2 - j) +
        -(Real.pi / N) * (((N / 2 + 3 + j : ℕ) : ℝ) - 2 - (N : ℝ) / 2) -
        -(Real.pi / (2 * N)) * (((j + 1 : ℕ) : ℝ) ^ 2 - ((j + 1 : ℕ) : ℝ)) =
        -(Real.pi / N * (((N / 2 : ℕ) : ℝ) + 1 - (N : ℝ) / 2)) := by
      push_cast
      ring
    have h3 : 0 ≤ Real.pi / N * (((N / 2 : ℕ) : ℝ) + 1 - (N : ℝ) / 2) :=
      mul_nonneg (by positivity) (by linarith)
    linarith

/-- Comparison of the two Gaussian exponents:
`e^{-(π/2N)(j² - j)} ≤ e^{10} e^{-(1/2N) x²}` when `x² ≤ (j + 3)²`. -/
private theorem exp_compare_ridgeBound {N : ℕ} (hN : 1 ≤ N) {j x : ℝ} (hj : 0 ≤ j ^ 2 - j)
    (hx : x ^ 2 ≤ (j + 3) ^ 2) :
    Real.exp (-(Real.pi / (2 * N)) * (j ^ 2 - j)) ≤
      Real.exp 10 * Real.exp (-((1 / 2 : ℝ) / N) * x ^ 2) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hnum : x ^ 2 - Real.pi * (j ^ 2 - j) ≤ 20 * N := by
    nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) hj, sq_nonneg (j - 9 / 4)]
  have hdiv : (x ^ 2 - Real.pi * (j ^ 2 - j)) / (2 * N) ≤ 10 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have e : 10 + -((1 / 2 : ℝ) / N) * x ^ 2 - -(Real.pi / (2 * N)) * (j ^ 2 - j) =
      10 - (x ^ 2 - Real.pi * (j ^ 2 - j)) / (2 * N) := by
    ring
  linarith

/-- `0 ≤ j² - j` for a natural number `j`. -/
private theorem natCast_sq_sub_nonneg_ridgeBound (j : ℕ) : (0 : ℝ) ≤ (j : ℝ) ^ 2 - j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith

/-- Right of the centre with explicit constants `c = 1/2`, `C = 8 e^{10}`. -/
private theorem ridge_le_right_explicit_ridgeBound {N n : ℕ} (hN : 1 ≤ N) (hn : N / 2 ≤ n)
    (hnN : n < N) :
    ppZRidge N n ≤ 8 * Real.exp 10 * Real.exp (-((1 / 2 : ℝ) / N) * ((n : ℝ) - N / 2) ^ 2) *
      geoNormFactor0 N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hS0 := (normFactor0_pos_ridgeBound hN).le
  have hnc1 : (N : ℝ) / 2 ≤ ((N / 2 : ℕ) : ℝ) + 1 / 2 := by
    have h2 : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (by omega : N ≤ 2 * (N / 2) + 1)
    linarith
  have hnc2 : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
    have h2 : 2 * ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : 2 * (N / 2) ≤ N)
    linarith
  rcases le_or_gt d 3 with hd | hd
  · have h1 := ridge_le_two_pow_ridgeBound (N := N) d hnN
    have h2 : (2 : ℝ) ^ d ≤ 8 :=
      (pow_le_pow_right₀ (by norm_num) hd).trans (by norm_num)
    have hdr : (d : ℝ) ≤ 3 := by exact_mod_cast hd
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h3 := exp_compare_ridgeBound hN (j := 0) (x := ((N / 2 + d : ℕ) : ℝ) - N / 2)
      (by norm_num) (by push_cast; nlinarith)
    rw [show -(Real.pi / (2 * N)) * ((0 : ℝ) ^ 2 - 0) = 0 by ring, Real.exp_zero] at h3
    calc ppZRidge N (N / 2 + d) ≤ 2 ^ d * geoNormFactor0 N := h1
      _ ≤ 8 * geoNormFactor0 N := mul_le_mul_of_nonneg_right h2 hS0
      _ = 8 * 1 * geoNormFactor0 N := by ring
      _ ≤ 8 * (Real.exp 10 * Real.exp (-((1 / 2 : ℝ) / N) *
            (((N / 2 + d : ℕ) : ℝ) - N / 2) ^ 2)) * geoNormFactor0 N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by norm_num)) hS0
      _ = _ := by ring
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hd.le
    have h1 := ridge_le_right_aux_ridgeBound hN j (by omega)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h3 := exp_compare_ridgeBound hN (j := (j : ℝ))
      (x := ((N / 2 + (3 + j) : ℕ) : ℝ) - N / 2) (natCast_sq_sub_nonneg_ridgeBound j)
      (by push_cast; nlinarith)
    rw [← add_assoc] at h3 ⊢
    calc ppZRidge N (N / 2 + 3 + j)
        ≤ 8 * geoNormFactor0 N * Real.exp (-(Real.pi / (2 * N)) * ((j : ℝ) ^ 2 - j)) := h1
      _ ≤ 8 * geoNormFactor0 N * (Real.exp 10 * Real.exp (-((1 / 2 : ℝ) / N) *
            (((N / 2 + 3 + j : ℕ) : ℝ) - N / 2) ^ 2)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring

/-- Right of the centre: Gaussian decay with some absolute constants. -/
theorem ppZ_ridge_le_right :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N n : ℕ, 1 ≤ N → N / 2 ≤ n → n < N →
      ppZRidge N n ≤ C * Real.exp (-(c / N) * ((n : ℝ) - N / 2) ^ 2) * geoNormFactor0 N :=
  ⟨1 / 2, by norm_num, 8 * Real.exp 10, fun _ _ hN hn hnN ↦
    ridge_le_right_explicit_ridgeBound hN hn hnN⟩

/-- Gaussian decay of the ridge values around `n = N/2`. -/
theorem ppZ_ridge_le :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N n : ℕ, 1 ≤ N → n < N →
      ppZRidge N n ≤ C * Real.exp (-(c / N) * ((n : ℝ) - N / 2) ^ 2) * geoNormFactor0 N := by
  refine ⟨1 / 2, by norm_num, 8 * Real.exp 10, fun N n hN hnN ↦ ?_⟩
  rcases le_total (N / 2) n with hn | hn
  · exact ridge_le_right_explicit_ridgeBound hN hn hnN
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
    have h1 := ridge_le_left_aux_ridgeBound hN k n hk.symm
    have hS0 := (normFactor0_pos_ridgeBound hN).le
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hnc1 : (N : ℝ) / 2 ≤ (n : ℝ) + k + 1 / 2 := by
      have h2 : (N : ℝ) ≤ 2 * ((n : ℝ) + k) + 1 := by
        exact_mod_cast (by omega : N ≤ 2 * (n + k) + 1)
      linarith
    have hnc2 : (n : ℝ) + k ≤ (N : ℝ) / 2 := by
      have h2 : 2 * ((n : ℝ) + k) ≤ N := by exact_mod_cast (by omega : 2 * (n + k) ≤ N)
      linarith
    have h3 := exp_compare_ridgeBound hN (j := (k : ℝ)) (x := (n : ℝ) - N / 2)
      (natCast_sq_sub_nonneg_ridgeBound k) (by nlinarith)
    calc ppZRidge N n
        ≤ geoNormFactor0 N * Real.exp (-(Real.pi / (2 * N)) * ((k : ℝ) ^ 2 - k)) := h1
      _ ≤ geoNormFactor0 N * (Real.exp 10 * Real.exp (-((1 / 2 : ℝ) / N) *
            ((n : ℝ) - N / 2) ^ 2)) := mul_le_mul_of_nonneg_left h3 hS0
      _ = 1 * (Real.exp 10 * Real.exp (-((1 / 2 : ℝ) / N) * ((n : ℝ) - N / 2) ^ 2) *
            geoNormFactor0 N) := by ring
      _ ≤ 8 * (Real.exp 10 * Real.exp (-((1 / 2 : ℝ) / N) * ((n : ℝ) - N / 2) ^ 2) *
            geoNormFactor0 N) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = _ := by ring

end AJConjecture
