import Mathlib
import AJPaper.Zheng.PpZNormSteps

/-!
# The ridge of `S_{n,i}` and the Gaussian bound in `i` (Unit PpZ, node `PpZ_RidgeI`)

Source: Zheng, Lemma 3.2 (the function `f(x, y) = -2Λ(x+y) + 2Λ(y) + Λ(x)` is concave in `y`,
with maximum on the line `x + 2y = π`); here in exact discrete form.

For fixed `n` the ratio `S_{n,i+1}/S_{n,i} = (sin((i+n+1)π/N)/sin((i+1)π/N))²` is `≥ 1` exactly
when `2(i+1) ≤ N - n`. So `i ↦ S_{n,i}` is maximal at the ridge index `i*(n) = ⌊(N-n)/2⌋`
(`ppZRidgeIdx`), with value `T_n` (`ppZRidge`). Quantitatively, with `θ = nπ/N`,
`t = (i + 1 - (N-n)/2)π/N`: the ratio is `(cos(θ/2 + t)/cos(θ/2 - t))² = ((1-u)/(1+u))²`,
`u = tan(θ/2) tan t`, and `log((1-u)/(1+u)) ≤ -2u ≤ -2 tan(θ/2) t` for `0 ≤ t`
(`≥ 2 tan(θ/2)|t|` for `t ≤ 0`).

* `ppZ_normFactor_step_right_le`, `ppZ_normFactor_step_right_ge`: the two one-step bounds.
* `ppZ_normFactor_le_ridge`: `S_{n,i} ≤ T_n · exp(-(2π/N) tan(nπ/2N) (D² - D))`, `D = |i - i*(n)|`.

Route for the last: sum the step bounds from `i*` to `i` (for `i ≥ i*`:
`∑_{l=i*}^{i-1} (l + 1 - (N-n)/2) ≥ ∑ (l - i* + 1/2) = D²/2`; for `i < i*`:
`∑_{l=i}^{i*-1} ((N-n)/2 - l - 1) ≥ ∑ (i* - l - 1) = D(D-1)/2`). Checked numerically for all
`n + i < N`, `N ≤ 59` and `N ∈ {101, 128, 255, 500}` (`scaf.py`).
-/

noncomputable section

namespace AJConjecture

/-- The ridge index `i*(n) = ⌊(N - n)/2⌋`: a maximiser of `i ↦ S_{n,i}`. -/
def ppZRidgeIdx (N n : ℕ) : ℕ := (N - n) / 2

/-- The ridge value `T_n = S_{n, i*(n)}`. -/
def ppZRidge (N n : ℕ) : ℝ := geoNormFactor N n (ppZRidgeIdx N n)

/-- `1 - u ≤ (1 + u) e^{-2u}` for `0 ≤ u < 1` (i.e. `log((1-u)/(1+u)) ≤ -2u`). -/
private theorem one_sub_le_one_add_mul_exp_neg_ridgeI {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    1 - u ≤ (1 + u) * Real.exp (-2 * u) := by
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (x := u)
    (by rw [abs_lt]; constructor <;> linarith)
  have hle := le_hasSum hs 0 (fun k _ ↦ by positivity)
  have h2 : Real.log (1 - u) ≤ Real.log (1 + u) + -2 * u := by
    simp only [Nat.cast_zero, mul_zero, zero_add, div_one, mul_one, pow_one] at hle
    linarith
  have h3 := Real.exp_le_exp.mpr h2
  rwa [Real.exp_add, Real.exp_log (by linarith), Real.exp_log (by linarith)] at h3

/-- `cos(α + t) ≤ cos(α - t) e^{-2 tan α · t}` for `0 ≤ α`, `0 ≤ t`, `α + t < π/2`. -/
private theorem cos_add_le_cos_sub_mul_exp_ridgeI {α t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t)
    (hsum : α + t < Real.pi / 2) :
    Real.cos (α + t) ≤ Real.cos (α - t) * Real.exp (-2 * Real.tan α * t) := by
  have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hct : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcs : 0 < Real.cos (α + t) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have htα : 0 ≤ Real.tan α := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hα (by linarith)
  have htt : t ≤ Real.tan t := Real.le_tan ht (by linarith)
  set u := Real.tan α * Real.tan t with hu
  have hu0 : 0 ≤ u := mul_nonneg htα (ht.trans htt)
  have e1 : Real.cos (α + t) = Real.cos α * Real.cos t * (1 - u) := by
    rw [Real.cos_add, hu, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
    field_simp
  have e2 : Real.cos (α - t) = Real.cos α * Real.cos t * (1 + u) := by
    rw [Real.cos_sub, hu, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
    field_simp
  have hu1 : u < 1 := by
    rw [e1] at hcs
    by_contra hge
    nlinarith [mul_pos hcα hct]
  have h1 := one_sub_le_one_add_mul_exp_neg_ridgeI hu0 hu1
  have h2 : Real.exp (-2 * u) ≤ Real.exp (-2 * Real.tan α * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [e1, e2]
  have h3 : (1 - u) ≤ (1 + u) * Real.exp (-2 * Real.tan α * t) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
  calc Real.cos α * Real.cos t * (1 - u)
      ≤ Real.cos α * Real.cos t * ((1 + u) * Real.exp (-2 * Real.tan α * t)) :=
        mul_le_mul_of_nonneg_left h3 (mul_pos hcα hct).le
    _ = _ := by ring

/-- Squared form: `cos²(α + t) ≤ cos²(α - t) e^{-4 tan α · t}`, and `cos(α - t) > 0`. -/
private theorem cos_sq_add_le_cos_sq_sub_mul_exp_ridgeI {α t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t)
    (hsum : α + t < Real.pi / 2) :
    0 < Real.cos (α - t) ∧
      Real.cos (α + t) ^ 2 ≤ Real.cos (α - t) ^ 2 * Real.exp (-4 * Real.tan α * t) := by
  have hcs : 0 < Real.cos (α + t) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcd : 0 < Real.cos (α - t) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  refine ⟨hcd, ?_⟩
  have h := cos_add_le_cos_sub_mul_exp_ridgeI hα ht hsum
  have e : Real.exp (-4 * Real.tan α * t) = Real.exp (-2 * Real.tan α * t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e, ← mul_pow]
  exact pow_le_pow_left₀ hcs.le h 2

/-- `2 i*(n) + n ≤ N ≤ 2 i*(n) + 1 + n` for `n ≤ N`. -/
private theorem ridgeIdx_bounds_ridgeI {N n : ℕ} (hn : n ≤ N) :
    2 * ppZRidgeIdx N n + n ≤ N ∧ N ≤ 2 * ppZRidgeIdx N n + 1 + n := by
  unfold ppZRidgeIdx
  omega

/-- `tan(nπ/(2N)) ≥ 0` for `n ≤ N`. -/
private theorem tan_half_angle_nonneg_ridgeI {N n : ℕ} (hn : n ≤ N) :
    0 ≤ Real.tan (n * Real.pi / (2 * N)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnr : (n : ℝ) ≤ N := by exact_mod_cast hn
  refine Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by positivity) ?_
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

/-- Past the ridge (`N - n ≤ 2(i+1)`) one step in `i` decreases `S` at a Gaussian rate. -/
theorem ppZ_normFactor_step_right_le {N n i : ℕ} (h : n + i + 1 < N)
    (hi : (N : ℝ) - n ≤ 2 * ((i : ℝ) + 1)) :
    geoNormFactor N n (i + 1) ≤ geoNormFactor N n i *
      Real.exp (-(4 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) *
        ((i : ℝ) + 1 - ((N : ℝ) - n) / 2)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlt : (n : ℝ) + i + 1 < N := by exact_mod_cast h
  have hπ := Real.pi_pos
  set α := (n : ℝ) * Real.pi / (2 * N) with hα
  set t := ((i : ℝ) + 1 - ((N : ℝ) - n) / 2) * Real.pi / N with ht
  have hα0 : 0 ≤ α := by positivity
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg (by linarith) hπ.le) hN.le
  have hsum : α + t < Real.pi / 2 := by
    have e : α + t = ((n : ℝ) + i + 1) * Real.pi / N - Real.pi / 2 := by
      rw [hα, ht]
      field_simp
      ring
    have h2 : ((n : ℝ) + i + 1) * Real.pi / N < Real.pi := by
      rw [div_lt_iff₀ hN]
      nlinarith
    linarith
  have e1 : Real.sin (((i : ℝ) + 1) * Real.pi / N) = Real.cos (α - t) := by
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    rw [hα, ht]
    field_simp
    ring
  have e2 : Real.sin (((i : ℝ) + n + 1) * Real.pi / N) = Real.cos (α + t) := by
    rw [← Real.sin_pi_div_two_sub, ← Real.sin_pi_sub]
    congr 1
    rw [hα, ht]
    field_simp
    ring
  obtain ⟨hpos, key⟩ := cos_sq_add_le_cos_sq_sub_mul_exp_ridgeI hα0 ht0 hsum
  have hS := ppZ_normFactor_succ_right N n i
  rw [e1, e2] at hS
  have hSpos : 0 ≤ geoNormFactor N n i := (ppZ_normFactor_pos (by omega)).le
  have ee : -(4 * Real.pi / N) * Real.tan α * ((i : ℝ) + 1 - ((N : ℝ) - n) / 2) =
      -4 * Real.tan α * t := by
    rw [ht]
    field_simp
  rw [ee]
  refine le_of_mul_le_mul_right ?_ (pow_pos hpos 2)
  rw [hS, mul_assoc, mul_comm (Real.exp _)]
  exact mul_le_mul_of_nonneg_left key hSpos

/-- Before the ridge (`2(i+1) ≤ N - n`) one step in `i` increases `S` at a Gaussian rate. -/
theorem ppZ_normFactor_step_right_ge {N n i : ℕ} (h : n + i + 1 < N)
    (hi : 2 * ((i : ℝ) + 1) ≤ (N : ℝ) - n) :
    geoNormFactor N n i *
        Real.exp ((4 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) *
          (((N : ℝ) - n) / 2 - i - 1)) ≤
      geoNormFactor N n (i + 1) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlt : (n : ℝ) + i + 1 < N := by exact_mod_cast h
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hπ := Real.pi_pos
  set α := (n : ℝ) * Real.pi / (2 * N) with hα
  set t := (((N : ℝ) - n) / 2 - i - 1) * Real.pi / N with ht
  have hα0 : 0 ≤ α := by positivity
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg (by linarith) hπ.le) hN.le
  have hsum : α + t < Real.pi / 2 := by
    have e : α + t = Real.pi / 2 - ((i : ℝ) + 1) * Real.pi / N := by
      rw [hα, ht]
      field_simp
      ring
    have h2 : 0 < ((i : ℝ) + 1) * Real.pi / N := by positivity
    linarith
  have e1 : Real.sin (((i : ℝ) + 1) * Real.pi / N) = Real.cos (α + t) := by
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    rw [hα, ht]
    field_simp
    ring
  have e2 : Real.sin (((i : ℝ) + n + 1) * Real.pi / N) = Real.cos (α - t) := by
    rw [← Real.sin_pi_div_two_sub, ← Real.sin_pi_sub]
    congr 1
    rw [hα, ht]
    field_simp
    ring
  obtain ⟨-, key⟩ := cos_sq_add_le_cos_sq_sub_mul_exp_ridgeI hα0 ht0 hsum
  have hcs : 0 < Real.cos (α + t) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hS := ppZ_normFactor_succ_right N n i
  rw [e1, e2] at hS
  have hSpos : 0 ≤ geoNormFactor N n i := (ppZ_normFactor_pos (by omega)).le
  have ee : (4 * Real.pi / N) * Real.tan α * (((N : ℝ) - n) / 2 - i - 1) =
      -(-4 * Real.tan α * t) := by
    rw [ht]
    field_simp
  rw [ee, Real.exp_neg]
  refine le_of_mul_le_mul_right ?_ (pow_pos hcs 2)
  rw [hS, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hSpos
  rw [inv_mul_le_iff₀ (Real.exp_pos _), mul_comm]
  exact key

/-- The ridge value is positive for `n < N`. -/
private theorem ridge_pos_ridgeI {N n : ℕ} (hn : n < N) : 0 < ppZRidge N n := by
  have hb := ridgeIdx_bounds_ridgeI hn.le
  exact ppZ_normFactor_pos (by omega)

/-- The Gaussian bound to the right of the ridge, `i = i*(n) + D`. -/
private theorem normFactor_le_ridge_right_ridgeI {N n : ℕ} (D : ℕ)
    (h : n + (ppZRidgeIdx N n + D) < N) :
    geoNormFactor N n (ppZRidgeIdx N n + D) ≤ ppZRidge N n *
      Real.exp (-(2 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) * ((D : ℝ) ^ 2 - D)) := by
  induction D with
  | zero => simp [ppZRidge]
  | succ D ih =>
    have ih' := ih (by omega)
    have hN : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hb := ridgeIdx_bounds_ridgeI (by omega : n ≤ N)
    have hb2 : (N : ℝ) ≤ 2 * (ppZRidgeIdx N n : ℝ) + 1 + n := by exact_mod_cast hb.2
    have htan := tan_half_angle_nonneg_ridgeI (by omega : n ≤ N)
    have hT := (ridge_pos_ridgeI (by omega : n < N)).le
    have hstep := ppZ_normFactor_step_right_le (N := N) (n := n) (i := ppZRidgeIdx N n + D)
      (by omega) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) D])
    rw [← add_assoc]
    refine hstep.trans ?_
    refine (mul_le_mul_of_nonneg_right ih' (Real.exp_pos _).le).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hT
    have hX : 0 ≤ Real.pi / N * Real.tan (n * Real.pi / (2 * N)) :=
      mul_nonneg (by positivity) htan
    have e : -(2 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) * ((D : ℝ) ^ 2 - D) +
        -(4 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) *
          (((ppZRidgeIdx N n + D : ℕ) : ℝ) + 1 - ((N : ℝ) - n) / 2) -
        -(2 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) *
          (((D + 1 : ℕ) : ℝ) ^ 2 - ((D + 1 : ℕ) : ℝ)) =
        -(2 * (Real.pi / N * Real.tan (n * Real.pi / (2 * N))) *
          (2 * (ppZRidgeIdx N n : ℝ) + 2 + n - N)) := by
      push_cast
      ring
    have h3 : 0 ≤ 2 * (Real.pi / N * Real.tan (n * Real.pi / (2 * N))) *
        (2 * (ppZRidgeIdx N n : ℝ) + 2 + n - N) :=
      mul_nonneg (by linarith) (by linarith)
    linarith

/-- The Gaussian bound to the left of the ridge, `i = i*(n) - D`. -/
private theorem normFactor_le_ridge_left_ridgeI {N n : ℕ} (hn : n < N) (D : ℕ) :
    ∀ i : ℕ, i + D = ppZRidgeIdx N n → geoNormFactor N n i ≤ ppZRidge N n *
      Real.exp (-(2 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) * ((D : ℝ) ^ 2 - D)) := by
  induction D with
  | zero =>
    intro i hi
    rw [add_zero] at hi
    simp [ppZRidge, hi]
  | succ D ih =>
    intro i hi
    have ih' := ih (i + 1) (by omega)
    have hN : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hb := ridgeIdx_bounds_ridgeI hn.le
    have hb1 : 2 * (ppZRidgeIdx N n : ℝ) + n ≤ N := by exact_mod_cast hb.1
    have hiD : (ppZRidgeIdx N n : ℝ) = (i : ℝ) + D + 1 := by
      rw [← hi]
      push_cast
      ring
    have htan := tan_half_angle_nonneg_ridgeI hn.le
    have hT := (ridge_pos_ridgeI hn).le
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    have hstep := ppZ_normFactor_step_right_ge (N := N) (n := n) (i := i)
      (by omega) (by linarith)
    have hS : geoNormFactor N n i ≤ geoNormFactor N n (i + 1) *
        Real.exp (-((4 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) *
          (((N : ℝ) - n) / 2 - i - 1))) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
      exact hstep
    refine hS.trans ?_
    refine (mul_le_mul_of_nonneg_right ih' (Real.exp_pos _).le).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hT
    have hX : 0 ≤ Real.pi / N * Real.tan (n * Real.pi / (2 * N)) :=
      mul_nonneg (by positivity) htan
    have e : -(2 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) * ((D : ℝ) ^ 2 - D) +
        -((4 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) *
          (((N : ℝ) - n) / 2 - i - 1)) -
        -(2 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) *
          (((D + 1 : ℕ) : ℝ) ^ 2 - ((D + 1 : ℕ) : ℝ)) =
        -(2 * (Real.pi / N * Real.tan (n * Real.pi / (2 * N))) *
          ((N : ℝ) - n - 2 * i - 2 * D - 2)) := by
      push_cast
      ring
    have h3 : 0 ≤ 2 * (Real.pi / N * Real.tan (n * Real.pi / (2 * N))) *
        ((N : ℝ) - n - 2 * i - 2 * D - 2) :=
      mul_nonneg (by linarith) (by linarith)
    linarith

/-- Gaussian bound in `i` around the ridge:
`S_{n,i} ≤ T_n · exp(-(2π/N) tan(nπ/2N) (D² - D))`, `D = |i - i*(n)|`. -/
theorem ppZ_normFactor_le_ridge {N n i : ℕ} (h : n + i < N) :
    geoNormFactor N n i ≤ ppZRidge N n *
      Real.exp (-(2 * Real.pi / N) * Real.tan (n * Real.pi / (2 * N)) *
        (((i : ℝ) - ppZRidgeIdx N n) ^ 2 - |(i : ℝ) - ppZRidgeIdx N n|)) := by
  rcases le_total (ppZRidgeIdx N n) i with hle | hle
  · obtain ⟨D, rfl⟩ := Nat.exists_eq_add_of_le hle
    have key := normFactor_le_ridge_right_ridgeI D h
    have e : ((ppZRidgeIdx N n + D : ℕ) : ℝ) - ppZRidgeIdx N n = D := by
      push_cast
      ring
    rw [e, Nat.abs_cast]
    exact key
  · obtain ⟨D, hD⟩ := Nat.exists_eq_add_of_le hle
    have key := normFactor_le_ridge_left_ridgeI (by omega) D i hD.symm
    have e : (i : ℝ) - ppZRidgeIdx N n = -D := by
      rw [hD]
      push_cast
      ring
    rw [e, neg_sq, abs_neg, Nat.abs_cast]
    exact key

end AJConjecture
