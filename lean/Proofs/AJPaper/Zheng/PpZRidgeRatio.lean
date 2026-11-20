import Mathlib
import AJPaper.Zheng.PpZRidgeI

/-!
# Exact ratios along the ridge (Unit PpZ, node `PpZ_RidgeRatio`)

Source: Zheng, Lemma 3.2 ((3.23): the maximum of `f` on the line `x + 2y = π` is at `x = π/2`);
here the exact discrete statement. With `φ_k = kπ/(2N)` and `T_n = S_{n,⌊(N-n)/2⌋}`:

* `ppZ_ridge_succ_odd`: if `N - n` is odd, then `i*(n+1) = i*(n)` and
  `T_{n+1} sin φ_{n+1} = T_n cos φ_{n+1}` (one step in `n`: `2 sin²((i*+n+1)π/N)/sin((n+1)π/N)`
  with `i* + n + 1 = (N+n+1)/2`, so the sine is `cos φ_{n+1}`).
* `ppZ_ridge_succ_even`: if `N - n` is even, then `i*(n+1) = i*(n) - 1` and
  `T_{n+1} sin φ_{n+1} cos φ_{n+1} = T_n cos² φ_n` (one step in `n` and one step back in `i`;
  `i* = (N-n)/2`, `sin(i*π/N) = cos φ_n`).
* `ppZ_ridge_center`: `T_{⌊N/2⌋} = S₀` (for `N ≡ 3 mod 4` the two indices `⌊N/4⌋`, `⌊N/4⌋ + 1`
  give the same value: the step ratio between them is `1`).

All three checked numerically for `N ≤ 59` and `N ∈ {101, 128, 255, 500}` (`scaf.py`, `ridge.py`).
-/

noncomputable section

namespace AJConjecture

/-- `sin(xπ/N) > 0` for `0 < x < N`. -/
private theorem sin_mul_pi_div_pos_ridgeRatio {N : ℕ} {x : ℝ} (h0 : 0 < x) (h1 : x < N) :
    0 < Real.sin (x * Real.pi / N) := by
  have hN : (0 : ℝ) < N := h0.trans h1
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [div_lt_iff₀ hN]
    nlinarith [Real.pi_pos]

/-- `sin(aπ/N) = sin(bπ/N)` when `a + b = N`. -/
private theorem sin_eq_sin_of_add_eq_ridgeRatio {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (h : a + b = N) : Real.sin (a * Real.pi / N) = Real.sin (b * Real.pi / N) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← Real.sin_pi_sub]
  congr 1
  field_simp
  linarith

/-- `sin(aπ/N) = cos(cπ/(2N))` when `2a = N + c`. -/
private theorem sin_eq_cos_of_two_mul_eq_add_ridgeRatio {N : ℕ} (hN : 0 < N) {a c : ℝ}
    (h : 2 * a = N + c) : Real.sin (a * Real.pi / N) = Real.cos (c * Real.pi / (2 * N)) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← Real.sin_add_pi_div_two]
  congr 1
  field_simp
  linarith

/-- `sin(aπ/N) = cos(cπ/(2N))` when `2a + c = N`. -/
private theorem sin_eq_cos_of_two_mul_add_eq_ridgeRatio {N : ℕ} (hN : 0 < N) {a c : ℝ}
    (h : 2 * a + c = N) : Real.sin (a * Real.pi / N) = Real.cos (c * Real.pi / (2 * N)) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← Real.sin_pi_div_two_sub]
  congr 1
  field_simp
  linarith

/-- `sin((n+1)π/N) = 2 sin φ_{n+1} cos φ_{n+1}`, and both factors are positive for `n + 1 < N`. -/
private theorem sin_succ_eq_two_mul_ridgeRatio {N n : ℕ} (h : n + 1 < N) :
    Real.sin (((n : ℝ) + 1) * Real.pi / N) =
        2 * Real.sin (((n : ℝ) + 1) * Real.pi / (2 * N)) *
          Real.cos (((n : ℝ) + 1) * Real.pi / (2 * N)) ∧
      0 < Real.sin (((n : ℝ) + 1) * Real.pi / (2 * N)) ∧
      0 < Real.cos (((n : ℝ) + 1) * Real.pi / (2 * N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlt : (n : ℝ) + 1 < N := by exact_mod_cast h
  have hπ := Real.pi_pos
  have h0 : 0 < ((n : ℝ) + 1) * Real.pi / (2 * N) := by positivity
  have h1 : ((n : ℝ) + 1) * Real.pi / (2 * N) < Real.pi / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨?_, Real.sin_pos_of_pos_of_lt_pi h0 (by linarith),
    Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩⟩
  rw [← Real.sin_two_mul]
  congr 1
  field_simp

/-- The ridge value at `n = ⌊N/2⌋` is `S₀`. -/
theorem ppZ_ridge_center (N : ℕ) : ppZRidge N (N / 2) = geoNormFactor0 N := by
  unfold ppZRidge geoNormFactor0
  by_cases h3 : N % 4 = 3
  · have hidx : ppZRidgeIdx N (N / 2) = N / 4 + 1 := by
      unfold ppZRidgeIdx
      omega
    rw [hidx]
    have hS := ppZ_normFactor_succ_right N (N / 2) (N / 4)
    have hsum : ((N / 4 : ℕ) : ℝ) + (N / 2 : ℕ) + 1 + (((N / 4 : ℕ) : ℝ) + 1) = N := by
      exact_mod_cast (by omega : N / 4 + N / 2 + 1 + (N / 4 + 1) = N)
    have hlt : ((N / 4 : ℕ) : ℝ) + 1 < N := by
      exact_mod_cast (by omega : N / 4 + 1 < N)
    rw [sin_eq_sin_of_add_eq_ridgeRatio (by omega) hsum] at hS
    have hpos := sin_mul_pi_div_pos_ridgeRatio (N := N) (x := ((N / 4 : ℕ) : ℝ) + 1)
      (by positivity) hlt
    exact mul_right_cancel₀ (pow_pos hpos 2).ne' hS
  · have hidx : ppZRidgeIdx N (N / 2) = N / 4 := by
      unfold ppZRidgeIdx
      omega
    rw [hidx]

/-- Ridge step when `N - n` is odd: `T_{n+1} sin φ_{n+1} = T_n cos φ_{n+1}`. -/
theorem ppZ_ridge_succ_odd {N n : ℕ} (h : n + 1 < N) (hp : (N - n) % 2 = 1) :
    ppZRidge N (n + 1) * Real.sin (((n : ℝ) + 1) * Real.pi / (2 * N)) =
      ppZRidge N n * Real.cos (((n : ℝ) + 1) * Real.pi / (2 * N)) := by
  have hidx1 : ppZRidgeIdx N (n + 1) = ppZRidgeIdx N n := by
    unfold ppZRidgeIdx
    omega
  have hi : 2 * (ppZRidgeIdx N n + n + 1) = N + (n + 1) := by
    unfold ppZRidgeIdx
    omega
  unfold ppZRidge
  rw [hidx1, ppZ_normFactor_succ_left]
  have hir : 2 * ((ppZRidgeIdx N n : ℝ) + n + 1) = N + ((n : ℝ) + 1) := by exact_mod_cast hi
  obtain ⟨e2, hs, hc⟩ := sin_succ_eq_two_mul_ridgeRatio h
  rw [sin_eq_cos_of_two_mul_eq_add_ridgeRatio (by omega) hir, e2]
  field_simp
  ring

/-- Ridge step when `N - n` is even: `T_{n+1} sin φ_{n+1} cos φ_{n+1} = T_n cos² φ_n`. -/
theorem ppZ_ridge_succ_even {N n : ℕ} (h : n + 1 < N) (hp : (N - n) % 2 = 0) :
    ppZRidge N (n + 1) * (Real.sin (((n : ℝ) + 1) * Real.pi / (2 * N)) *
        Real.cos (((n : ℝ) + 1) * Real.pi / (2 * N))) =
      ppZRidge N n * Real.cos ((n : ℝ) * Real.pi / (2 * N)) ^ 2 := by
  obtain ⟨j, hj⟩ : ∃ j, ppZRidgeIdx N n = j + 1 := by
    refine ⟨ppZRidgeIdx N n - 1, ?_⟩
    unfold ppZRidgeIdx
    omega
  have hj1 : ppZRidgeIdx N (n + 1) = j := by
    unfold ppZRidgeIdx at hj ⊢
    omega
  have hi : 2 * (j + 1) + n = N := by
    unfold ppZRidgeIdx at hj
    omega
  unfold ppZRidge
  rw [hj1, hj, ppZ_normFactor_succ_left]
  have hS := ppZ_normFactor_succ_right N n j
  have hir : 2 * ((j : ℝ) + 1) + n = N := by exact_mod_cast hi
  obtain ⟨e2, hs, hc⟩ := sin_succ_eq_two_mul_ridgeRatio h
  rw [sin_eq_cos_of_two_mul_add_eq_ridgeRatio (by omega) hir] at hS
  rw [hS, e2]
  generalize Real.sin (((n : ℝ) + 1) * Real.pi / (2 * N)) = s at hs ⊢
  generalize Real.cos (((n : ℝ) + 1) * Real.pi / (2 * N)) = c at hc ⊢
  field_simp
  ring

end AJConjecture
