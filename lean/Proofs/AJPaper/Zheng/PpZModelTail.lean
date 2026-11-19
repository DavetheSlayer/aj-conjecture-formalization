import Mathlib
import AJPaper.Zheng.PpZModelFull

/-!
# The Gaussian model outside a diamond (Unit PpZ, node `PpZ_ModelTail`)

Source: Zheng, (3.30) (second equality: the integral over the complement of the window).

* `ppZPot_le`: `V(x, y) ≤ -(π/(5N))(|x - N/2| + |y - N/4|)²`, i.e. `5 Q(x, y) ≥ (|x| + |y|)²`
  (`5(x² + 2xy + 2y²) - (|x| + |y|)² = 4x² + 10xy + 9y² - 2|x||y| ≥ (2|x| - 3|y|)² ≥ 0`).
* `ppZ_model_tail`: there is an absolute `K` with
  `∑_{(n,i) ∈ ℤ², |n-N/2| + |i-N/4| ≥ R} e^{V(n,i)} ≤ K N e^{-(π/10) R²/N}` for all `N ≥ 1`,
  `R ≥ 0`.

Route. For `d = |n-N/2| + |i-N/4| ≥ R`:
`e^{V} ≤ e^{-(π/(5N))d²} ≤ e^{-(π/(10N))R²} e^{-(π/(10N))((n-N/2)² + (i-N/4)²)}`
(`d² ≥ x² + y²`); the double sum factors, each factor `≤ √(10N) + 1/√(10N)`
(`ppZ_tsum_gauss_real_le` with `c = 1/(10N)`), so `K = 13` works. With `R = 0` this also bounds
the full sum of `e^{V}` by `K N`.
-/

noncomputable section

namespace AJConjecture

/-- Real shifted Gaussians are summable over `ℤ`. -/
private theorem summable_gauss_real_modelTail {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Summable fun k : ℤ ↦ Real.exp (-Real.pi * c * ((k : ℝ) - t) ^ 2) := by
  have h := ppZ_summable_gauss_shift (c := (c : ℂ)) (by simpa using hc) t
  rw [← Complex.summable_ofReal]
  convert h using 2 with k
  push_cast
  ring_nf

/-- A real shifted Gaussian lattice sum with `c = 1/(10N)` is at most `√(10N) + 1`. -/
private theorem tsum_gauss_tenth_le_modelTail {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ∑' k : ℤ, Real.exp (-Real.pi * (1 / (10 * N)) * ((k : ℝ) - t) ^ 2) ≤
      Real.sqrt (10 * N) + 1 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : (0 : ℝ) < 1 / (10 * N) := by positivity
  refine (ppZ_tsum_gauss_real_le hc t).trans ?_
  rw [one_div (10 * (N : ℝ)), Real.sqrt_inv, one_div, inv_inv]
  gcongr
  exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by linarith))

/-- `V(x, y) ≤ -(π/(5N))(|x - N/2| + |y - N/4|)²`. -/
theorem ppZPot_le (N : ℕ) (x y : ℝ) :
    ppZPot N x y ≤ -(Real.pi / (5 * N)) * (|x - N / 2| + |y - N / 4|) ^ 2 := by
  rw [ppZPot]
  set a : ℝ := x - N / 2
  set b : ℝ := y - N / 4
  have hab : -(|a| * |b|) ≤ a * b := by
    rw [← abs_mul]
    exact neg_abs_le _
  have key : 0 ≤ Real.pi / (5 * N) *
      (5 * (a ^ 2 + 2 * a * b + 2 * b ^ 2) - (|a| + |b|) ^ 2) :=
    mul_nonneg (by positivity) (by
      nlinarith [sq_abs a, sq_abs b, sq_nonneg (2 * |a| - 3 * |b|)])
  have e : Real.pi / N = 5 * (Real.pi / (5 * N)) := by
    ring
  rw [e]
  linarith

/-- The model outside the diamond of radius `R` is `O(N e^{-(π/10)R²/N})`. -/
theorem ppZ_model_tail :
    ∃ K : ℝ, ∀ (N : ℕ) (R : ℝ), 1 ≤ N → 0 ≤ R →
      ∑' p : ℤ × ℤ, (if R ≤ |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| then
          Real.exp (ppZPot N p.1 p.2) else 0) ≤
        K * N * Real.exp (-(Real.pi / 10) * R ^ 2 / N) := by
  refine ⟨31, fun N R hN hR ↦ ?_⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : (0 : ℝ) < 1 / (10 * N) := by positivity
  set f : ℤ → ℝ := fun k ↦ Real.exp (-Real.pi * (1 / (10 * N)) * ((k : ℝ) - N / 2) ^ 2) with hf'
  set g : ℤ → ℝ := fun k ↦ Real.exp (-Real.pi * (1 / (10 * N)) * ((k : ℝ) - N / 4) ^ 2) with hg'
  have hf : Summable f := summable_gauss_real_modelTail hc _
  have hg : Summable g := summable_gauss_real_modelTail hc _
  have hfg : Summable fun p : ℤ × ℤ ↦ f p.1 * g p.2 :=
    hf.mul_of_nonneg hg (fun _ ↦ (Real.exp_pos _).le) (fun _ ↦ (Real.exp_pos _).le)
  set C : ℝ := Real.exp (-(Real.pi / 10) * R ^ 2 / N) with hC
  have hle : ∀ p : ℤ × ℤ, (if R ≤ |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| then
      Real.exp (ppZPot N p.1 p.2) else 0) ≤ C * (f p.1 * g p.2) := fun p ↦ by
    split_ifs with h
    · rw [hC, hf', hg', ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      refine (ppZPot_le N _ _).trans ?_
      have h1 : R ^ 2 ≤ (|(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4|) ^ 2 :=
        pow_le_pow_left₀ hR h 2
      have h2 : ((p.1 : ℝ) - N / 2) ^ 2 + ((p.2 : ℝ) - N / 4) ^ 2 ≤
          (|(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4|) ^ 2 := by
        nlinarith [sq_abs ((p.1 : ℝ) - N / 2), sq_abs ((p.2 : ℝ) - N / 4),
          abs_nonneg ((p.1 : ℝ) - N / 2), abs_nonneg ((p.2 : ℝ) - N / 4)]
      have h3 : 0 ≤ Real.pi / (10 * N) * (2 * (|(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4|) ^ 2 -
          R ^ 2 - ((p.1 : ℝ) - N / 2) ^ 2 - ((p.2 : ℝ) - N / 4) ^ 2) :=
        mul_nonneg (by positivity) (by linarith)
      have e1 : Real.pi / (5 * N) = 2 * (Real.pi / (10 * N)) := by
        ring
      have e2 : -(Real.pi / 10) * R ^ 2 / N = -(Real.pi / (10 * N)) * R ^ 2 := by
        ring
      have e3 : -Real.pi * (1 / (10 * (N : ℝ))) = -(Real.pi / (10 * N)) := by
        ring
      rw [e1, e2, e3]
      linarith
    · positivity
  have hnn : ∀ p : ℤ × ℤ, 0 ≤ (if R ≤ |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| then
      Real.exp (ppZPot N p.1 p.2) else 0) := fun p ↦ by
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hsum := Summable.of_nonneg_of_le hnn hle (hfg.mul_left C)
  have hs0 : 0 ≤ Real.sqrt (10 * N) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (10 * N) ^ 2 = 10 * N := Real.sq_sqrt (by positivity)
  have hs2 : 1 ≤ Real.sqrt (10 * N) := Real.one_le_sqrt.mpr (by linarith)
  have hF : ∑' k, f k ≤ Real.sqrt (10 * N) + 1 := tsum_gauss_tenth_le_modelTail hN _
  have hG : ∑' k, g k ≤ Real.sqrt (10 * N) + 1 := tsum_gauss_tenth_le_modelTail hN _
  have hG0 : 0 ≤ ∑' k, g k := tsum_nonneg fun _ ↦ (Real.exp_pos _).le
  have hprod : (∑' k, f k) * (∑' k, g k) ≤ 31 * N :=
    calc (∑' k, f k) * (∑' k, g k) ≤ (Real.sqrt (10 * N) + 1) * (Real.sqrt (10 * N) + 1) :=
          mul_le_mul hF hG hG0 (by linarith)
      _ ≤ 31 * N := by nlinarith
  calc ∑' p : ℤ × ℤ, (if R ≤ |(p.1 : ℝ) - N / 2| + |(p.2 : ℝ) - N / 4| then
        Real.exp (ppZPot N p.1 p.2) else 0)
      ≤ ∑' p : ℤ × ℤ, C * (f p.1 * g p.2) := hsum.tsum_le_tsum hle (hfg.mul_left C)
    _ = C * ((∑' k, f k) * (∑' k, g k)) := by rw [tsum_mul_left, hf.tsum_mul_tsum hg hfg]
    _ ≤ C * (31 * N) := mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = 31 * N * C := by ring

end AJConjecture
