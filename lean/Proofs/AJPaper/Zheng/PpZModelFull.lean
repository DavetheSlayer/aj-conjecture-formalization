import Mathlib
import AJPaper.Zheng.PpZNormLocalStep
import AJPaper.Zheng.PpZThetaOne

/-!
# The Gaussian model sum over `ℤ²` (Unit PpZ, node `PpZ_ModelFull`)

Source: Zheng, (3.30) and the constant (3.34).

`ppZModel N β n i = exp(V(n,i) + iβπ(n - N/2)²/(2N))`, `V = ppZPot N`, for `(n, i) ∈ ℤ²`: the
model of the summand `a_n^β S_{n,i}/(e^{iβπ(1/4 - N/8)} S₀)`.

* `ppZ_model_norm`: `‖ppZModel N β n i‖ = exp(V(n, i))`.
* `ppZ_model_inner_tsum`: `∑_{i ∈ ℤ} ppZModel N β n i =
  e^{-(π/(2N))(1 - iβ)(n-N/2)²} · ∑_i e^{-(2π/N)(i - N/4 + (n-N/2)/2)²}`
  (`Q(x, y) = 2(y + x/2)² + x²/2`).
* `ppZ_model_summable`: absolute summability over `ℤ²`.

Route. Norm: the second term of the exponent is purely imaginary (`Complex.norm_exp`).
Inner sum: `Q(x, y) = 2(y + x/2)² + x²/2`, so the summand is
`e^{-(π/(2N))(1 - iβ)x²} · e^{-π(2/N)(i - (N/4 - x/2))²}`; pull the first factor out of the sum
(`tsum_mul_left`) and move the real exponential under the coercion (`Complex.ofReal_tsum`,
`Complex.ofReal_exp`). Summability: `e^{V} ≤ e^{-(π/(5N))(x² + y²)}` (from
`5Q(x, y) ≥ (|x| + |y|)² ≥ x² + y²`), a product of two summable Gaussians
(`ppZ_summable_gauss_shift` with real `c`, `Summable.mul_of_nonneg` / `summable_prod_of_nonneg`).
-/

noncomputable section

namespace AJConjecture

/-- The model summand `exp(V(n,i) + iβπ(n - N/2)²/(2N))` on `ℤ²`. -/
def ppZModel (N : ℕ) (β : ℝ) (n i : ℤ) : ℂ :=
  Complex.exp ((ppZPot N n i : ℝ) +
    β * Real.pi * Complex.I * ((n : ℂ) - N / 2) ^ 2 / (2 * N))

/-- Real shifted Gaussians are summable over `ℤ`. -/
private theorem summable_gauss_real_modelFull {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Summable fun k : ℤ ↦ Real.exp (-Real.pi * c * ((k : ℝ) - t) ^ 2) := by
  have h := ppZ_summable_gauss_shift (c := (c : ℂ)) (by simpa using hc) t
  rw [← Complex.summable_ofReal]
  convert h using 2 with k
  push_cast
  ring_nf

/-- `‖ppZModel N β n i‖ = exp(V(n, i))`. -/
theorem ppZ_model_norm (N : ℕ) (β : ℝ) (n i : ℤ) :
    ‖ppZModel N β n i‖ = Real.exp (ppZPot N n i) := by
  have e : (β : ℂ) * Real.pi * Complex.I * ((n : ℂ) - N / 2) ^ 2 / (2 * N) =
      ((β * Real.pi * ((n : ℝ) - N / 2) ^ 2 / (2 * N) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [ppZModel, Complex.norm_exp, e, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
    Complex.I_re, mul_zero, add_zero]

/-- The model summand is absolutely summable over `ℤ²`. -/
theorem ppZ_model_summable (N : ℕ) (hN : 1 ≤ N) (β : ℝ) :
    Summable fun p : ℤ × ℤ ↦ ‖ppZModel N β p.1 p.2‖ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (0 : ℝ) < 1 / (5 * N) := by positivity
  have h := (summable_gauss_real_modelFull hc (N / 2)).mul_of_nonneg
    (summable_gauss_real_modelFull hc (N / 4)) (fun _ ↦ (Real.exp_pos _).le)
    (fun _ ↦ (Real.exp_pos _).le)
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ ?_) h
  rw [ppZ_model_norm, ← Real.exp_add, Real.exp_le_exp, ppZPot]
  have key : 0 ≤ Real.pi / (5 * N) * (5 * (((p.1 : ℝ) - N / 2) ^ 2 +
      2 * ((p.1 : ℝ) - N / 2) * ((p.2 : ℝ) - N / 4) + 2 * ((p.2 : ℝ) - N / 4) ^ 2) -
      ((p.1 : ℝ) - N / 2) ^ 2 - ((p.2 : ℝ) - N / 4) ^ 2) :=
    mul_nonneg (by positivity) (by
      nlinarith [sq_nonneg (2 * ((p.1 : ℝ) - N / 2) + 5 / 2 * ((p.2 : ℝ) - N / 4)),
        sq_nonneg ((p.2 : ℝ) - N / 4)])
  have e : Real.pi / N = 5 * (Real.pi / (5 * N)) := by
    field_simp
  have e' : Real.pi * (1 / (5 * (N : ℝ))) = Real.pi / (5 * N) := by
    ring
  rw [e]
  simp only [neg_mul, e']
  linarith

/-- The inner sum over `i`: a Gaussian in `n` times a shifted real Gaussian lattice sum. -/
theorem ppZ_model_inner_tsum (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (n : ℤ) :
    ∑' i : ℤ, ppZModel N β n i =
      Complex.exp (-(Real.pi / (2 * N) : ℝ) * (1 - β * Complex.I) * ((n : ℂ) - N / 2) ^ 2) *
        ((∑' i : ℤ, Real.exp (-Real.pi * (2 / N) *
          ((i : ℝ) - (N / 4 - ((n : ℝ) - N / 2) / 2)) ^ 2) : ℝ) : ℂ) := by
  have hN' : (N : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  congr 1 with i
  rw [ppZModel, ppZPot, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

end AJConjecture
