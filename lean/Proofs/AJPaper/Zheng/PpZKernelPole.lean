import Mathlib
import AJPaper.Zheng.PpZStripPole
import AJPaper.Zheng.PpZTauDefs

/-!
# Crossing one pole of the kernel (Unit PpZ, node `PpZ_KernelPole`)

Source: Zheng, (5.10).

`ppZKernel a k A x₀ w = e^{-A(w - x₀)²} w^{2k} τ(ωw)`: the integrand of Zheng's
`∫_C e^{pq(nz - z²/h)} z^{2k} τ(z) dz` in the variable `w = z/ω`, after completing the square
(`A = aN/π`, `x₀ = (πc/N)ω`). Its poles are `w_j = ω(2j+1)π/(2a)`, simple, with residue
`ppZKernelRes a k A x₀ j = e^{-A(w_j - x₀)²} w_j^{2k} (-1)^j sin((2j+1)π/a)/(aω)`.

`ppZ_kernel_cross_pole`: if `Im w_{j-1} < Y₁ < Im w_j < Y₂ < Im w_{j+1}`
(`Im w_j = (2j+1)π/(2a√2)`), then
`∫_ℝ F(x + iY₁) dx - ∫_ℝ F(x + iY₂) dx = 2πi · Res_j`.

Route. `ppZ_strip_shift_simple_pole` with `P(w) = e^{-A(w-x₀)²} w^{2k} sinh(2ωw)`,
`Q(w) = cosh(aωw)`, `w₀ = w_j`.
* Zeros of `Q` in the closed strip: only `w_j` (`ppZ_cosh_omega_eq_zero_iff`,
  `Im(ω t) = t/√2` for real `t`, and the hypotheses on `Y₁, Y₂`).
* `Q'(w) = aω sinh(aωw)`, `aωw_j = i(2j+1)π/2`, `sinh(i(2j+1)π/2) = i(-1)^j ≠ 0`;
  `sinh(2ωw_j) = i sin((2j+1)π/a)`; so `P(w_j)/Q'(w_j)` is the stated residue (`ω² = i`).
* Decay: with `w = x + iy`, `|e^{-A(w-x₀)²}| = e^{-A((x - Re x₀)² - (y - Im x₀)²)}`,
  `|sinh(2ωw)| ≤ e^{2|w|}`, and `|cosh(aωw)|² ≥ sinh²(a(x - y)/√2) ≥ 1` for `|x| ≥ |y| + 2`
  (`ppZ_normSq_cosh`); a Gaussian times `e^{c|x|}(1 + |x|)^{2k}` is `≤ M/(1 + x²)`.
-/

noncomputable section

namespace AJConjecture

/-- The kernel `F(w) = e^{-A(w - x₀)²} w^{2k} τ(ωw)`. -/
def ppZKernel (a k : ℕ) (A : ℝ) (x₀ w : ℂ) : ℂ :=
  Complex.exp (-(A : ℂ) * (w - x₀) ^ 2) * w ^ (2 * k) * ppZTau a (ppZOmega * w)

/-- The residue of the kernel at `w_j = ω(2j+1)π/(2a)`. -/
def ppZKernelRes (a k : ℕ) (A : ℝ) (x₀ : ℂ) (j : ℕ) : ℂ :=
  Complex.exp (-(A : ℂ) * (ppZOmega * ((2 * (j : ℂ) + 1) * Real.pi / (2 * a)) - x₀) ^ 2) *
    (ppZOmega * ((2 * (j : ℂ) + 1) * Real.pi / (2 * a))) ^ (2 * k) *
    ((-1) ^ j * (Real.sin ((2 * (j : ℝ) + 1) * Real.pi / a) : ℂ) / (a * ppZOmega))

/-- `Im(ωt) = t/√2` for real `t`. -/
private theorem im_omega_mul_ppZKernelPole (t : ℝ) :
    (ppZOmega * (t : ℂ)).im = t / Real.sqrt 2 := by
  have h : (1 + Complex.I) / (Real.sqrt 2 : ℂ) * (t : ℂ) =
      ((t / Real.sqrt 2 : ℝ) : ℂ) + ((t / Real.sqrt 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [ppZOmega_eq, h]
  simp

/-- `Im w_j = (2j+1)π/(2a√2)`. -/
private theorem im_pole_ppZKernelPole (a : ℕ) (j : ℤ) :
    (ppZOmega * ((2 * (j : ℂ) + 1) * Real.pi / (2 * a))).im =
      (2 * (j : ℝ) + 1) * Real.pi / (2 * a * Real.sqrt 2) := by
  have h : ((2 * (j : ℂ) + 1) * Real.pi / (2 * a) : ℂ) =
      (((2 * (j : ℝ) + 1) * Real.pi / (2 * a) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, im_omega_mul_ppZKernelPole, div_div]

/-- In the closed strip between the neighbouring poles, `cosh(aωw)` vanishes only at `w_j`. -/
private theorem cosh_ne_zero_of_strip_ppZKernelPole (a : ℕ) (ha : 1 ≤ a) (j : ℕ) {Y₁ Y₂ : ℝ}
    (h1 : (2 * (j : ℝ) - 1) * Real.pi / (2 * a * Real.sqrt 2) < Y₁)
    (h4 : Y₂ < (2 * (j : ℝ) + 3) * Real.pi / (2 * a * Real.sqrt 2)) (w : ℂ)
    (hw1 : Y₁ ≤ w.im) (hw2 : w.im ≤ Y₂)
    (hne : w ≠ ppZOmega * ((2 * (j : ℂ) + 1) * Real.pi / (2 * a))) :
    Complex.cosh (a * (ppZOmega * w)) ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := (ppZ_cosh_omega_eq_zero_iff a ha w).mp h
  have him : w.im = (2 * (i : ℝ) + 1) * Real.pi / (2 * a * Real.sqrt 2) := by
    rw [hi, im_pole_ppZKernelPole]
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hD : (0 : ℝ) < 2 * a * Real.sqrt 2 := by positivity
  have e1 : (2 * ((j : ℤ) : ℝ) - 1) < 2 * (i : ℝ) + 1 := by
    have h5 := h1.trans_le hw1
    rw [him, div_lt_div_iff_of_pos_right hD] at h5
    simpa using lt_of_mul_lt_mul_right h5 Real.pi_pos.le
  have e2 : 2 * (i : ℝ) + 1 < (2 * ((j : ℤ) : ℝ) + 3) := by
    have h5 := hw2.trans_lt h4
    rw [him, div_lt_div_iff_of_pos_right hD] at h5
    simpa using lt_of_mul_lt_mul_right h5 Real.pi_pos.le
  have e3 : 2 * (j : ℤ) - 1 < 2 * i + 1 := by exact_mod_cast e1
  have e4 : 2 * i + 1 < 2 * (j : ℤ) + 3 := by exact_mod_cast e2
  have e5 : i = (j : ℤ) := by omega
  rw [e5] at hi
  exact hne (by simpa using hi)

/-- `2ωw_j = i(2j+1)π/a`. -/
private theorem two_omega_pole_ppZKernelPole (a : ℕ) (ha : 1 ≤ a) (j : ℕ) :
    2 * (ppZOmega * (ppZOmega * ((2 * (j : ℂ) + 1) * Real.pi / (2 * a)))) =
      (((2 * (j : ℝ) + 1) * Real.pi / a : ℝ) : ℂ) * Complex.I := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  push_cast
  field_simp
  linear_combination (2 * (j : ℂ) + 1) * ppZOmega_sq

/-- `aωw_j = i(jπ + π/2)`. -/
private theorem a_omega_pole_ppZKernelPole (a : ℕ) (ha : 1 ≤ a) (j : ℕ) :
    (a : ℂ) * (ppZOmega * (ppZOmega * ((2 * (j : ℂ) + 1) * Real.pi / (2 * a)))) =
      ((j * Real.pi + Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  push_cast
  field_simp
  linear_combination (2 * (j : ℂ) + 1) * ppZOmega_sq

/-- `ω(x + iy) = (x - y)/√2 + i(x + y)/√2`. -/
private theorem omega_mul_ppZKernelPole (x y : ℝ) :
    ppZOmega * ((x : ℂ) + y * Complex.I) = (((x - y) / Real.sqrt 2 : ℝ) : ℂ) +
      (((x + y) / Real.sqrt 2 : ℝ) : ℂ) * Complex.I := by
  have hs2' : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  rw [ppZOmega_eq]
  push_cast
  field_simp
  linear_combination (y : ℂ) * Complex.I_sq

/-- `‖cosh(aω(x + iy))‖ ≥ 1` once `|x| ≥ |y| + 2`. -/
private theorem one_le_norm_cosh_ppZKernelPole (a : ℕ) (ha : 1 ≤ a) {x y : ℝ}
    (hx : |y| + 2 ≤ |x|) :
    1 ≤ ‖Complex.cosh (a * (ppZOmega * ((x : ℂ) + y * Complex.I)))‖ := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : (a * (ppZOmega * ((x : ℂ) + y * Complex.I)) : ℂ) =
      ((a * ((x - y) / Real.sqrt 2) : ℝ) : ℂ) +
        ((a * ((x + y) / Real.sqrt 2) : ℝ) : ℂ) * Complex.I := by
    rw [omega_mul_ppZKernelPole]
    push_cast
    ring
  have h2 := ppZ_normSq_cosh (a * ((x - y) / Real.sqrt 2)) (a * ((x + y) / Real.sqrt 2))
  rw [← h1, Complex.normSq_eq_norm_sq] at h2
  have h3 : 1 ≤ |Real.sinh (a * ((x - y) / Real.sqrt 2))| := by
    rw [Real.abs_sinh]
    have h4 := Real.self_le_sinh_iff.mpr (abs_nonneg (a * ((x - y) / Real.sqrt 2)))
    have h5 : 1 ≤ |(a : ℝ) * ((x - y) / Real.sqrt 2)| := by
      rw [abs_mul, abs_div, Nat.abs_cast, abs_of_pos hs2]
      have h6 : 2 ≤ |x - y| := by
        have := abs_sub_abs_le_abs_sub x y
        linarith
      have h7 : Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have h8 : 1 ≤ |x - y| / Real.sqrt 2 := by
        rw [le_div_iff₀ hs2]
        linarith
      have h9 : (1 : ℝ) ≤ a := by exact_mod_cast ha
      nlinarith
    linarith
  have h10 : 1 ≤ Real.sinh (a * ((x - y) / Real.sqrt 2)) ^ 2 := by
    rw [← sq_abs]
    nlinarith
  nlinarith [norm_nonneg (Complex.cosh (a * (ppZOmega * ((x : ℂ) + y * Complex.I)))),
    sq_nonneg (Real.cos (a * ((x + y) / Real.sqrt 2)))]

/-- `‖sinh z‖ ≤ e^{‖z‖}`. -/
private theorem norm_sinh_le_exp_norm_ppZKernelPole (z : ℂ) :
    ‖Complex.sinh z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.sinh, norm_div]
  have h := norm_sub_le (Complex.exp z) (Complex.exp (-z))
  have h1 := Complex.norm_exp_le_exp_norm z
  have h2 := Complex.norm_exp_le_exp_norm (-z)
  rw [norm_neg] at h2
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h3, div_le_iff₀ (by norm_num)]
  linarith

/-- `‖sinh(2ω(x + iy))‖ ≤ e^{2(|x| + |y|)}`. -/
private theorem norm_sinh_le_exp_ppZKernelPole (x y : ℝ) :
    ‖Complex.sinh (2 * (ppZOmega * ((x : ℂ) + y * Complex.I)))‖ ≤
      Real.exp (2 * (|x| + |y|)) := by
  refine (norm_sinh_le_exp_norm_ppZKernelPole _).trans (Real.exp_le_exp.mpr ?_)
  have hω : ‖ppZOmega‖ = 1 := by
    rw [ppZOmega, Complex.norm_exp]
    simp
  have h := Complex.norm_le_abs_re_add_abs_im ((x : ℂ) + y * Complex.I)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
    Complex.mul_im, zero_add] at h
  rw [norm_mul, norm_mul, hω, one_mul, Complex.norm_ofNat]
  linarith

/-- The size of the kernel away from the poles. -/
private theorem norm_kernel_le_ppZKernelPole (a k : ℕ) (ha : 1 ≤ a) (A : ℝ) (x₀ : ℂ)
    {x y : ℝ} (hx : |y| + 2 ≤ |x|) :
    ‖ppZKernel a k A x₀ ((x : ℂ) + y * Complex.I)‖ ≤
      Real.exp (-A * (x - x₀.re) ^ 2 + A * (y - x₀.im) ^ 2) * (|x| + |y|) ^ (2 * k) *
        Real.exp (2 * (|x| + |y|)) := by
  have hre : (-(A : ℂ) * ((x : ℂ) + y * Complex.I - x₀) ^ 2).re =
      -A * (x - x₀.re) ^ 2 + A * (y - x₀.im) ^ 2 := by
    simp [pow_two]
    ring
  have hc := one_le_norm_cosh_ppZKernelPole a ha hx
  have hs := norm_sinh_le_exp_ppZKernelPole x y
  have hw : ‖(x : ℂ) + y * Complex.I‖ ≤ |x| + |y| := by
    simpa using Complex.norm_le_abs_re_add_abs_im ((x : ℂ) + y * Complex.I)
  have hq : ‖Complex.sinh (2 * (ppZOmega * ((x : ℂ) + y * Complex.I)))‖ /
      ‖Complex.cosh (a * (ppZOmega * ((x : ℂ) + y * Complex.I)))‖ ≤
        Real.exp (2 * (|x| + |y|)) :=
    (div_le_self (norm_nonneg _) hc).trans hs
  rw [ppZKernel, ppZTau, norm_mul, norm_mul, norm_div, norm_pow, Complex.norm_exp, hre]
  gcongr

/-- A Gaussian beats a polynomial times an exponential, with room for `1/(1 + x²)`. -/
private theorem gauss_decay_ppZKernelPole {A : ℝ} (hA : 0 < A) (p : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (n : ℕ) :
    ∃ M : ℝ, ∀ x : ℝ,
      Real.exp (-A * (x - p) ^ 2) * (|x| + B) ^ n * Real.exp (2 * |x|) ≤ M / (1 + x ^ 2) := by
  refine ⟨2 * n.factorial * Real.exp B * Real.exp ((2 * A * |p| + 4) ^ 2 / (4 * A)),
    fun x ↦ ?_⟩
  rw [le_div_iff₀ (by positivity)]
  have h1 : (|x| + B) ^ n ≤ n.factorial * Real.exp (|x| + B) := by
    have := Real.pow_div_factorial_le_exp (x := |x| + B) (by positivity) n
    rwa [div_le_iff₀' (by positivity)] at this
  have h2 : 1 + x ^ 2 ≤ 2 * Real.exp |x| := by
    have := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
    rw [sq_abs] at this
    nlinarith [abs_nonneg x]
  have h3 : -A * (x - p) ^ 2 + 4 * |x| ≤ (2 * A * |p| + 4) ^ 2 / (4 * A) := by
    rw [le_div_iff₀ (by positivity)]
    have h4 : p * x ≤ |p| * |x| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h5 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith [sq_nonneg (2 * A * |p| + 4 - 2 * A * |x|), sq_nonneg p,
      mul_le_mul_of_nonneg_left h4 hA.le, mul_pos hA hA, sq_nonneg (A * p)]
  calc Real.exp (-A * (x - p) ^ 2) * (|x| + B) ^ n * Real.exp (2 * |x|) * (1 + x ^ 2)
      ≤ Real.exp (-A * (x - p) ^ 2) * (n.factorial * Real.exp (|x| + B)) *
          Real.exp (2 * |x|) * (2 * Real.exp |x|) := by gcongr
    _ = 2 * n.factorial * Real.exp B * Real.exp (-A * (x - p) ^ 2 + 4 * |x|) := by
        rw [Real.exp_add |x| B, show -A * (x - p) ^ 2 + 4 * |x| =
          -A * (x - p) ^ 2 + |x| + 2 * |x| + |x| by ring, Real.exp_add, Real.exp_add,
          Real.exp_add]
        ring
    _ ≤ 2 * n.factorial * Real.exp B * Real.exp ((2 * A * |p| + 4) ^ 2 / (4 * A)) := by
        gcongr

/-- Decay of the kernel on a horizontal strip. -/
private theorem kernel_decay_ppZKernelPole (a k : ℕ) (ha : 1 ≤ a) {A : ℝ} (hA : 0 < A)
    (x₀ : ℂ) (Y₁ Y₂ : ℝ) :
    ∃ M R : ℝ, ∀ x y : ℝ, Y₁ ≤ y → y ≤ Y₂ → R ≤ |x| →
      ‖ppZKernel a k A x₀ ((x : ℂ) + y * Complex.I)‖ ≤ M / (1 + x ^ 2) := by
  have hB : 0 ≤ max |Y₁| |Y₂| := le_max_of_le_left (abs_nonneg _)
  obtain ⟨M, hM⟩ := gauss_decay_ppZKernelPole hA x₀.re hB (2 * k)
  refine ⟨Real.exp (A * (max |Y₁| |Y₂| + |x₀.im|) ^ 2) * Real.exp (2 * max |Y₁| |Y₂|) * M,
    max |Y₁| |Y₂| + 2, fun x y hy1 hy2 hx ↦ ?_⟩
  have hyB : |y| ≤ max |Y₁| |Y₂| := abs_le_max_abs_abs hy1 hy2
  refine (norm_kernel_le_ppZKernelPole a k ha A x₀ (by linarith)).trans ?_
  have h1 : (y - x₀.im) ^ 2 ≤ (max |Y₁| |Y₂| + |x₀.im|) ^ 2 := by
    rw [← sq_abs (y - x₀.im)]
    gcongr
    exact (abs_sub _ _).trans (by linarith)
  have h2 := hM x
  rw [Real.exp_add]
  calc Real.exp (-A * (x - x₀.re) ^ 2) * Real.exp (A * (y - x₀.im) ^ 2) *
        (|x| + |y|) ^ (2 * k) * Real.exp (2 * (|x| + |y|))
      ≤ Real.exp (-A * (x - x₀.re) ^ 2) * Real.exp (A * (max |Y₁| |Y₂| + |x₀.im|) ^ 2) *
          (|x| + max |Y₁| |Y₂|) ^ (2 * k) *
          (Real.exp (2 * |x|) * Real.exp (2 * max |Y₁| |Y₂|)) := by
        rw [← Real.exp_add (2 * |x|)]
        gcongr
        linarith
    _ = Real.exp (A * (max |Y₁| |Y₂| + |x₀.im|) ^ 2) * Real.exp (2 * max |Y₁| |Y₂|) *
          (Real.exp (-A * (x - x₀.re) ^ 2) * (|x| + max |Y₁| |Y₂|) ^ (2 * k) *
            Real.exp (2 * |x|)) := by ring
    _ ≤ Real.exp (A * (max |Y₁| |Y₂| + |x₀.im|) ^ 2) * Real.exp (2 * max |Y₁| |Y₂|) *
          (M / (1 + x ^ 2)) := by gcongr
    _ = _ := by ring

/-- Moving the line of integration across the pole `w_j` picks up `2πi` times the residue. -/
theorem ppZ_kernel_cross_pole (a k : ℕ) (ha : 1 ≤ a) {A : ℝ} (hA : 0 < A) (x₀ : ℂ) (j : ℕ)
    {Y₁ Y₂ : ℝ} (h1 : (2 * (j : ℝ) - 1) * Real.pi / (2 * a * Real.sqrt 2) < Y₁)
    (h2 : Y₁ < (2 * (j : ℝ) + 1) * Real.pi / (2 * a * Real.sqrt 2))
    (h3 : (2 * (j : ℝ) + 1) * Real.pi / (2 * a * Real.sqrt 2) < Y₂)
    (h4 : Y₂ < (2 * (j : ℝ) + 3) * Real.pi / (2 * a * Real.sqrt 2)) :
    (∫ x : ℝ, ppZKernel a k A x₀ (x + Y₁ * Complex.I)) -
        ∫ x : ℝ, ppZKernel a k A x₀ (x + Y₂ * Complex.I) =
      2 * Real.pi * Complex.I * ppZKernelRes a k A x₀ j := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hω : ppZOmega ≠ 0 := fun h ↦ by
    have := ppZOmega_sq
    rw [h] at this
    simp at this
    exact Complex.I_ne_zero this.symm
  have him : (ppZOmega * ((2 * (j : ℂ) + 1) * Real.pi / (2 * a))).im =
      (2 * (j : ℝ) + 1) * Real.pi / (2 * a * Real.sqrt 2) := by
    simpa using im_pole_ppZKernelPole a (j : ℤ)
  obtain ⟨M, R, hdec⟩ := kernel_decay_ppZKernelPole a k ha hA x₀ Y₁ Y₂
  have hQd : ∀ w : ℂ, HasDerivAt (fun w : ℂ ↦ Complex.cosh (a * (ppZOmega * w)))
      (Complex.sinh (a * (ppZOmega * w)) * (a * (ppZOmega * 1))) w := fun w ↦
    (((hasDerivAt_id w).const_mul ppZOmega).const_mul (a : ℂ)).ccosh
  have hsin : Real.sin (j * Real.pi + Real.pi / 2) = (-1) ^ j := by
    rw [Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
  have hcos : Real.cos (j * Real.pi + Real.pi / 2) = 0 := by
    rw [Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]
  have hpm : ((-1 : ℂ) ^ j) * ((-1 : ℂ) ^ j) = 1 := by
    rw [← mul_pow]
    simp
  have key := ppZ_strip_shift_simple_pole
    (P := fun w : ℂ ↦ Complex.exp (-(A : ℂ) * (w - x₀) ^ 2) * w ^ (2 * k) *
      Complex.sinh (2 * (ppZOmega * w)))
    (Q := fun w : ℂ ↦ Complex.cosh (a * (ppZOmega * w))) (Y₁ := Y₁) (Y₂ := Y₂) (M := M)
    (R := R) (w₀ := ppZOmega * ((2 * (j : ℂ) + 1) * Real.pi / (2 * a)))
    (by fun_prop) (by fun_prop) (by rw [him]; exact h2) (by rw [him]; exact h3)
    (by
      rw [a_omega_pole_ppZKernelPole a ha j, Complex.cosh_mul_I, ← Complex.ofReal_cos, hcos,
        Complex.ofReal_zero])
    (by
      rw [(hQd _).deriv, a_omega_pole_ppZKernelPole a ha j, Complex.sinh_mul_I,
        ← Complex.ofReal_sin, hsin]
      simp [ha', hω])
    (fun w hw1 hw2 hne ↦ cosh_ne_zero_of_strip_ppZKernelPole a ha j h1 h4 w hw1 hw2 hne)
    (fun x y hy1 hy2 hx ↦ by
      have := hdec x y hy1 hy2 hx
      rwa [ppZKernel, ppZTau, ← mul_div_assoc] at this)
  have hPQ : ∀ w : ℂ, ppZKernel a k A x₀ w = Complex.exp (-(A : ℂ) * (w - x₀) ^ 2) *
      w ^ (2 * k) * Complex.sinh (2 * (ppZOmega * w)) / Complex.cosh (a * (ppZOmega * w)) :=
    fun w ↦ by rw [ppZKernel, ppZTau, mul_div_assoc]
  simp only [hPQ]
  rw [key, (hQd _).deriv, a_omega_pole_ppZKernelPole a ha j, Complex.sinh_mul_I,
    two_omega_pole_ppZKernelPole a ha j, Complex.sinh_mul_I, ← Complex.ofReal_sin,
    ← Complex.ofReal_sin, hsin, ppZKernelRes]
  have hne : (-1 : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  congr 1
  rw [mul_assoc _ (_ ^ (2 * k)), mul_assoc _ (_ ^ (2 * k)), mul_div_assoc]
  congr 1
  rw [mul_div_assoc, mul_one, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  congr 1
  rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero hne Complex.I_ne_zero) (mul_ne_zero ha' hω))
      (mul_ne_zero ha' hω)]
  linear_combination
    (-((Real.sin ((2 * (j : ℝ) + 1) * Real.pi / a) : ℂ) * Complex.I * a * ppZOmega)) * hpm

end AJConjecture
