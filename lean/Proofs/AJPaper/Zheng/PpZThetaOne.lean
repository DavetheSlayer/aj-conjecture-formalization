import Mathlib

/-!
# One-dimensional Gaussian lattice sums (Unit PpZ, node `PpZ_ThetaOne`)

Source: Zheng, (3.30) ("Riemann sum of the Gaussian"); here via Poisson summation, which Mathlib
has for Gaussians with a linear term (`Complex.tsum_exp_neg_quadratic`).

For `Re c > 0` and real `t`:
`∑_{k ∈ ℤ} e^{-πc(k-t)²} = c^{-1/2} ∑_{n ∈ ℤ} e^{-πn²/c - 2πint}`, so

* `ppZ_tsum_gauss_shift`:
  `‖∑_k e^{-πc(k-t)²} - c^{-1/2}‖ ≤ ‖c^{-1/2}‖ · 2/(e^{π Re(1/c)} - 1)`;
* `ppZ_summable_gauss_shift`: summability;
* `ppZ_tsum_gauss_real_le` (`c > 0` real): `∑_k e^{-πc(k-t)²} ≤ 1/√c + √c`;
* `ppZ_tsum_gauss_tail` (`c > 0` real): the part with `|k - t| ≥ R` is
  `≤ e^{-πcR²/2} (1/√(c/2) + √(c/2))`.

Route. `Complex.tsum_exp_neg_quadratic ha b` with `a = c`, `b = c t`:
`-πc k² + 2π(ct)k = -πc(k-t)² + πct²` and `-(π/c)(n + i c t)² = -πn²/c - 2πi t n + πct²`; cancel
`e^{πct²}`. The term `n = 0` is `1`; for `n ≠ 0`, `‖e^{-πn²/c - 2πint}‖ = e^{-πn² Re(1/c)}
≤ e^{-π|n| Re(1/c)}`, a geometric series with sum `2/(e^{π Re(1/c)} - 1)` over `n ≠ 0`
(`tsum_geometric_of_lt_one`, `Summable.tsum_le_tsum`; split `ℤ` into `n > 0` and `n < 0`, e.g. by
`tsum_of_nat_of_neg`).
Real bound: `2/(e^{π/c} - 1) ≤ 2c/π ≤ c`. Tail: `e^{-πcu²} ≤ e^{-πcR²/2} e^{-π(c/2)u²}` for
`|u| ≥ R`, then the real bound with `c/2`.
-/

noncomputable section

namespace AJConjecture

/-- A two-sided series dominated by `q^{|n|}` differs from its term at `0` by at most
`2q/(1 - q)`. -/
private theorem norm_tsum_int_sub_zero_le_thetaOne {h : ℤ → ℂ} {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hb : ∀ n : ℤ, ‖h n‖ ≤ q ^ n.natAbs) :
    ‖(∑' n : ℤ, h n) - h 0‖ ≤ 2 * (q / (1 - q)) := by
  have hg : HasSum (fun n : ℕ ↦ q * q ^ n) (q * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left q
  have b1 : ∀ n : ℕ, ‖h ((n : ℤ) + 1)‖ ≤ q * q ^ n := fun n ↦ by
    have := hb ((n : ℤ) + 1)
    rwa [show ((n : ℤ) + 1).natAbs = n + 1 by omega, pow_succ'] at this
  have b2 : ∀ n : ℕ, ‖h (-((n : ℤ) + 1))‖ ≤ q * q ^ n := fun n ↦ by
    have := hb (-((n : ℤ) + 1))
    rwa [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, pow_succ'] at this
  have s1 : Summable fun n : ℕ ↦ h ((n : ℤ) + 1) := hg.summable.of_norm_bounded b1
  have s2 : Summable fun n : ℕ ↦ h (-((n : ℤ) + 1)) := hg.summable.of_norm_bounded b2
  have s0 : Summable fun n : ℕ ↦ h (n : ℤ) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa only [Nat.cast_add, Nat.cast_one] using s1
  have e0 : ∑' n : ℕ, h (n : ℤ) = h 0 + ∑' n : ℕ, h ((n : ℤ) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using s0.tsum_eq_zero_add
  rw [tsum_of_nat_of_neg_add_one s0 s2, e0, add_assoc, add_sub_cancel_left,
    div_eq_mul_inv, two_mul]
  exact (norm_add_le _ _).trans
    (add_le_add (tsum_of_norm_bounded hg b1) (tsum_of_norm_bounded hg b2))

/-- Poisson summation for the shifted Gaussian: the dual sum has the terms
`e^{-πn²/c - 2πint}`. -/
private theorem tsum_gauss_shift_eq_dual_thetaOne {c : ℂ} (hc : 0 < c.re) (t : ℝ) :
    (∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) * c * ((k : ℂ) - t) ^ 2)) =
      1 / c ^ (1 / 2 : ℂ) * ∑' n : ℤ, Complex.exp (((-Real.pi * (n : ℝ) ^ 2 : ℝ) : ℂ) * (1 / c) +
        ((-2 * Real.pi * n * t : ℝ) : ℂ) * Complex.I) := by
  have hc0 : c ≠ 0 := fun h ↦ by simp [h] at hc
  have P := Complex.tsum_exp_neg_quadratic hc (c * t)
  have e1 : ∀ k : ℤ, Complex.exp (-(Real.pi : ℂ) * c * (k : ℂ) ^ 2 + 2 * Real.pi * (c * t) * k) =
      Complex.exp (-(Real.pi : ℂ) * c * ((k : ℂ) - t) ^ 2) *
        Complex.exp (Real.pi * c * (t : ℂ) ^ 2) := fun k ↦ by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : ∀ n : ℤ, Complex.exp (-(Real.pi : ℂ) / c * ((n : ℂ) + Complex.I * (c * t)) ^ 2) =
      Complex.exp (((-Real.pi * (n : ℝ) ^ 2 : ℝ) : ℂ) * (1 / c) +
        ((-2 * Real.pi * n * t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (Real.pi * c * (t : ℂ) ^ 2) := fun n ↦ by
    rw [← Complex.exp_add]; congr 1
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [e1, e2, tsum_mul_right] at P
  rw [← mul_assoc] at P
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) P

/-- `Re(1/c) > 0` when `Re c > 0`. -/
private theorem one_div_re_pos_thetaOne {c : ℂ} (hc : 0 < c.re) : 0 < (1 / c).re := by
  have hc0 : c ≠ 0 := fun h ↦ by simp [h] at hc
  rw [one_div, Complex.inv_re]
  exact div_pos hc (Complex.normSq_pos.mpr hc0)

/-- The dual terms are dominated by a geometric sequence. -/
private theorem norm_dual_term_le_thetaOne (c : ℂ) (hρ : 0 ≤ (1 / c).re) (t : ℝ) (n : ℤ) :
    ‖Complex.exp (((-Real.pi * (n : ℝ) ^ 2 : ℝ) : ℂ) * (1 / c) +
        ((-2 * Real.pi * n * t : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.exp (-(Real.pi * (1 / c).re)) ^ n.natAbs := by
  rw [Complex.norm_exp, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    Complex.I_re, mul_zero, add_zero, ← Real.exp_nat_mul, Real.exp_le_exp]
  have h1 : ((n.natAbs : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, ← sq_abs (n : ℝ)]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      nlinarith
  nlinarith [mul_nonneg Real.pi_pos.le hρ, mul_le_mul_of_nonneg_left h1
    (mul_nonneg Real.pi_pos.le hρ)]

/-- The shifted Gaussians are summable over `ℤ`. -/
theorem ppZ_summable_gauss_shift {c : ℂ} (hc : 0 < c.re) (t : ℝ) :
    Summable fun k : ℤ ↦ Complex.exp (-(Real.pi : ℂ) * c * ((k : ℂ) - t) ^ 2) := by
  have hterm : ∀ k : ℤ, Complex.exp (-(Real.pi : ℂ) * c * ((k : ℂ) - t) ^ 2) =
      jacobiTheta₂_term k (-Complex.I * c * t) (Complex.I * c) *
        Complex.exp (-(Real.pi : ℂ) * c * (t : ℂ) ^ 2) := fun k ↦ by
    rw [jacobiTheta₂_term, ← Complex.exp_add]; congr 1
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [hterm]
  exact ((summable_jacobiTheta₂_term_iff _ _).mpr (by simpa using hc)).mul_right _

/-- Poisson summation for a shifted Gaussian, with the error of the dual sum. -/
theorem ppZ_tsum_gauss_shift {c : ℂ} (hc : 0 < c.re) (t : ℝ) :
    ‖(∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) * c * ((k : ℂ) - t) ^ 2)) - 1 / c ^ (1 / 2 : ℂ)‖ ≤
      ‖1 / c ^ (1 / 2 : ℂ)‖ * (2 / (Real.exp (Real.pi * (1 / c).re) - 1)) := by
  have hρ := one_div_re_pos_thetaOne hc
  have hq1 : Real.exp (-(Real.pi * (1 / c).re)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hE : 1 < Real.exp (Real.pi * (1 / c).re) := by
    rw [Real.one_lt_exp_iff]; nlinarith [Real.pi_pos]
  have key := norm_tsum_int_sub_zero_le_thetaOne (Real.exp_pos _).le hq1
    (norm_dual_term_le_thetaOne c hρ.le t)
  have h0 : Complex.exp (((-Real.pi * ((0 : ℤ) : ℝ) ^ 2 : ℝ) : ℂ) * (1 / c) +
      ((-2 * Real.pi * (0 : ℤ) * t : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have hq : Real.exp (-(Real.pi * (1 / c).re)) / (1 - Real.exp (-(Real.pi * (1 / c).re))) =
      1 / (Real.exp (Real.pi * (1 / c).re) - 1) := by
    rw [Real.exp_neg]
    have : Real.exp (Real.pi * (1 / c).re) - 1 ≠ 0 := by linarith
    field_simp
  rw [h0, hq] at key
  rw [tsum_gauss_shift_eq_dual_thetaOne hc t, ← mul_sub_one, norm_mul]
  refine mul_le_mul_of_nonneg_left (key.trans (le_of_eq ?_)) (norm_nonneg _)
  ring

/-- Real shifted Gaussians are summable over `ℤ`. -/
private theorem summable_gauss_real_thetaOne {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Summable fun k : ℤ ↦ Real.exp (-Real.pi * c * ((k : ℝ) - t) ^ 2) := by
  have h := ppZ_summable_gauss_shift (c := (c : ℂ)) (by simpa using hc) t
  rw [← Complex.summable_ofReal]
  convert h using 2 with k
  push_cast
  ring_nf

/-- A real shifted Gaussian lattice sum is at most `1/√c + √c`. -/
theorem ppZ_tsum_gauss_real_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∑' k : ℤ, Real.exp (-Real.pi * c * ((k : ℝ) - t) ^ 2) ≤ 1 / Real.sqrt c + Real.sqrt c := by
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
  have hnorm : ‖1 / (c : ℂ) ^ (1 / 2 : ℂ)‖ = 1 / Real.sqrt c := by
    rw [norm_div, norm_one, Complex.norm_cpow_eq_rpow_re_of_pos hc, Real.sqrt_eq_rpow]
    norm_num
  rw [hS, hre, hnorm] at h
  have hx : Real.pi / c ≤ Real.exp (Real.pi * (1 / c)) - 1 := by
    have := Real.add_one_le_exp (Real.pi * (1 / c))
    rw [mul_one_div] at this ⊢
    linarith
  have hB : 2 / (Real.exp (Real.pi * (1 / c)) - 1) ≤ c := by
    have hπc : 0 < Real.pi / c := by positivity
    rw [div_le_iff₀ (by linarith)]
    have : c * (Real.pi / c) = Real.pi := by field_simp
    nlinarith [Real.pi_gt_three]
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have h1 := (norm_sub_norm_le _ _).trans h
  rw [hnorm, Complex.norm_real, Real.norm_eq_abs] at h1
  have h2 : 1 / Real.sqrt c * (2 / (Real.exp (Real.pi * (1 / c)) - 1)) ≤ 1 / Real.sqrt c * c :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h3 : 1 / Real.sqrt c * c = Real.sqrt c := by
    rw [one_div, inv_mul_eq_div, Real.div_sqrt]
  linarith [le_abs_self (∑' k : ℤ, Real.exp (-Real.pi * c * ((k : ℝ) - t) ^ 2))]

/-- The tail `|k - t| ≥ R` of a real shifted Gaussian lattice sum. -/
theorem ppZ_tsum_gauss_tail {c : ℝ} (hc : 0 < c) (t : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∑' k : ℤ, (if R ≤ |(k : ℝ) - t| then Real.exp (-Real.pi * c * ((k : ℝ) - t) ^ 2) else 0) ≤
      Real.exp (-Real.pi * c * R ^ 2 / 2) * (1 / Real.sqrt (c / 2) + Real.sqrt (c / 2)) := by
  have hc2 : 0 < c / 2 := by positivity
  have hs2 := summable_gauss_real_thetaOne hc2 t
  have hle : ∀ k : ℤ,
      (if R ≤ |(k : ℝ) - t| then Real.exp (-Real.pi * c * ((k : ℝ) - t) ^ 2) else 0) ≤
        Real.exp (-Real.pi * c * R ^ 2 / 2) *
          Real.exp (-Real.pi * (c / 2) * ((k : ℝ) - t) ^ 2) := fun k ↦ by
    split_ifs with hk
    · rw [← Real.exp_add, Real.exp_le_exp]
      have h1 : R ^ 2 ≤ ((k : ℝ) - t) ^ 2 := by
        rw [← sq_abs ((k : ℝ) - t)]
        exact pow_le_pow_left₀ hR hk 2
      nlinarith [mul_le_mul_of_nonneg_left h1 (mul_pos Real.pi_pos hc).le]
    · positivity
  have hnn : ∀ k : ℤ,
      0 ≤ (if R ≤ |(k : ℝ) - t| then Real.exp (-Real.pi * c * ((k : ℝ) - t) ^ 2) else 0) :=
    fun k ↦ by split_ifs <;> positivity
  have hs1 := Summable.of_nonneg_of_le hnn hle (hs2.mul_left _)
  refine (hs1.tsum_le_tsum hle (hs2.mul_left _)).trans ?_
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (ppZ_tsum_gauss_real_le hc2 t) (Real.exp_pos _).le

end AJConjecture
