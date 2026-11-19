import Mathlib
import AJFamily.VolumeDefs

/-!
# The Bloch–Wigner dilogarithm at `i`

`D(i) = Im Li₂(i) = ∑_{j ≥ 0} (-1)ʲ / (2j+1)² = G`: `|i| = 1`, so the logarithmic term vanishes,
and `Im(i^(n+1))` is `0` for even `n + 1` and `(-1)ʲ` for `n + 1 = 2j + 1`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The imaginary part of a term of the dilogarithm series at `i`. -/
private theorem im_term (n : ℕ) :
    (Complex.I ^ (n + 1) / ((n : ℂ) + 1) ^ 2).im = (Complex.I ^ (n + 1)).im / ((n : ℝ) + 1) ^ 2 := by
  have : ((n : ℂ) + 1) ^ 2 = (((n : ℝ) + 1) ^ 2 : ℝ) := by push_cast; ring
  rw [this, Complex.div_ofReal_im]

/-- `i^(2j+1) = (-1)ʲ i`. -/
private theorem I_pow_even (j : ℕ) : Complex.I ^ (2 * j + 1) = (-1 : ℂ) ^ j * Complex.I := by
  rw [pow_succ, pow_mul, Complex.I_sq]

/-- `i^(2j+2) = (-1)^(j+1)`. -/
private theorem I_pow_odd (j : ℕ) : Complex.I ^ (2 * j + 1 + 1) = (-1 : ℂ) ^ (j + 1) := by
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul, Complex.I_sq]

/-- The dilogarithm series converges absolutely at `i`. -/
private theorem summable_dilog_I :
    Summable fun n : ℕ ↦ Complex.I ^ (n + 1) / ((n : ℂ) + 1) ^ 2 := by
  refine Summable.of_norm ?_
  have h2 : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    exact this.congr fun n ↦ by push_cast; ring_nf
  refine h2.congr fun n ↦ ?_
  rw [norm_div, norm_pow, Complex.norm_I, one_pow, norm_pow]
  congr 1
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  push_cast; ring

/-- `D(i) = Im Li₂(i)`, since `log |i| = 0`. -/
private theorem blochWigner_I_eq : blochWigner Complex.I = (dilogSeries Complex.I).im := by
  have hnorm : ‖Complex.I‖ = 1 := Complex.norm_I
  unfold blochWigner
  simp only [hnorm, le_refl, ↓reduceIte, Real.log_one, mul_zero, add_zero]

/-- `Im Li₂(i)` as a real series. -/
private theorem dilogSeries_I_im :
    (dilogSeries Complex.I).im = ∑' n : ℕ, (Complex.I ^ (n + 1)).im / ((n : ℝ) + 1) ^ 2 := by
  unfold dilogSeries
  rw [Complex.im_tsum summable_dilog_I]
  exact tsum_congr im_term

/-- The real series is summable. -/
private theorem summable_im_terms :
    Summable fun n : ℕ ↦ (Complex.I ^ (n + 1)).im / ((n : ℝ) + 1) ^ 2 := by
  have := Complex.imCLM.summable summable_dilog_I
  exact this.congr fun n ↦ im_term n

/-- The even terms are the Catalan terms. -/
private theorem even_term (j : ℕ) :
    (Complex.I ^ (2 * j + 1)).im / (((2 * j : ℕ) : ℝ) + 1) ^ 2 =
      (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1) ^ 2 := by
  rw [I_pow_even]
  have : ((-1 : ℂ) ^ j * Complex.I).im = (-1 : ℝ) ^ j := by
    rw [show ((-1 : ℂ) ^ j) = (((-1 : ℝ) ^ j : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul,
      Complex.I_im, mul_one]
  rw [this]
  push_cast
  ring

/-- The odd terms vanish. -/
private theorem odd_term (j : ℕ) :
    (Complex.I ^ (2 * j + 1 + 1)).im / (((2 * j + 1 : ℕ) : ℝ) + 1) ^ 2 = 0 := by
  rw [I_pow_odd]
  have : ((-1 : ℂ) ^ (j + 1)).im = 0 := by
    rw [show ((-1 : ℂ) ^ (j + 1)) = (((-1 : ℝ) ^ (j + 1) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_im]
  rw [this, zero_div]

/-- `D(i)` is Catalan's constant. -/
theorem blochWigner_I : blochWigner Complex.I = catalanConstant := by
  rw [blochWigner_I_eq, dilogSeries_I_im]
  have hi1 : Function.Injective (fun j : ℕ ↦ 2 * j) := fun a b h ↦ by simp only at h; omega
  have hi2 : Function.Injective (fun j : ℕ ↦ 2 * j + 1) := fun a b h ↦ by simp only at h; omega
  set f : ℕ → ℝ := fun n ↦ (Complex.I ^ (n + 1)).im / ((n : ℝ) + 1) ^ 2 with hf
  have hfs : Summable f := summable_im_terms
  have he : Summable fun k ↦ f (2 * k) := hfs.comp_injective hi1
  have ho : Summable fun k ↦ f (2 * k + 1) := hfs.comp_injective hi2
  rw [← tsum_even_add_odd (f := f) he ho]
  have h1 : ∀ k : ℕ, f (2 * k) = (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2 := fun k ↦ even_term k
  have h2 : ∀ k : ℕ, f (2 * k + 1) = 0 := fun k ↦ odd_term k
  rw [tsum_congr h1, tsum_congr h2, tsum_zero, add_zero]
  rfl

end AJConjecture
