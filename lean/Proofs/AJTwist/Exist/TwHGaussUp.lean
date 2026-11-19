import Mathlib
import AJTwist.Exist.TwHGaussContig
import AJTwist.Exist.TwHSpanClosure

/-!
# One step of the window induction for the Gaussian periods: upwards

Let `h = |ℓ|`. In the contiguity relation `twHGauss_contiguity ℓ c` the four periods have
indices in an interval of `2h + 2` consecutive integers, and the periods at its two ends have
nonzero polynomial coefficients. Hence a period lies in a saturated span as soon as the `2h + 1`
periods just below it do (`twHSpan_gauss_up`); the downward step is in
`AJTwist.Exist.TwHGaussDown`.

At the index `e` (multiplier in brackets):
* `ℓ ≥ 1`, relation at `c = e - 2ℓ - 1`:
  `[q^e] 𝔊^(e) = -𝔊^(e-2ℓ-1) + q J 𝔊^(e-2ℓ) + q^e J 𝔊^(e-1)`;
* `ℓ ≤ -1`, relation at `c = e - 1`:
  `[q J] 𝔊^(e) = 𝔊^(e-1) - q^(2ℓ+e) J 𝔊^(e-1+2ℓ) + q^(2ℓ+e) 𝔊^(e+2ℓ)`;
* `ℓ = 0`, relation at `c = e - 1`: `[q J - q^e] 𝔊^(e) = (1 - q^e J) 𝔊^(e-1)`.

In each case the right-hand side lies in the span by `twHSpan_add`, `twHSpan_sub`,
`twHSpan_polyMul`, `twHSpan_constMul`, and `twHSpan_of_polyMul` removes the multiplier (the
polynomials `C a`, `C a * X`, `C a * X - C b` with `a ≠ 0` are nonzero). All indices on the
right lie in `[e - (2h + 1), e - 1]`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Membership in a saturated span from a three-term relation with a nonzero multiplier. -/
private theorem twHSpan_of_three_term_gaussUp {ι : Type*} [Fintype ι] {g : ι → ℕ → RatFunc ℚ}
    {y y₁ y₂ y₃ : ℕ → RatFunc ℚ} {f : (RatFunc ℚ)[X]} (f₁ f₂ f₃ : (RatFunc ℚ)[X]) (hf : f ≠ 0)
    (h₁ : TwHSpan g y₁) (h₂ : TwHSpan g y₂) (h₃ : TwHSpan g y₃)
    (he : ∀ j : ℕ, f.eval (qParam ^ j) * y j = f₁.eval (qParam ^ j) * y₁ j +
      f₂.eval (qParam ^ j) * y₂ j + f₃.eval (qParam ^ j) * y₃ j) : TwHSpan g y := by
  refine twHSpan_of_polyMul hf ?_
  rw [funext he]
  exact twHSpan_add (twHSpan_add (twHSpan_polyMul f₁ h₁) (twHSpan_polyMul f₂ h₂))
    (twHSpan_polyMul f₃ h₃)

/-- The polynomial `C a * X` is nonzero for `a ≠ 0`. -/
private theorem C_mul_X_ne_zero_gaussUp {a : RatFunc ℚ} (ha : a ≠ 0) :
    (C a * X : (RatFunc ℚ)[X]) ≠ 0 :=
  mul_ne_zero (C_ne_zero.mpr ha) X_ne_zero

/-- The polynomial `C a * X - C b` is nonzero for `a ≠ 0`. -/
private theorem C_mul_X_sub_C_ne_zero_gaussUp {a : RatFunc ℚ} (ha : a ≠ 0) (b : RatFunc ℚ) :
    (C a * X - C b : (RatFunc ℚ)[X]) ≠ 0 := by
  intro h0
  have h1 := congrArg (fun p : (RatFunc ℚ)[X] ↦ p.coeff 1) h0
  simp only [coeff_sub, coeff_C_mul, coeff_X_one, mul_one, coeff_C_succ, sub_zero,
    coeff_zero] at h1
  exact ha h1

/-- The upward step for a positive twist: the multiplier is `q^e`. -/
private theorem twHSpan_gauss_up_pos {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ)
    (ℓ e : ℤ) (hℓ : 1 ≤ ℓ)
    (h : ∀ c : ℤ, e - (2 * (ℓ.natAbs : ℤ) + 1) ≤ c → c ≤ e - 1 → TwHSpan g (twHGauss ℓ c)) :
    TwHSpan g (twHGauss ℓ e) := by
  have hh : (ℓ.natAbs : ℤ) = ℓ := Int.natAbs_of_nonneg (by omega)
  refine twHSpan_of_three_term_gaussUp (f := C (qParam ^ e)) (-1) (C qParam * X)
    (C (qParam ^ e) * X) (C_ne_zero.mpr (zpow_ne_zero _ qParam_ne_zero))
    (h (e - 2 * ℓ - 1) (by omega) (by omega)) (h (e - 2 * ℓ) (by omega) (by omega))
    (h (e - 1) (by omega) (by omega)) fun j ↦ ?_
  have hc := twHGauss_contiguity ℓ (e - 2 * ℓ - 1) j
  rw [show 1 + 2 * ℓ + (e - 2 * ℓ - 1) = e by ring,
    show e - 2 * ℓ - 1 + 2 * ℓ = e - 1 by ring, show e - 1 + 1 = e by ring,
    show e - 2 * ℓ - 1 + 1 = e - 2 * ℓ by ring] at hc
  simp only [eval_one, eval_mul, eval_C, eval_X, eval_neg]
  linear_combination hc

/-- The upward step for a negative twist: the multiplier is `q J`. -/
private theorem twHSpan_gauss_up_neg {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ)
    (ℓ e : ℤ) (hℓ : ℓ ≤ -1)
    (h : ∀ c : ℤ, e - (2 * (ℓ.natAbs : ℤ) + 1) ≤ c → c ≤ e - 1 → TwHSpan g (twHGauss ℓ c)) :
    TwHSpan g (twHGauss ℓ e) := by
  have hh : (ℓ.natAbs : ℤ) = -ℓ := Int.ofNat_natAbs_of_nonpos (by omega)
  refine twHSpan_of_three_term_gaussUp (f := C qParam * X) 1
    (-(C (qParam ^ (2 * ℓ + e)) * X)) (C (qParam ^ (2 * ℓ + e)))
    (C_mul_X_ne_zero_gaussUp qParam_ne_zero)
    (h (e - 1) (by omega) (by omega)) (h (e - 1 + 2 * ℓ) (by omega) (by omega))
    (h (e + 2 * ℓ) (by omega) (by omega)) fun j ↦ ?_
  have hc := twHGauss_contiguity ℓ (e - 1) j
  rw [show e - 1 + 2 * ℓ + 1 = e + 2 * ℓ by ring, show e - 1 + 1 = e by ring,
    show 1 + 2 * ℓ + (e - 1) = 2 * ℓ + e by ring] at hc
  simp only [eval_one, eval_mul, eval_C, eval_X, eval_neg]
  linear_combination -hc

/-- The upward step without twist: the multiplier is `q J - q^e`. -/
private theorem twHSpan_gauss_up_zero {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ)
    (e : ℤ) (h : TwHSpan g (twHGauss 0 (e - 1))) : TwHSpan g (twHGauss 0 e) := by
  refine twHSpan_of_three_term_gaussUp (f := C qParam * X - C (qParam ^ e))
    (1 - C (qParam ^ e) * X) 0 0 (C_mul_X_sub_C_ne_zero_gaussUp qParam_ne_zero _) h h h
    fun j ↦ ?_
  have hc := twHGauss_contiguity 0 (e - 1) j
  rw [show (1 : ℤ) + 2 * 0 + (e - 1) = e by ring, show e - 1 + 2 * 0 = e - 1 by ring,
    show e - 1 + 1 = e by ring] at hc
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, eval_zero]
  linear_combination -hc

/-- A period lies in a saturated span if the `2|ℓ| + 1` periods just below it do. -/
theorem twHSpan_gauss_up {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ) (ℓ e : ℤ)
    (h : ∀ c : ℤ, e - (2 * (ℓ.natAbs : ℤ) + 1) ≤ c → c ≤ e - 1 → TwHSpan g (twHGauss ℓ c)) :
    TwHSpan g (twHGauss ℓ e) := by
  rcases lt_trichotomy ℓ 0 with hℓ | rfl | hℓ
  · exact twHSpan_gauss_up_neg g ℓ e (by omega) h
  · exact twHSpan_gauss_up_zero g e (h (e - 1) (by omega) le_rfl)
  · exact twHSpan_gauss_up_pos g ℓ e (by omega) h

end AJConjecture
