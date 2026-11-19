import Mathlib
import AJTwist.Exist.TwHGaussContig
import AJTwist.Exist.TwHSpanClosure

/-!
# One step of the window induction for the Gaussian periods: downwards

Let `h = |ℓ|`. A Gaussian period lies in a saturated span as soon as the `2h + 1` periods just
above it do (`twHSpan_gauss_down`), by the contiguity relation `twHGauss_contiguity` solved for
the period of lowest index (the upward step is in `AJTwist.Exist.TwHGaussUp`).

At the index `e` (multiplier in brackets):
* `ℓ ≥ 1`, relation at `c = e`:
  `[1] 𝔊^(e) = q J 𝔊^(e+1) + q^(1+2ℓ+e) J 𝔊^(e+2ℓ) - q^(1+2ℓ+e) 𝔊^(e+2ℓ+1)`;
* `ℓ ≤ -1`, relation at `c = e - 2ℓ`:
  `[q^(1+e) J] 𝔊^(e) = 𝔊^(e-2ℓ) - q J 𝔊^(e-2ℓ+1) + q^(1+e) 𝔊^(e+1)`;
* `ℓ = 0`, relation at `c = e`: `[1 - q^(1+e) J] 𝔊^(e) = (q J - q^(1+e)) 𝔊^(e+1)`.

In each case the right-hand side lies in the span by `twHSpan_add`, `twHSpan_sub`,
`twHSpan_polyMul`, `twHSpan_constMul`, and `twHSpan_of_polyMul` removes the multiplier (the
polynomials `C a * X`, `1 - C a * X` with `a ≠ 0` are nonzero). All indices on the right lie
in `[e + 1, e + (2h + 1)]`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Membership in a saturated span from a three-term relation with a nonzero multiplier. -/
private theorem twHSpan_of_three_term_gaussDown {ι : Type*} [Fintype ι] {g : ι → ℕ → RatFunc ℚ}
    {y y₁ y₂ y₃ : ℕ → RatFunc ℚ} {f : (RatFunc ℚ)[X]} (f₁ f₂ f₃ : (RatFunc ℚ)[X]) (hf : f ≠ 0)
    (h₁ : TwHSpan g y₁) (h₂ : TwHSpan g y₂) (h₃ : TwHSpan g y₃)
    (he : ∀ j : ℕ, f.eval (qParam ^ j) * y j = f₁.eval (qParam ^ j) * y₁ j +
      f₂.eval (qParam ^ j) * y₂ j + f₃.eval (qParam ^ j) * y₃ j) : TwHSpan g y := by
  refine twHSpan_of_polyMul hf ?_
  rw [funext he]
  exact twHSpan_add (twHSpan_add (twHSpan_polyMul f₁ h₁) (twHSpan_polyMul f₂ h₂))
    (twHSpan_polyMul f₃ h₃)

/-- The polynomial `C a * X` is nonzero for `a ≠ 0`. -/
private theorem C_mul_X_ne_zero_gaussDown {a : RatFunc ℚ} (ha : a ≠ 0) :
    (C a * X : (RatFunc ℚ)[X]) ≠ 0 :=
  mul_ne_zero (C_ne_zero.mpr ha) X_ne_zero

/-- The polynomial `1 - C a * X` is nonzero. -/
private theorem one_sub_C_mul_X_ne_zero_gaussDown (a : RatFunc ℚ) :
    (1 - C a * X : (RatFunc ℚ)[X]) ≠ 0 := by
  intro h0
  have h1 := congrArg (eval 0) h0
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, mul_zero, sub_zero, eval_zero] at h1
  exact one_ne_zero h1

/-- The downward step for a positive twist: the multiplier is `1`. -/
private theorem twHSpan_gauss_down_pos {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ)
    (ℓ e : ℤ) (hℓ : 1 ≤ ℓ)
    (h : ∀ c : ℤ, e + 1 ≤ c → c ≤ e + (2 * (ℓ.natAbs : ℤ) + 1) → TwHSpan g (twHGauss ℓ c)) :
    TwHSpan g (twHGauss ℓ e) := by
  have hh : (ℓ.natAbs : ℤ) = ℓ := Int.natAbs_of_nonneg (by omega)
  refine twHSpan_of_three_term_gaussDown (f := 1) (C qParam * X)
    (C (qParam ^ (1 + 2 * ℓ + e)) * X) (-C (qParam ^ (1 + 2 * ℓ + e))) one_ne_zero
    (h (e + 1) (by omega) (by omega)) (h (e + 2 * ℓ) (by omega) (by omega))
    (h (e + 2 * ℓ + 1) (by omega) (by omega)) fun j ↦ ?_
  simp only [eval_one, eval_mul, eval_C, eval_X, eval_neg]
  linear_combination twHGauss_contiguity ℓ e j

/-- The downward step for a negative twist: the multiplier is `q^(1+e) J`. -/
private theorem twHSpan_gauss_down_neg {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ)
    (ℓ e : ℤ) (hℓ : ℓ ≤ -1)
    (h : ∀ c : ℤ, e + 1 ≤ c → c ≤ e + (2 * (ℓ.natAbs : ℤ) + 1) → TwHSpan g (twHGauss ℓ c)) :
    TwHSpan g (twHGauss ℓ e) := by
  have hh : (ℓ.natAbs : ℤ) = -ℓ := Int.ofNat_natAbs_of_nonpos (by omega)
  refine twHSpan_of_three_term_gaussDown (f := C (qParam ^ (1 + e)) * X) 1 (-(C qParam * X))
    (C (qParam ^ (1 + e))) (C_mul_X_ne_zero_gaussDown (zpow_ne_zero _ qParam_ne_zero))
    (h (e - 2 * ℓ) (by omega) (by omega)) (h (e - 2 * ℓ + 1) (by omega) (by omega))
    (h (e + 1) (by omega) (by omega)) fun j ↦ ?_
  have hc := twHGauss_contiguity ℓ (e - 2 * ℓ) j
  rw [show 1 + 2 * ℓ + (e - 2 * ℓ) = 1 + e by ring, show e - 2 * ℓ + 2 * ℓ = e by ring] at hc
  simp only [eval_one, eval_mul, eval_C, eval_X, eval_neg]
  linear_combination -hc

/-- The downward step without twist: the multiplier is `1 - q^(1+e) J`. -/
private theorem twHSpan_gauss_down_zero {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ)
    (e : ℤ) (h : TwHSpan g (twHGauss 0 (e + 1))) : TwHSpan g (twHGauss 0 e) := by
  refine twHSpan_of_three_term_gaussDown (f := 1 - C (qParam ^ (1 + e)) * X)
    (C qParam * X - C (qParam ^ (1 + e))) 0 0 (one_sub_C_mul_X_ne_zero_gaussDown _) h h h
    fun j ↦ ?_
  have hc := twHGauss_contiguity 0 e j
  rw [show (1 : ℤ) + 2 * 0 + e = 1 + e by ring, show e + 2 * 0 = e by ring] at hc
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, eval_zero]
  linear_combination hc

/-- A period lies in a saturated span if the `2|ℓ| + 1` periods just above it do. -/
theorem twHSpan_gauss_down {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ) (ℓ e : ℤ)
    (h : ∀ c : ℤ, e + 1 ≤ c → c ≤ e + (2 * (ℓ.natAbs : ℤ) + 1) → TwHSpan g (twHGauss ℓ c)) :
    TwHSpan g (twHGauss ℓ e) := by
  rcases lt_trichotomy ℓ 0 with hℓ | rfl | hℓ
  · exact twHSpan_gauss_down_neg g ℓ e (by omega) h
  · exact twHSpan_gauss_down_zero g e (h (e + 1) le_rfl (by omega))
  · exact twHSpan_gauss_down_pos g ℓ e (by omega) h

end AJConjecture
