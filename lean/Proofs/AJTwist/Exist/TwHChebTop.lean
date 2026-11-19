import Mathlib
import AJTwist.Quantum.TwQDefect
import AJTwist.Exist.TwHSpanClosure

/-!
# The top trace operator of the inner equation

Source: revision 5, Section 3.2 (`transfer.tex`), eq. (innerforcing):
`p_a = S_(a-1)(𝒵) + (1 - qJ) S_a(𝒵) - qJ S_(a+1)(𝒵)` for every integer `a`, with
`S_(-k) = q^k S_k`. As a polynomial in the step operator `V = 𝒵` (library `cycloStep`,
`S_k(V) = cycloCheb k`) it has degree `|a| + 1`, and its top coefficient in the basis of the
trace operators is readable from the three shapes of `twDefect` (`twDefect_natCast`,
`twDefect_zero`, `twDefect_neg_natCast`), with `D = pairQCycloCoeff u`, `e = twDefect a u`:

* `a = m ≥ 1`: `q J · S_(m+1) D = S_(m-1) D + (1 - qJ) S_m D - e`;
* `a = 0`: `q (1 - J) · S_1 D = e - (1 - qJ) S_0 D` (the multiplier vanishes at `j = 0`);
* `a = -b ≤ -1`: `q^(b+1) · S_(b+1) D = e - q^b (1 - qJ) S_b D + q^b J S_(b-1) D`.

So in a saturated span that contains the lower trace operators `S_i D`, `i ≤ |a|`, and the
right-hand side `e` of the inner equation, the top one `S_(|a|+1) D` lies as well
(`twHSpan_cheb_top`; closure lemmas of `TwHSpanClosure`, then `twHSpan_of_polyMul` with the
multiplier `C q * X`, `C q * (1 - X)`, `C (q^(b+1))`).

The three shapes were checked in exact arithmetic for `-4 ≤ a ≤ 4` on random sequences
(scratch `H/h01_basic.py`, item (e)).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Membership in a saturated span from a three-term relation with a nonzero multiplier. -/
private theorem twHSpan_of_three_term_chebTop {ι : Type*} [Fintype ι] {g : ι → ℕ → RatFunc ℚ}
    {y y₁ y₂ y₃ : ℕ → RatFunc ℚ} {f : (RatFunc ℚ)[X]} (f₁ f₂ f₃ : (RatFunc ℚ)[X]) (hf : f ≠ 0)
    (h₁ : TwHSpan g y₁) (h₂ : TwHSpan g y₂) (h₃ : TwHSpan g y₃)
    (he : ∀ j : ℕ, f.eval (qParam ^ j) * y j = f₁.eval (qParam ^ j) * y₁ j +
      f₂.eval (qParam ^ j) * y₂ j + f₃.eval (qParam ^ j) * y₃ j) : TwHSpan g y := by
  refine twHSpan_of_polyMul hf ?_
  rw [funext he]
  exact twHSpan_add (twHSpan_add (twHSpan_polyMul f₁ h₁) (twHSpan_polyMul f₂ h₂))
    (twHSpan_polyMul f₃ h₃)

/-- The top trace operator for a positive index `a = m`. -/
theorem twHSpan_cheb_top_pos {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ) (m : ℕ)
    (hm : 1 ≤ m) (u : ℕ → RatFunc ℚ)
    (h0 : TwHSpan g (cycloCheb (m - 1) (pairQCycloCoeff u)))
    (h1 : TwHSpan g (cycloCheb m (pairQCycloCoeff u)))
    (hdef : TwHSpan g (twDefect (m : ℤ) u)) :
    TwHSpan g (cycloCheb (m + 1) (pairQCycloCoeff u)) := by
  refine twHSpan_of_three_term_chebTop (f := C qParam * X) 1 (1 - C qParam * X) (-1)
    (mul_ne_zero (C_ne_zero.mpr qParam_ne_zero) X_ne_zero) h0 h1 hdef fun j ↦ ?_
  have hd : twDefect (m : ℤ) u j = pairQCycloDefect m u j := by rw [twDefect_natCast m hm u]
  rw [pairQCycloDefect] at hd
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, eval_neg]
  linear_combination hd

/-- The top trace operator for the index `a = 0`: `q (1 - J) V D = e - (1 - qJ) S_0 D`. -/
theorem twHSpan_cheb_top_zero {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ)
    (u : ℕ → RatFunc ℚ) (h0 : TwHSpan g (cycloCheb 0 (pairQCycloCoeff u)))
    (hdef : TwHSpan g (twDefect 0 u)) :
    TwHSpan g (cycloCheb 1 (pairQCycloCoeff u)) := by
  have hne : (C qParam * (1 - X) : (RatFunc ℚ)[X]) ≠ 0 := by
    refine mul_ne_zero (C_ne_zero.mpr qParam_ne_zero) fun h ↦ ?_
    have h1 := congrArg (eval (0 : RatFunc ℚ)) h
    rw [eval_sub, eval_one, eval_X, eval_zero, sub_zero] at h1
    exact one_ne_zero h1
  refine twHSpan_of_three_term_chebTop (f := C qParam * (1 - X)) 1 (-(1 - C qParam * X)) 0
    hne hdef h0 h0 fun j ↦ ?_
  have hd := twDefect_zero u j
  have h1 : cycloCheb 1 (pairQCycloCoeff u) j = cycloStep (pairQCycloCoeff u) j := rfl
  have h2 : cycloCheb 0 (pairQCycloCoeff u) j = 2 * pairQCycloCoeff u j := rfl
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, eval_neg, eval_zero]
  rw [h1, h2]
  linear_combination -hd

/-- The top trace operator for a negative index `a = -b`. -/
theorem twHSpan_cheb_top_neg {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ) (b : ℕ)
    (hb : 1 ≤ b) (u : ℕ → RatFunc ℚ)
    (h0 : TwHSpan g (cycloCheb (b - 1) (pairQCycloCoeff u)))
    (h1 : TwHSpan g (cycloCheb b (pairQCycloCoeff u)))
    (hdef : TwHSpan g (twDefect (-(b : ℤ)) u)) :
    TwHSpan g (cycloCheb (b + 1) (pairQCycloCoeff u)) := by
  refine twHSpan_of_three_term_chebTop (f := C (qParam ^ (b + 1))) 1
    (-(C (qParam ^ b) * (1 - C qParam * X))) (C (qParam ^ b) * X)
    (C_ne_zero.mpr (pow_ne_zero _ qParam_ne_zero)) hdef h1 h0 fun j ↦ ?_
  have hd := twDefect_neg_natCast b hb u j
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, eval_neg]
  linear_combination -hd

/-- In a saturated span that contains `S_i(V) D` for `i ≤ |a|` and the right-hand side
`p_a D` of the inner equation, the top trace operator `S_(|a|+1)(V) D` lies as well. -/
theorem twHSpan_cheb_top {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ) (a : ℤ)
    (u : ℕ → RatFunc ℚ)
    (hlow : ∀ i : ℕ, i ≤ a.natAbs → TwHSpan g (cycloCheb i (pairQCycloCoeff u)))
    (hdef : TwHSpan g (twDefect a u)) :
    TwHSpan g (cycloCheb (a.natAbs + 1) (pairQCycloCoeff u)) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have hb : a = -((a.natAbs : ℕ) : ℤ) := by omega
    rw [hb] at hdef
    exact twHSpan_cheb_top_neg g a.natAbs (by omega) u (hlow _ (Nat.sub_le _ _))
      (hlow _ le_rfl) hdef
  · exact twHSpan_cheb_top_zero g u (hlow 0 le_rfl) hdef
  · have hb : a = ((a.natAbs : ℕ) : ℤ) := by omega
    rw [hb] at hdef
    exact twHSpan_cheb_top_pos g a.natAbs (by omega) u (hlow _ (Nat.sub_le _ _))
      (hlow _ le_rfl) hdef

end AJConjecture
