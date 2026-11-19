import Mathlib
import AJFamily.Classical.FamilyPoint
import AJTwist.Classical.TwCPolysCheb

/-!
# `C_b` does not vanish at the witness point of `E`

Source: revision 5, Section 7.3 (`classical.tex`, eq. (allcresultant)): on `E = 0` the norm of
`T_(-k)` is `1 + k(2k-1)(K+2) ≠ 0`. As for `B_k`, one point replaces the resultant.

At `M = 2` and a root `L` of `E(2, L) = L² - L + 16`: `k = 4 (4 + L)² = 36 L`, `τ = -2k`,
`A = -(240 + 141 L)`, so by `evalPoint_twistPolyNeg_mul` and `homCheb_of_eq_neg_two`
`C_b(2, L) (4 + L) = -(-k)^(b-1) ((b + 1) k + b A) = (-k)^(b-1) (240 b - (36 - 105 b) L)`.
The factors are nonzero: `4 + L = 0` or `k = 0` would give `36 = 0`, and
`240 b = (36 - 105 b) L` is impossible because `L` is not real (`L² - L + 16 = 0`; argue as in
the proof of `evalPoint_famB_two_ne_zero`, `AJFamily.Classical.FamilyPoint`, with the norm form
`16 y² + x y + x²` of `x + y L`).

Checked exactly for `b ≤ 4` (`SCR/C/py/v7_resultants.py`): `C_b(4, L) mod E` is
`L + 64`, `-216 (25 L - 16)`, `1296 (59 L - 3760)`, `2985984 (79 L + 16)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- With `τ = -2k` the Chebyshev combination of `C_(n+1)` is
`-(-k)^n ((n + 2) k + (n + 1) A)`. -/
private theorem cheb_combination_twCWitnessNeg (τ k A : ℂ) (hτ : τ = -2 * k) (n : ℕ) :
    (τ - A) * homCheb τ k (n + 1) - k ^ 2 * homCheb τ k n =
      -(-k) ^ n * (((n : ℂ) + 2) * k + ((n : ℂ) + 1) * A) := by
  rcases n with _ | m
  · simp only [homCheb, mul_one, mul_zero, sub_zero, pow_zero, CharP.cast_eq_zero, zero_add]
    rw [hτ]
    ring
  · rw [homCheb_of_eq_neg_two _ _ hτ (m + 1), homCheb_of_eq_neg_two _ _ hτ m, hτ]
    push_cast
    ring

/-- At a root `L` of `L² - L + 16 = E(2, L)`, `C_b(2, L) ≠ 0`. -/
theorem evalPoint_twistPolyNeg_witness_ne_zero (L : ℂ) (hL : L ^ 2 - L + 16 = 0) (b : ℕ)
    (hb : 1 ≤ b) : evalPoint (mapC (twistPolyNeg b)) (2, L) ≠ 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  intro h0
  have hk : evalPoint (mapC famK) (2, L) = 36 * L := by
    rw [evalPoint_famK]
    linear_combination 4 * hL
  have hτ : evalPoint (mapC famTau) (2, L) = -2 * evalPoint (mapC famK) (2, L) := by
    rw [evalPoint_famTau, evalPoint_famK]
    linear_combination 25 * hL
  have hA : evalPoint (mapC famA) (2, L) = -(240 + 141 * L) := by
    rw [evalPoint_famA]
    linear_combination 16 * hL
  have hmul := evalPoint_twistPolyNeg_mul (n + 1) hb 2 L
  rw [h0, zero_mul, Nat.add_sub_cancel, cheb_combination_twCWitnessNeg _ _ _ hτ n, hk, hA] at hmul
  have hL0 : L ≠ 0 := by
    rintro rfl
    norm_num at hL
  have hw : 240 * ((n : ℂ) + 1) + (105 * n + 69) * L = 0 := by
    have h1 := (mul_eq_zero.mp hmul.symm).resolve_left
      (neg_ne_zero.mpr (pow_ne_zero _ (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hL0))))
    linear_combination -h1
  have hnorm : ((16 * (105 * n + 69) ^ 2 + (240 * (n + 1)) ^ 2
      + 240 * (n + 1) * (105 * n + 69) : ℕ) : ℂ) = 0 := by
    push_cast
    linear_combination (105 * (n : ℂ) + 69) ^ 2 * hL
      - ((105 * (n : ℂ) + 69) * L - 240 * (n + 1) - (105 * n + 69)) * hw
  rw [Nat.cast_eq_zero] at hnorm
  exact absurd hnorm (Nat.pos_iff_ne_zero.mp (by positivity))

end AJConjecture
