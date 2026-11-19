import Mathlib
import AJFamily.Classical.FamilyPoint
import AJTwist.Classical.TwCPolys

/-!
# `B_k` does not vanish at the witness point of `E`

Source: revision 5, Section 7.3 (`classical.tex`, "The resultants with `E`"): on `E = 0` one has
`Z = -2` and `T_k = (-1)^k (2k + 1 - k e)`, whose norm is `1 + k(2k+1)(K+2) ≠ 0`
(eq. (allbresultant)). The library replaces the resultant by one point: at `M = 2`,
`E(2, L) = L² - L + 16`, and at its roots `B_(n+1)(2, L) = (-k)^n ((n+1) A + n k) ≠ 0`.

`evalPoint_twistPoly_witness_ne_zero` restates, for an explicit point and for `twistPoly`, the
private `evalPoint_famB_two_ne_zero` of `AJFamily.Classical.FamilyPoint` (copy its proof and
its helper `evalPoint_famB_two_of_quadratic_root`; then `famB_eq_twistPoly`). The explicit point
is needed because the bound of the twisted families has two varying factors, which must be
nonzero at the same zero of `E`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- At a point `(2, L)` with `L² - L + 16 = 0`, the value of `B_{n+1}` is
`(-k)^n ((n + 1) A + n k)`, where `A`, `k` are the values of `famA`, `famK`. -/
private theorem evalPoint_famB_two_of_root_twCWitnessPos (n : ℕ) (L : ℂ)
    (hL : L ^ 2 - L + 16 = 0) :
    evalPoint (mapC (famB (n + 1))) (2, L) =
      (-evalPoint (mapC famK) (2, L)) ^ n *
        ((n + 1 : ℂ) * evalPoint (mapC famA) (2, L) + n * evalPoint (mapC famK) (2, L)) := by
  have hτ : evalPoint (mapC famTau) (2, L) = -2 * evalPoint (mapC famK) (2, L) := by
    rw [evalPoint_famTau, evalPoint_famK]
    linear_combination 25 * hL
  rw [evalPoint_famB, homCheb_of_eq_neg_two _ _ hτ, Nat.add_sub_cancel]
  rcases n with _ | n
  · simp [homCheb]
  · rw [homCheb_of_eq_neg_two _ _ hτ]
    push_cast
    ring

/-- At a root of `L² - L + 16`, the value of `B_{n+1}` at `(2, L)` is nonzero. -/
private theorem evalPoint_famB_two_ne_zero_twCWitnessPos (n : ℕ) (L : ℂ)
    (hL : L ^ 2 - L + 16 = 0) : evalPoint (mapC (famB (n + 1))) (2, L) ≠ 0 := by
  rw [evalPoint_famB_two_of_root_twCWitnessPos n L hL]
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr fun hk ↦ ?_)) fun h0 ↦ ?_
  · rw [evalPoint_famK] at hk
    have h4 : (2 : ℂ) ^ 2 + L = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp
      ((mul_eq_zero.mp hk).resolve_left (by norm_num))
    have h36 : (36 : ℂ) = 0 := by linear_combination hL - (L - 5) * h4
    norm_num at h36
  · rw [evalPoint_famA, evalPoint_famK] at h0
    have hw : 240 * ((n : ℂ) + 1) + (105 * n + 141) * L = 0 := by
      linear_combination -h0 + (((n : ℂ) + 1) * 16 + 4 * n) * hL
    have hnorm : ((16 * (105 * n + 141) ^ 2 + (240 * (n + 1)) ^ 2
        + 240 * (n + 1) * (105 * n + 141) : ℕ) : ℂ) = 0 := by
      push_cast
      linear_combination (105 * (n : ℂ) + 141) ^ 2 * hL
        - ((105 * (n : ℂ) + 141) * L - 240 * (n + 1) - (105 * n + 141)) * hw
    rw [Nat.cast_eq_zero] at hnorm
    exact absurd hnorm (Nat.pos_iff_ne_zero.mp (by positivity))

/-- At a root `L` of `L² - L + 16 = E(2, L)`, `B_(n+1)(2, L) ≠ 0`. -/
theorem evalPoint_twistPoly_witness_ne_zero (L : ℂ) (hL : L ^ 2 - L + 16 = 0) (n : ℕ) :
    evalPoint (mapC (twistPoly (n + 1))) (2, L) ≠ 0 := by
  rw [← famB_eq_twistPoly (n + 1) (by omega)]
  exact evalPoint_famB_two_ne_zero_twCWitnessPos n L hL

end AJConjecture
