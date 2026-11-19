import Mathlib
import AJConjecture.WitnessPolynomials
import AJFamily.Classical.FamilyEval

/-!
# A zero of the extra factor off the bound

The point `(M, L) = (2, (1 + √-63)/2)` is a zero of `extraFactor` at which `(L - 1) B_m` does not
vanish for any `m ≥ 1`. In particular the bound `famBound m` is a nonzero polynomial.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- At a point `(2, L)` with `L² - L + 16 = 0`, the value of `B_{n+1}` is
`(-k)^n ((n + 1) A + n k)`, where `A`, `k` are the values of `famA`, `famK`. -/
private theorem evalPoint_famB_two_of_quadratic_root (n : ℕ) (L : ℂ)
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
private theorem evalPoint_famB_two_ne_zero (n : ℕ) (L : ℂ) (hL : L ^ 2 - L + 16 = 0) :
    evalPoint (mapC (famB (n + 1))) (2, L) ≠ 0 := by
  rw [evalPoint_famB_two_of_quadratic_root n L hL]
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

/-- Some zero of the extra factor `E` is not a zero of the bound `(L - 1) B_m`. -/
theorem exists_extraFactor_zero_not_famBound_zero {m : ℕ} (hm : 0 < m) :
    ∃ p : ℂ × ℂ, evalPoint (mapC extraFactor) p = 0 ∧ evalPoint (mapC (famBound m)) p ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = -63 := IsAlgClosed.exists_pow_nat_eq (-63) (by norm_num)
  have hL : ((1 + s) / 2) ^ 2 - (1 + s) / 2 + 16 = 0 := by linear_combination (1 / 4 : ℂ) * hs
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine ⟨(2, (1 + s) / 2), ?_, ?_⟩
  · simp only [mapC, evalPoint, extraFactor, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom,
      Polynomial.map_sub, Polynomial.map_one, Polynomial.map_ofNat, eval₂_add, eval₂_sub,
      eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, Polynomial.coe_evalRingHom, eval_add, eval_mul,
      eval_pow, eval_X, eval_sub, eval_one, eval_ofNat]
    linear_combination hL
  · have hmul : evalPoint (mapC (famBound (n + 1))) (2, (1 + s) / 2) =
        ((1 + s) / 2 - 1) * evalPoint (mapC (famB (n + 1))) (2, (1 + s) / 2) := by
      simp only [mapC, evalPoint, famBound, Polynomial.map_mul, Polynomial.map_sub,
        Polynomial.map_X, Polynomial.map_one, eval₂_mul, eval₂_sub, eval₂_X, eval₂_one]
    rw [hmul]
    refine mul_ne_zero (fun h1 ↦ ?_) (evalPoint_famB_two_ne_zero n _ hL)
    have h16 : (16 : ℂ) = 0 := by
      linear_combination hL - ((1 + s) / 2) * h1
    norm_num at h16

/-- The bound `(L - 1) B_m` is a nonzero polynomial. -/
theorem famBound_ne_zero {m : ℕ} (hm : 0 < m) : famBound m ≠ 0 := by
  intro h
  obtain ⟨p, -, hp⟩ := exists_extraFactor_zero_not_famBound_zero hm
  apply hp
  simp only [h, mapC, Polynomial.map_zero, evalPoint, eval₂_zero]

end AJConjecture
