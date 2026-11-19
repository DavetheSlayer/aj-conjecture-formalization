import Mathlib

/-!
# Polynomial interpolation in the colour

Let `T_j ∈ ℚ[x][[u]]` (`j ∈ ℕ`) be divisible by `u^j`, and suppose that at every integer colour
`n` the terms with `j ≥ |n| + c₀` vanish, so that `S(n) = ∑_{j < |n| + c₀} T_j(n) ∈ ℚ[[u]]` is a
finite sum. If `S(n) = 0` for all large `n`, then `S(n) = 0` for every integer `n`.

Proof. For each `r`, the coefficient of `u^r` in `S(n)` is `z_r(n)` with
`z_r = ∑_{j ≤ r} [u^r] T_j ∈ ℚ[x]`, the same polynomial for all `n` (terms with `j > r` have no
`u^r`, terms with `j ≥ |n| + c₀` vanish at `n`). A polynomial vanishing at infinitely many
integers is zero (`Polynomial.eq_zero_of_infinite_isRoot`). This is coefficientwise formal
convergence: no analytic limit or uniform estimate in the colour is used.
-/

open Polynomial

namespace AJConjecture

theorem sum_map_eval_eq_zero_of_eventually {T : ℕ → PowerSeries ℚ[X]} (c₀ : ℕ)
    (horder : ∀ j r : ℕ, r < j → PowerSeries.coeff r (T j) = 0)
    (hvanish : ∀ (n : ℤ) (j : ℕ), n.natAbs + c₀ ≤ j →
      (T j).map (Polynomial.evalRingHom (n : ℚ)) = 0)
    {n₀ : ℤ} (hzero : ∀ n : ℤ, n₀ ≤ n →
      ∑ j ∈ Finset.range (n.natAbs + c₀), (T j).map (Polynomial.evalRingHom (n : ℚ)) = 0)
    (n : ℤ) :
    ∑ j ∈ Finset.range (n.natAbs + c₀), (T j).map (Polynomial.evalRingHom (n : ℚ)) = 0 := by
  have hcoeff : ∀ (m : ℤ) (r : ℕ), PowerSeries.coeff r
      (∑ j ∈ Finset.range (m.natAbs + c₀), (T j).map (Polynomial.evalRingHom (m : ℚ))) =
        (∑ j ∈ Finset.range (r + 1), PowerSeries.coeff r (T j)).eval (m : ℚ) := by
    intro m r
    rw [map_sum, Polynomial.eval_finsetSum]
    simp only [PowerSeries.coeff_map, Polynomial.coe_evalRingHom]
    have hz : ∀ j, (r < j ∨ m.natAbs + c₀ ≤ j) →
        (PowerSeries.coeff r (T j)).eval (m : ℚ) = 0 := by
      rintro j (h | h)
      · rw [horder j r h, eval_zero]
      · simpa [PowerSeries.coeff_map] using congrArg (PowerSeries.coeff r) (hvanish m j h)
    rw [Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left (m.natAbs + c₀) (r + 1)))
        fun j hj hn ↦ hz j (Or.inr (by simp only [Finset.mem_range] at hj hn; omega)),
      Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right (m.natAbs + c₀) (r + 1)))
        fun j hj hn ↦ hz j (Or.inl (by simp only [Finset.mem_range] at hj hn; omega))]
  have hpoly : ∀ r : ℕ, ∑ j ∈ Finset.range (r + 1), PowerSeries.coeff r (T j) = 0 := by
    intro r
    refine Polynomial.eq_zero_of_infinite_isRoot _ <|
      Set.infinite_of_injective_forall_mem (f := fun k : ℕ ↦ ((n₀ + k : ℤ) : ℚ)) ?_ fun k ↦ ?_
    · intro a b h
      simpa using h
    · change IsRoot _ _
      rw [IsRoot, ← hcoeff, hzero _ (by omega), map_zero]
  ext r
  rw [hcoeff, hpoly, eval_zero, map_zero]

end AJConjecture
