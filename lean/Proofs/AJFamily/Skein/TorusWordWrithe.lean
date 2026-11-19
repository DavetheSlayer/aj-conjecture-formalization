import Mathlib
import AJConjecture.ColoredJones
import AJFamily.Skein.TorusWord

/-!
# The writhe of the family word

`writhe_whiteheadTorusWord`: the writhe is `4k`; the `4k + 2` bands (small climbs included) have
writhe `1` each and the two Hopf letters `-1` each.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The writhe of a concatenation. -/
private theorem writhe_append_torus (u v : BraidWord) : writhe (u ++ v) = writhe u + writhe v := by
  simp [writhe, List.map_append, List.sum_append]

/-- A run of positive letters has writhe its length. -/
private theorem writhe_map_true (n : ℕ) (f : ℕ → ℕ) :
    writhe ((List.range n).map fun x ↦ (f x, true)) = n := by
  simp [writhe, List.map_map, Function.comp_def]

/-- A run of negative letters has writhe minus its length. -/
private theorem writhe_map_false (n : ℕ) (f : ℕ → ℕ) :
    writhe ((List.range n).map fun x ↦ (f x, false)) = -n := by
  simp [writhe, List.map_map, Function.comp_def]

/-- A band has writhe `1`. -/
private theorem writhe_surfaceBand (i j : ℕ) : writhe (surfaceBand i j) = 1 := by
  rw [surfaceBand, writhe_append_torus, writhe_append_torus, writhe_map_true, writhe_map_false]
  simp [writhe]

/-- A sequence of bands has writhe the number of bands. -/
private theorem writhe_flatMap_surfaceBand (n : ℕ) (f g : ℕ → ℕ) :
    writhe ((List.range n).flatMap fun s ↦ surfaceBand (f s) (g s)) = n := by
  induction n with
  | zero => simp [writhe]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, writhe_append_torus, ih]
    simp [writhe_surfaceBand]

theorem writhe_whiteheadTorusWord (k : ℕ) (hk : 1 ≤ k) :
    writhe (whiteheadTorusWord k) = 4 * k := by
  rw [whiteheadTorusWord]
  simp only [writhe_append_torus, writhe_map_true, writhe_surfaceBand,
    writhe_flatMap_surfaceBand]
  have h1 : writhe [(4 * k + 1, false)] = -1 := by simp [writhe]
  rw [h1]
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
  ring

end AJConjecture
