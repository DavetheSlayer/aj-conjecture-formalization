import Mathlib
import AJConjecture.SkeinThickCable

/-!
# Thickness profiles: offsets, shifts and locality

A thick crossing at a shifted position is the shifted word; the cable of a word on `m` strands
depends only on the thicknesses of the columns `< m`; the offset of a column plus its thickness
is at most the total thickness; and a word on `m` strands permutes the thicknesses of the
columns `< m`, so that the total thickness is the same at the top and at the bottom. All
statements are about lists and finite sums.
-/

namespace AJConjecture

/-- A thick crossing at a shifted position is the shifted word. -/
theorem thickCross_add_off (a b off d : ℕ) (s : Bool) :
    thickCross a b (off + d) s = (thickCross a b off s).map fun g ↦ (g.1 + d, g.2) := by
  cases s
  · simp only [thickCross, thickGen, Bool.false_eq_true, ite_false, List.map_flatMap,
      List.map_map, Function.comp_def]
    simp only [add_right_comm _ d]
  · simp only [thickCross, thickGen, ite_true, List.map_flatMap, List.map_map,
      Function.comp_def]
    simp only [add_right_comm _ d]

/-- The profile cable of a word on `m` strands depends only on the columns `< m`. -/
theorem thickCable_congr (m : ℕ) (κ κ' : ℕ → ℕ) (w : BraidWord) (hw : IsOnStrands m w)
    (h : ∀ x < m, κ x = κ' x) : thickCable κ w = thickCable κ' w := by
  induction w generalizing κ κ' with
  | nil => rfl
  | cons g w ih =>
    have hg : g.1 + 1 < m := hw g List.mem_cons_self
    have hoff : profileOffset κ g.1 = profileOffset κ' g.1 :=
      Finset.sum_congr rfl fun y hy ↦ h y (by have := Finset.mem_range.mp hy; omega)
    have hswap : ∀ x < m, profileSwap κ g.1 x = profileSwap κ' g.1 x := by
      intro x hx
      refine h _ ?_
      rw [Equiv.swap_apply_def]
      split_ifs <;> omega
    rw [thickCable, thickCable, h g.1 (by omega), h (g.1 + 1) hg, hoff,
      ih _ _ (fun g' hg' ↦ hw g' (List.mem_cons_of_mem _ hg')) hswap]

/-- A column ends before the total thickness. -/
theorem profileOffset_add_le (κ : ℕ → ℕ) (p m : ℕ) (hp : p < m) :
    profileOffset κ p + κ p ≤ profileOffset κ m := by
  have h1 : profileOffset κ p + κ p = profileOffset κ (p + 1) := by
    rw [profileOffset, profileOffset, Finset.sum_range_succ]
  rw [h1]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

end AJConjecture
