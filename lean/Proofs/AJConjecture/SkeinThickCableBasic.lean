import Mathlib
import AJConjecture.ColoredJones
import AJConjecture.SkeinThickCable

/-!
# Thick crossings and profile cables: bookkeeping

The cabled generator of `AJConjecture.cableGen` is the thick crossing of two bundles of the
same size, the cable with a constant profile is `AJConjecture.cable`, a thick crossing splits
along the first bundle as a concatenation of words, and the strand bookkeeping agrees with the
strand permutation of `AJConjecture.strandPerm`. All statements are about lists and finite sums.
-/

namespace AJConjecture

/-- The cabled generator is a thick crossing of two bundles of `c` strands. -/
theorem cableGen_eq_thickCross (c : ℕ) (g : ℕ × Bool) :
    cableGen c g = thickCross c c (c * g.1) g.2 := by
  obtain ⟨i, s⟩ := g
  cases s <;> rfl

/-- The cable with a constant profile is the blackboard cable. -/
theorem thickCable_const (c : ℕ) (w : BraidWord) : thickCable (fun _ ↦ c) w = cable c w := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    have hoff : profileOffset (fun _ ↦ c) g.1 = c * g.1 := by
      rw [profileOffset, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
    have hswap : profileSwap (fun _ ↦ c) g.1 = fun _ ↦ c := rfl
    rw [thickCable, hswap, ih, hoff, ← cableGen_eq_thickCross]
    rfl

/-- Splitting the first bundle: its last `a₂` strands cross first. -/
theorem thickGen_add_left (a₁ a₂ b off : ℕ) :
    thickGen (a₁ + a₂) b off true = thickGen a₂ b (off + a₁) true ++ thickGen a₁ b off true := by
  simp only [thickGen, ite_true, List.range_add, List.reverse_append, List.flatMap_append,
    ← List.map_reverse, List.flatMap_map, add_assoc]

/-- The top profile of a word is the bottom profile transported along the strands. -/
theorem profileEnd_strandEnd (κ : ℕ → ℕ) (w : BraidWord) (p : ℕ) :
    profileEnd κ w (strandEnd w p) = κ p := by
  induction w generalizing κ p with
  | nil => rfl
  | cons g w ih =>
    change profileEnd (profileSwap κ g.1) w (strandEnd w (Equiv.swap g.1 (g.1 + 1) p)) = κ p
    rw [ih, profileSwap, Equiv.swap_apply_self]

/-- The strand bookkeeping agrees with the strand permutation of the word: the strand that
starts in the column `p` ends in the column `(strandPerm m w)⁻¹ p`. -/
theorem strandEnd_eq_strandPerm_symm (m : ℕ) (w : BraidWord) (hw : IsOnStrands m w) (p : Fin m) :
    strandEnd w p = (((strandPerm m w)⁻¹ p : Fin m) : ℕ) := by
  induction w generalizing p with
  | nil => simp [strandEnd, strandPerm]
  | cons g w ih =>
    have hg : g.1 + 1 < m := hw g List.mem_cons_self
    have hperm : strandPerm m (g :: w) = strandSwap m g.1 * strandPerm m w := by
      rw [strandPerm, List.map_cons, List.prod_cons]
      rfl
    have hswap : Equiv.swap g.1 (g.1 + 1) (p : ℕ) = ((strandSwap m g.1 p : Fin m) : ℕ) := by
      rw [strandSwap, dite_eq_left hg, Equiv.swap_apply_def, Equiv.swap_apply_def]
      simp only [Fin.ext_iff]
      split_ifs <;> rfl
    have hinv : (strandSwap m g.1)⁻¹ = strandSwap m g.1 := by
      rw [strandSwap, dite_eq_left hg, Equiv.swap_inv]
    change strandEnd w (Equiv.swap g.1 (g.1 + 1) (p : ℕ)) = _
    rw [hswap, ih (fun h hh ↦ hw h (List.mem_cons_of_mem _ hh)), hperm, mul_inv_rev, hinv]
    rfl

end AJConjecture
