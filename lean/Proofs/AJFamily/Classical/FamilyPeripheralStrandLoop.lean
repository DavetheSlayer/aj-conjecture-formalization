import Mathlib
import AJFamily.Classical.FamilyPeripheralStrandPerm

/-!
# The strand loops of the family word

The loop collected by each strand of the family block list, in terms of the block loops
`L r = loopAt (4k+3) (famBlocks k) f r`, is `famStrandLoop k L t` (`stLoop_famBlocks`), and the
product of the strand loops along the orbit of `0` is `famOrbitLoop k L`
(`orbitLoop_famBlocks`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The strand loops of the last three blocks, in terms of the loops of the family block
list. -/
private theorem stLoop_famTop_strandL (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) (t : ℕ) :
    stLoop (4 * k + 3) (famTop k)
        (runTop (4 * k + 3) (famClimbs k ++ famMid k ++ famStair k) f) t =
      if t = 4 * k + 1 then loopAt (4 * k + 3) (famBlocks k) f (4 * k + 3)
      else if t = 4 * k + 2 ∨ t = 2 * k + 1 then
        loopAt (4 * k + 3) (famBlocks k) f (4 * k + 2) *
          loopAt (4 * k + 3) (famBlocks k) f (4 * k + 1)
      else if 2 * k + 2 ≤ t ∧ t ≤ 4 * k then loopAt (4 * k + 3) (famBlocks k) f (4 * k + 2)
      else if 1 ≤ t ∧ t ≤ 2 * k - 1 then loopAt (4 * k + 3) (famBlocks k) f (4 * k + 1)
      else 1 := by
  rw [stLoop_famTop k hk, ← loopAt_famBlocks_top k hk f 0, ← loopAt_famBlocks_top k hk f 1,
    ← loopAt_famBlocks_top k hk f 2]

/-- The strand loops of the staircase, in terms of the loops of the family block list. -/
private theorem stLoop_famStair_strandL (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G)
    (t : ℕ) :
    stLoop (4 * k + 3) (famStair k) (runTop (4 * k + 3) (famClimbs k ++ famMid k) f) t =
      if t = 2 * k then
        ((List.range (k - 1)).reverse.map fun r ↦
          loopAt (4 * k + 3) (famBlocks k) f (2 * k + 3 + 2 * r)).prod
      else if t = 2 * k + 1 then
        ((List.range k).reverse.map fun r ↦
          loopAt (4 * k + 3) (famBlocks k) f (2 * k + 2 + 2 * r)).prod
      else if 2 * k + 2 ≤ t ∧ t ≤ 4 * k then
        loopAt (4 * k + 3) (famBlocks k) f (2 * k + 2 + (4 * k - t))
      else 1 := by
  rw [stLoop_famStair k hk]
  split_ifs with h1 h2 h3
  · refine congrArg List.prod (List.map_congr_left fun r hr ↦ ?_)
    have hr' := List.mem_range.1 (List.mem_reverse.1 hr)
    rw [← loopAt_famBlocks_stair k hk f _ (by omega), show 2 * k + 2 + (2 * r + 1) =
      2 * k + 3 + 2 * r by omega]
  · refine congrArg List.prod (List.map_congr_left fun r hr ↦ ?_)
    have hr' := List.mem_range.1 (List.mem_reverse.1 hr)
    rw [← loopAt_famBlocks_stair k hk f _ (by omega)]
  · rw [← loopAt_famBlocks_stair k hk f _ (by omega)]
  · rfl

/-- The strand loops of the middle blocks, in terms of the loops of the family block list. -/
private theorem stLoop_famMid_strandL (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) (t : ℕ) :
    stLoop (4 * k + 3) (famMid k) (runTop (4 * k + 3) (famClimbs k) f) t =
      if t = 4 * k + 1 then loopAt (4 * k + 3) (famBlocks k) f (2 * k + 1)
      else if t = 4 * k + 2 ∨ t = 4 * k then
        loopAt (4 * k + 3) (famBlocks k) f (2 * k) *
          loopAt (4 * k + 3) (famBlocks k) f (2 * k - 1)
      else if 2 * k ≤ t ∧ t ≤ 4 * k - 2 then loopAt (4 * k + 3) (famBlocks k) f (2 * k - 1)
      else 1 := by
  rw [stLoop_famMid k hk, ← loopAt_famBlocks_mid k hk f 0 (by norm_num),
    ← loopAt_famBlocks_mid k hk f 1 (by norm_num), ← loopAt_famBlocks_mid k hk f 2 (by norm_num),
    Nat.add_zero (2 * k - 1), show 2 * k - 1 + 1 = 2 * k by omega, show 2 * k - 1 + 2 = 2 * k + 1 by omega]

/-- The strand loops of the climbs, in terms of the loops of the family block list. -/
private theorem stLoop_famClimbs_strandL (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G)
    (t : ℕ) :
    stLoop (4 * k + 3) (famClimbs k) f t =
      if t = 2 * k - 1 then
        ((List.range (2 * k - 1)).reverse.map (loopAt (4 * k + 3) (famBlocks k) f)).prod
      else 1 := by
  rw [stLoop_famClimbs k hk]
  split_ifs
  · refine congrArg List.prod (List.map_congr_left fun r hr ↦ ?_)
    exact (loopAt_famBlocks_climb k hk f r (List.mem_range.1 (List.mem_reverse.1 hr))).symm
  · rfl

theorem stLoop_famBlocks (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) (t : ℕ)
    (ht : t < 4 * k + 3) :
    stLoop (4 * k + 3) (famBlocks k) f t =
      famStrandLoop k (loopAt (4 * k + 3) (famBlocks k) f) t := by
  rw [famBlocks, stLoop_append, stLoop_append, stLoop_append, stLoop_famTop_strandL k hk,
    stLoop_famStair_strandL k hk, stLoop_famMid_strandL k hk, stLoop_famClimbs_strandL k hk,
    ← famBlocks]
  have e1 := stPerm_famTop k t hk
  generalize stPerm (famTop k) t = x1 at e1 ⊢
  have e2 := stPerm_famStair k x1 hk
  generalize stPerm (famStair k) x1 = x2 at e2 ⊢
  have e3 := stPerm_famMid k x2 hk
  generalize stPerm (famMid k) x2 = x3 at e3 ⊢
  generalize loopAt (4 * k + 3) (famBlocks k) f = L
  have hreg : t = 0 ∨ (1 ≤ t ∧ t < 2 * k - 1) ∨ t = 2 * k - 1 ∨ t = 2 * k ∨ t = 2 * k + 1 ∨
      (2 * k + 2 ≤ t ∧ t ≤ 4 * k) ∨ t = 4 * k + 1 ∨ t = 4 * k + 2 := by omega
  unfold famStrandLoop
  rcases hreg with h | h | h | h | h | h | h | h <;>
  · simp (disch := omega) only [ite_eq_left, ite_eq_right] at e1
    subst e1
    simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte] at e2
    subst e2
    simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte] at e3
    subst e3
    simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte, true_or, or_true,
      mul_one, one_mul, mul_assoc]

theorem orbitLoop_famBlocks (k : ℕ) (hk : 1 ≤ k) (f : Fin (4 * k + 3) → G) :
    orbitLoop (4 * k + 3) (famBlocks k) f = famOrbitLoop k (loopAt (4 * k + 3) (famBlocks k) f) := by
  rw [orbitLoop, famOrbitLoop]
  refine congrArg List.prod (List.map_congr_left fun j hj ↦ ?_)
  rw [iterate_stPerm_famBlocks k hk j (by simp only [List.mem_range] at hj; omega),
    stLoop_famBlocks k hk f _ (famCycle_lt k j)]

end AJConjecture
