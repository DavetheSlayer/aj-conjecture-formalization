import Mathlib
import AJFamily.Classical.FamilyPeripheralAlgebra
import AJFamily.Classical.FamilyPeripheralLongitude
import AJFamily.Classical.FamilyPeripheralPhaseOuter
import AJFamily.Classical.FamilyPeripheralPhaseStair
import AJFamily.Skein.TorusWordPerm

/-!
# The strand permutation of the family word

The strand permutation of the family block list is `whiteheadTorusPermNat k`, the orbit of the
strand `0` is enumerated by `famCycle k` and closes after `4k+3` steps, and the meridian counts
`famCount k` sum to `4k` along the orbit (`orbitCount_famBlocks`).
-/

namespace AJConjecture

/-- The meridian counts of the strands of the family word. -/
def famCount (k t : ℕ) : ℤ :=
  if t = 2 * k then -1
  else if 2 * k + 1 ≤ t ∧ t ≤ 4 * k then 1
  else if t = 4 * k + 2 then ((2 * k + 1 : ℕ) : ℤ)
  else 0

theorem stPerm_famBlocks (k : ℕ) (hk : 1 ≤ k) (t : ℕ) (ht : t < 4 * k + 3) :
    stPerm (famBlocks k) t = whiteheadTorusPermNat k t := by
  rw [famBlocks, stPerm_append, stPerm_append, stPerm_append]
  have e1 := stPerm_famTop k t hk
  generalize stPerm (famTop k) t = x1 at e1 ⊢
  have e2 := stPerm_famStair k x1 hk
  generalize stPerm (famStair k) x1 = x2 at e2 ⊢
  have e3 := stPerm_famMid k x2 hk
  generalize stPerm (famMid k) x2 = x3 at e3 ⊢
  rw [stPerm_famClimbs]
  unfold whiteheadTorusPermNat
  split_ifs at e1 <;> split_ifs at e2 <;> (try omega) <;> split_ifs at e3 <;> (try omega) <;>
    split_ifs <;> omega

theorem stCount_famBlocks (k : ℕ) (hk : 1 ≤ k) (t : ℕ) (ht : t < 4 * k + 3) :
    stCount (famBlocks k) t = famCount k t := by
  rw [famBlocks, stCount_append, stCount_append, stCount_append, stCount_famTop k t hk]
  have e1 := stPerm_famTop k t hk
  generalize stPerm (famTop k) t = x1 at e1 ⊢
  rw [stCount_famStair k x1 hk]
  have e2 := stPerm_famStair k x1 hk
  generalize stPerm (famStair k) x1 = x2 at e2 ⊢
  rw [stCount_famMid k x2 hk]
  have e3 := stPerm_famMid k x2 hk
  generalize stPerm (famMid k) x2 = x3 at e3 ⊢
  rw [stCount_famClimbs]
  unfold famCount
  split_ifs at e1 <;> split_ifs at e2 <;> (try omega) <;> split_ifs at e3 <;> omega

/-- One step of `whiteheadTorusPermNat` advances `famCycle` by one. -/
private theorem whiteheadTorusPermNat_famCycle (k t : ℕ) (hk : 1 ≤ k) (ht : t < 4 * k + 2) :
    whiteheadTorusPermNat k (famCycle k t) = famCycle k (t + 1) := by
  generalize hx : famCycle k t = x
  generalize hy : famCycle k (t + 1) = y
  unfold famCycle at hx hy
  unfold whiteheadTorusPermNat
  split_ifs at hx hy ⊢ <;> (try contradiction) <;> omega

/-- The points of `famCycle` are strands of the family word. -/
theorem famCycle_lt (k t : ℕ) : famCycle k t < 4 * k + 3 := by
  unfold famCycle
  split_ifs <;> omega

theorem iterate_stPerm_famBlocks (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ 4 * k + 2) :
    (stPerm (famBlocks k))^[j] 0 = famCycle k j := by
  induction j with
  | zero => simp [famCycle]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega), stPerm_famBlocks k hk _ (famCycle_lt k j),
      whiteheadTorusPermNat_famCycle k j hk (by omega)]

theorem iterate_stPerm_famBlocks_period (k : ℕ) (hk : 1 ≤ k) :
    (stPerm (famBlocks k))^[4 * k + 3] 0 = 0 := by
  rw [Function.iterate_succ_apply', iterate_stPerm_famBlocks k hk _ le_rfl,
    stPerm_famBlocks k hk _ (famCycle_lt k _),
    show famCycle k (4 * k + 2) = 4 * k + 2 by unfold famCycle; split_ifs <;> omega]
  unfold whiteheadTorusPermNat
  split_ifs <;> omega

/-- The partial sums of the meridian counts along `famCycle`. -/
private def famCountPartial (k n : ℕ) : ℤ :=
  if n ≤ 2 then 0
  else if n ≤ k + 2 then (n : ℤ) - 2
  else if n ≤ 3 * k + 1 then (k : ℤ)
  else if n ≤ 4 * k + 1 then (k : ℤ) + n - 3 * k - 1
  else if n = 4 * k + 2 then 2 * (k : ℤ) - 1
  else 4 * (k : ℤ)

/-- The meridian count of the `n`-th point of `famCycle`. -/
private theorem famCount_famCycle (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    famCount k (famCycle k n) =
      if n ≤ 1 then 0 else if n ≤ k + 1 then 1 else if n ≤ 3 * k then 0
      else if n ≤ 4 * k then 1 else if n = 4 * k + 1 then -1
      else ((2 * k + 1 : ℕ) : ℤ) := by
  generalize hx : famCycle k n = x
  unfold famCycle at hx
  unfold famCount
  split_ifs at hx <;> split_ifs <;> omega

set_option maxHeartbeats 1600000 in
/-- One step of the partial sums of the meridian counts along `famCycle`. -/
private theorem famCountPartial_succ (k : ℕ) (hk : 1 ≤ k) (n m : ℕ) (hn : n < 4 * k + 3)
    (hm : m = n + 1) :
    famCountPartial k m = famCountPartial k n +
      if n ≤ 1 then 0 else if n ≤ k + 1 then 1 else if n ≤ 3 * k then 0
      else if n ≤ 4 * k then 1 else if n = 4 * k + 1 then -1
      else ((2 * k + 1 : ℕ) : ℤ) := by
  unfold famCountPartial
  split_ifs <;> omega

/-- The partial sums of the meridian counts along `famCycle` in closed form. -/
private theorem sum_famCount_famCycle (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : n ≤ 4 * k + 3) :
    ((List.range n).map fun j ↦ famCount k (famCycle k j)).sum = famCountPartial k n := by
  induction n with
  | zero => simp [famCountPartial]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih (by omega), List.map_singleton,
      List.sum_singleton]
    rw [famCount_famCycle k hk, famCountPartial_succ k hk n (n + 1) (by omega) rfl]

theorem orbitCount_famBlocks (k : ℕ) (hk : 1 ≤ k) :
    orbitCount (4 * k + 3) (famBlocks k) = 4 * k := by
  rw [orbitCount, List.map_congr_left (g := fun j ↦ famCount k (famCycle k j)) fun j hj ↦ by
    rw [iterate_stPerm_famBlocks k hk j (by simp at hj; omega),
      stCount_famBlocks k hk _ (famCycle_lt k j)], sum_famCount_famCycle k hk _ le_rfl]
  unfold famCountPartial
  split_ifs <;> omega

end AJConjecture
