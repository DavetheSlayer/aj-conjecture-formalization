import Mathlib
import AJHandoff.TorusKnot.PairKOrbPatPerm

/-!
# Strand loops of the block patterns of `pairBlocks r s`

For each block pattern of `pairBlocks r s` (nested climbs, decreasing run, increasing run,
descents, staircase) the strand loop of the strand at top position `t` is the product, from the
last block to the first, of the loops of the blocks that it carries; the lemmas give the carried
blocks by an explicit condition on the block index `j` and `t`:

* nested climbs `b(i, y - i)`: `j < t ∧ j + t ≤ y`;
* decreasing run `b(a - j, a + 1 - j)`: `j + t = a + 1`;
* increasing run `b(b + j, b + 1 + j)`: `t = b + n` (the top strand slides down the whole run);
* descents `b(a - j, b + j)`: `a < t + j ∧ t ≤ b + j`;
* staircase `b(x - j, y - j)`, `y = x + d`: on the upper part `y < t + n ∧ t ≤ y` only the block
  `j = y - t`; otherwise `x < t + n ∧ t ≤ y ∧ j + t < y ∧ (y - t - j) % d ≠ 0` (a strand of the
  lower part climbs and skips the blocks whose bottom end it meets).

The conditions were checked by computer against the definition of `stLoop` for all parameters
up to size 14. Route for each: induction on `n` as for the strand maps
(`AJHandoff.TorusKnot.PairKOrbPatPerm`), with `stLoop_append` for the last block,
`loopAt_append_left` for `j < n` and `loopAt_append_right` (`r = 0`) for `j = n`, then
`split_ifs <;> omega` on the conditions (the residue facts as in `stPerm_orbStair`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The strand loop of a one-block list. -/
theorem stLoop_singleton_orb (m : ℕ) (b : SBlock) (f : Fin m → G) (t : ℕ) :
    stLoop m [b] f t = b.strandLoop f t := by
  rw [stLoop, stLoop, stPerm, one_mul]

/-- Peeling the last block of a mapped range off a strand loop. -/
theorem stLoop_map_range_succ_orb (m : ℕ) (g : ℕ → SBlock) (f : Fin m → G) (n t : ℕ) :
    stLoop m ((List.range (n + 1)).map g) f t =
      (g n).strandLoop (runTop m ((List.range n).map g) f) t *
        stLoop m ((List.range n).map g) f ((g n).perm t) := by
  rw [List.range_succ, List.map_append, List.map_singleton, stLoop_append,
    stLoop_singleton_orb, stPerm_singleton_orb]

/-- The loop of the last block of a mapped range, read on the tuple below it. -/
private theorem loopAt_map_range_last_orb (m : ℕ) (g : ℕ → SBlock) (f : Fin m → G) (n : ℕ) :
    loopAt m ((List.range (n + 1)).map g) f n = (g n).loop (runTop m ((List.range n).map g) f) := by
  have h := loopAt_append_right m ((List.range n).map g) [g n] f 0
  rw [List.length_map, List.length_range, Nat.add_zero] at h
  rw [List.range_succ, List.map_append, List.map_singleton, h]
  simp only [loopAt, List.take_zero, runTop_nil, List.getD_cons_zero]

/-- The strand loop of a mapped range of blocks, when the carried blocks are given by a
condition `P n j t` (`n` the length of the range, `j` the block, `t` the top position). -/
private theorem stLoop_map_range_eq_filter (m : ℕ) (g : ℕ → SBlock) (f : Fin m → G)
    (P : ℕ → ℕ → ℕ → Prop) [∀ n j t, Decidable (P n j t)] (N : ℕ)
    (hc : ∀ k < N, ∀ t, (g k).carries t = true ↔ P (k + 1) k t)
    (hp : ∀ k < N, ∀ j < k, ∀ t, P k j ((g k).perm t) ↔ P (k + 1) j t) (t : ℕ) :
    stLoop m ((List.range N).map g) f t =
      ((List.range N).reverse.map fun j ↦ if P N j t then
        loopAt m ((List.range N).map g) f j else 1).prod := by
  induction N generalizing t with
  | zero => simp only [List.range_zero, List.map_nil, stLoop, List.reverse_nil, List.prod_nil]
  | succ N ih =>
    rw [stLoop_map_range_succ_orb, ih (fun k hk ↦ hc k (by omega)) (fun k hk ↦ hp k (by omega)),
      List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, List.prod_cons, ← List.range_succ, loopAt_map_range_last_orb]
    congr 1
    · rw [SBlock.strandLoop]
      by_cases h : P (N + 1) N t
      · rw [ite_eq_left ((hc N (by omega) t).2 h), ite_eq_left h]
      · rw [ite_eq_right (fun h' ↦ h ((hc N (by omega) t).1 h')), ite_eq_right h]
    · congr 1
      refine List.map_congr_left fun j hj ↦ ?_
      rw [List.mem_reverse, List.mem_range] at hj
      have hl : loopAt m ((List.range (N + 1)).map g) f j =
          loopAt m ((List.range N).map g) f j := by
        rw [List.range_succ, List.map_append]
        exact loopAt_append_left m _ _ f j (by rw [List.length_map, List.length_range]; exact hj)
      rw [hl]
      by_cases h : P (N + 1) j t
      · rw [ite_eq_left ((hp N (by omega) j hj t).2 h), ite_eq_left h]
      · rw [ite_eq_right (fun h' ↦ h ((hp N (by omega) j hj t).1 h')), ite_eq_right h]

/-- The nested climbs `b(i, y - i)`, `i < n`. -/
theorem stLoop_orbNested (m y n : ℕ) (f : Fin m → G) (t : ℕ) (hn : 2 * n ≤ y + 1) :
    stLoop m ((List.range n).map fun i ↦ SBlock.band i (y - i)) f t =
      ((List.range n).reverse.map fun j ↦ if j < t ∧ j + t ≤ y then
        loopAt m ((List.range n).map fun i ↦ SBlock.band i (y - i)) f j else 1).prod := by
  refine stLoop_map_range_eq_filter m _ f (fun _ j t ↦ j < t ∧ j + t ≤ y) n ?_ ?_ t
  · intro k hk t
    simp only [SBlock.carries, decide_eq_true_eq]
    omega
  · intro k hk j hj t
    simp only [SBlock.perm]
    split_ifs <;> omega

/-- The decreasing run `b(a - j, a' - j)` (`a' = a + 1`), `j < n`. -/
theorem stLoop_orbRunDown (m a a' n : ℕ) (f : Fin m → G) (t : ℕ) (ha : a' = a + 1)
    (hn : n ≤ a + 1) :
    stLoop m ((List.range n).map fun j ↦ SBlock.band (a - j) (a' - j)) f t =
      ((List.range n).reverse.map fun j ↦ if j + t = a' then
        loopAt m ((List.range n).map fun j ↦ SBlock.band (a - j) (a' - j)) f j else 1).prod := by
  refine stLoop_map_range_eq_filter m _ f (fun _ j t ↦ j + t = a') n ?_ ?_ t
  · intro k hk t
    simp only [SBlock.carries, decide_eq_true_eq]
    omega
  · intro k hk j hj t
    simp only [SBlock.perm]
    split_ifs <;> omega

/-- The increasing run `b(b + j, b' + j)` (`b' = b + 1`), `j < n`. -/
theorem stLoop_orbRunUp (m b b' n : ℕ) (f : Fin m → G) (t : ℕ) (hb : b' = b + 1) :
    stLoop m ((List.range n).map fun j ↦ SBlock.band (b + j) (b' + j)) f t =
      ((List.range n).reverse.map fun j ↦ if t = b + n then
        loopAt m ((List.range n).map fun j ↦ SBlock.band (b + j) (b' + j)) f j else 1).prod := by
  refine stLoop_map_range_eq_filter m _ f (fun n _ t ↦ t = b + n) n ?_ ?_ t
  · intro k hk t
    simp only [SBlock.carries, decide_eq_true_eq]
    omega
  · intro k hk j hj t
    simp only [SBlock.perm]
    split_ifs <;> omega

/-- The descents `b(a - j, b + j)`, `j < n`, with `a < b`. -/
theorem stLoop_orbSpread (m a b n : ℕ) (f : Fin m → G) (t : ℕ) (hab : a < b)
    (hn : n ≤ a + 1) :
    stLoop m ((List.range n).map fun j ↦ SBlock.band (a - j) (b + j)) f t =
      ((List.range n).reverse.map fun j ↦ if a < t + j ∧ t ≤ b + j then
        loopAt m ((List.range n).map fun j ↦ SBlock.band (a - j) (b + j)) f j else 1).prod := by
  refine stLoop_map_range_eq_filter m _ f (fun _ j t ↦ a < t + j ∧ t ≤ b + j) n ?_ ?_ t
  · intro k hk t
    simp only [SBlock.carries, decide_eq_true_eq]
    omega
  · intro k hk j hj t
    simp only [SBlock.perm]
    split_ifs <;> omega

/-- The staircase `b(x - j, y - j)` (`y = x + d`), `j < n`. -/
theorem stLoop_orbStair (m x y d n : ℕ) (f : Fin m → G) (t : ℕ) (hy : y = x + d) (hd : 1 ≤ d)
    (hn : n ≤ x + 1) :
    stLoop m ((List.range n).map fun j ↦ SBlock.band (x - j) (y - j)) f t =
      ((List.range n).reverse.map fun j ↦
        if (if y < t + n ∧ t ≤ y then j + t = y
            else x < t + n ∧ t ≤ y ∧ j + t < y ∧ (y - t - j) % d ≠ 0) then
          loopAt m ((List.range n).map fun j ↦ SBlock.band (x - j) (y - j)) f j
        else 1).prod := by
  refine stLoop_map_range_eq_filter m _ f (fun n j t ↦ if y < t + n ∧ t ≤ y then j + t = y
    else x < t + n ∧ t ≤ y ∧ j + t < y ∧ (y - t - j) % d ≠ 0) n ?_ ?_ t
  · intro k hk t
    have hmod : x ≤ t + k → t + k < y → ((y - t - k) % d = 0 ↔ x = t + k) := by
      intro h1 h2
      constructor
      · intro h0
        by_contra hne
        rw [Nat.mod_eq_of_lt (by omega)] at h0
        omega
      · intro he
        rw [show y - t - k = d by omega, Nat.mod_self]
    simp only [SBlock.carries, decide_eq_true_eq]
    split_ifs <;> omega
  · intro k hk j hj t
    have hm : (y - (x - k) - j) % d = (y - (y - k) - j) % d := by
      rw [show y - (x - k) - j = (y - (y - k) - j) + d by omega, Nat.add_mod_right]
    simp only [SBlock.perm]
    by_cases h1 : t = x - k
    · subst h1
      simp only [ite_true]
      split_ifs <;> omega
    · by_cases h2 : t = y - k
      · subst h2
        simp only [h1, ite_true, ite_false]
        split_ifs <;> omega
      · simp only [h1, h2, ite_false]
        split_ifs <;> omega

end AJConjecture
