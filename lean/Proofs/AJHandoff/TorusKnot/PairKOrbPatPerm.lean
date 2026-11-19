import Mathlib
import AJHandoff.TorusKnot.PairKOrbDefs

/-!
# Strand maps of the block patterns of `pairBlocks r s`

Public copies (renamed) of the pattern lemmas of `AJHandoff.TorusKnot.PairKConnected`, where they
are private: the strand map of a one-block list, of the nested climbs `b(i, y - i)`, of the
decreasing and increasing runs, of the descents `b(a - j, b + j)` and of the staircase
`b(x - j, y - j)`. They are used for the closed form of `stPerm (pairBlocks r s)`
(`AJHandoff.TorusKnot.PairKOrbPerm`) and for the strand loops of the patterns
(`AJHandoff.TorusKnot.PairKOrbPatLoop`).
-/

namespace AJConjecture

/-- The strand map of a one-block list. -/
theorem stPerm_singleton_orb (b : SBlock) (t : ℕ) : stPerm [b] t = b.perm t := rfl

/-- Peeling the last block of a mapped range. -/
theorem stPerm_map_range_succ_orb (f : ℕ → SBlock) (n t : ℕ) :
    stPerm ((List.range (n + 1)).map f) t = stPerm ((List.range n).map f) ((f n).perm t) := by
  rw [List.range_succ, List.map_append, stPerm_append, List.map_singleton, stPerm_singleton_orb]

/-- The nested climbs `b(i, y - i)`, `i < n`, swap `t` and `y - t` on both ends. -/
theorem stPerm_orbNested (y n t : ℕ) (hn : 2 * n ≤ y + 1) :
    stPerm ((List.range n).map fun i ↦ SBlock.band i (y - i)) t =
      if t < n ∨ (y < t + n ∧ t ≤ y) then y - t else t := by
  induction n generalizing t with
  | zero => simp only [List.range_zero, List.map_nil, stPerm]; split_ifs <;> omega
  | succ n ih =>
    rw [stPerm_map_range_succ_orb, ih _ (by omega)]
    simp only [SBlock.perm]
    split_ifs <;> omega

/-- The decreasing run `b(a - j, a' - j)` (`a' = a + 1`), `j < n`. -/
theorem stPerm_orbRunDown (a a' n t : ℕ) (ha : a' = a + 1) (hn : n ≤ a + 1) :
    stPerm ((List.range n).map fun j ↦ SBlock.band (a - j) (a' - j)) t =
      if t + n = a' then a' else if a' + 1 ≤ t + n ∧ t ≤ a' then t - 1 else t := by
  induction n generalizing t with
  | zero => simp only [List.range_zero, List.map_nil, stPerm]; split_ifs <;> omega
  | succ n ih =>
    rw [stPerm_map_range_succ_orb, ih _ (by omega)]
    simp only [SBlock.perm]
    split_ifs <;> omega

/-- The increasing run `b(b + j, b' + j)` (`b' = b + 1`), `j < n`. -/
theorem stPerm_orbRunUp (b b' n t : ℕ) (hb : b' = b + 1) :
    stPerm ((List.range n).map fun j ↦ SBlock.band (b + j) (b' + j)) t =
      if t = b + n then b else if b ≤ t ∧ t < b + n then t + 1 else t := by
  induction n generalizing t with
  | zero => simp only [List.range_zero, List.map_nil, stPerm]; split_ifs <;> omega
  | succ n ih =>
    rw [stPerm_map_range_succ_orb, ih]
    simp only [SBlock.perm]
    split_ifs <;> omega

/-- The descents `b(a - j, b + j)`, `j < n`, with `a < b`. -/
theorem stPerm_orbSpread (a b n t : ℕ) (hab : a < b) (hn : n ≤ a + 1) :
    stPerm ((List.range n).map fun j ↦ SBlock.band (a - j) (b + j)) t =
      if t ≤ a ∧ a < t + n then b + (a - t) else if b ≤ t ∧ t < b + n then a - (t - b)
      else t := by
  induction n generalizing t with
  | zero => simp only [List.range_zero, List.map_nil, stPerm]; split_ifs <;> omega
  | succ n ih =>
    rw [stPerm_map_range_succ_orb, ih _ (by omega)]
    simp only [SBlock.perm]
    split_ifs <;> omega

/-- The staircase `b(x - j, y - j)` (`y = x + d`), `j < n`: a strand of the upper part steps
down by `d`, a strand of the lower part climbs to the top of its residue class. -/
theorem stPerm_orbStair (x y d n t : ℕ) (hy : y = x + d) (hd : 1 ≤ d)
    (hn : n ≤ x + 1) :
    stPerm ((List.range n).map fun j ↦ SBlock.band (x - j) (y - j)) t =
      if y < t + n ∧ t ≤ y then t - d
      else if x < t + n ∧ t ≤ x then y - (y - t) % d else t := by
  induction n generalizing t with
  | zero => simp only [List.range_zero, List.map_nil, stPerm]; split_ifs <;> omega
  | succ n ih =>
    rw [stPerm_map_range_succ_orb, ih _ (by omega)]
    have h1 : (y - t) % d = n % d ∨ t ≠ x - n := by
      by_cases ht : t = x - n
      · left
        rw [ht, show y - (x - n) = n + d by omega, Nat.add_mod_right]
      · exact Or.inr ht
    have h2 : (y - (y - n)) % d = n % d := by
      rw [show y - (y - n) = n by omega]
    have h3 : n % d = n ∨ d ≤ n := by
      rcases lt_or_ge n d with h | h
      · exact Or.inl (Nat.mod_eq_of_lt h)
      · exact Or.inr h
    simp only [SBlock.perm]
    split_ifs <;> omega

end AJConjecture
