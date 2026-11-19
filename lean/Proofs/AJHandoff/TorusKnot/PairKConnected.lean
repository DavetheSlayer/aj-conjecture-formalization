import Mathlib
import AJHandoff.TorusKnot.PairKBlocks

/-!
# The closure of the braided-surface word is a knot

The strand permutation of `pairWhiteheadWord r s` is one `(2c + 1)`-cycle (`c = (r - 1) s`).
Route: each block acts on positions by `SBlock.perm` (a transposition), so the strand map is
`stPerm (pairBlocks r s)` (`AJConjecture.artinWord_blocksWord_fst`); give it in closed form
(piecewise affine in the position, with the four regimes "below the staircase", "decreasing
run", "increasing run", "staircase"), then an explicit enumeration of the orbit of `0` and its
inverse, as `whiteheadCycleEnum` / `whiteheadCycleIndex` do for `r = 2`. Computed orbits
(outside the formal development): for `(3, 4)`,
`0 → 16 → 11 → 14 → 10 → 13 → 9 → 8 → 7 → 6 → 5 → 12 → 15 → 1 → 2 → 3 → 4 → 0`.
-/

namespace AJConjecture

/-- The strand map of a one-block list. -/
private theorem stPerm_singleton_pair (b : SBlock) (t : ℕ) : stPerm [b] t = b.perm t := rfl

/-- Peeling the last block of a mapped range. -/
private theorem stPerm_map_range_succ (f : ℕ → SBlock) (n t : ℕ) :
    stPerm ((List.range (n + 1)).map f) t = stPerm ((List.range n).map f) ((f n).perm t) := by
  rw [List.range_succ, List.map_append, stPerm_append, List.map_singleton, stPerm_singleton_pair]

/-- The nested climbs `b(i, y - i)`, `i < n`, swap `t` and `y - t` on both ends. -/
private theorem stPerm_pairNested (y n t : ℕ) (hn : 2 * n ≤ y + 1) :
    stPerm ((List.range n).map fun i ↦ SBlock.band i (y - i)) t =
      if t < n ∨ (y < t + n ∧ t ≤ y) then y - t else t := by
  induction n generalizing t with
  | zero => simp only [List.range_zero, List.map_nil, stPerm]; split_ifs <;> omega
  | succ n ih =>
    rw [stPerm_map_range_succ, ih _ (by omega)]
    simp only [SBlock.perm]
    split_ifs <;> omega

/-- The decreasing run `b(a - j, a' - j)` (`a' = a + 1`), `j < n`. -/
private theorem stPerm_pairRunDown (a a' n t : ℕ) (ha : a' = a + 1) (hn : n ≤ a + 1) :
    stPerm ((List.range n).map fun j ↦ SBlock.band (a - j) (a' - j)) t =
      if t + n = a' then a' else if a' + 1 ≤ t + n ∧ t ≤ a' then t - 1 else t := by
  induction n generalizing t with
  | zero => simp only [List.range_zero, List.map_nil, stPerm]; split_ifs <;> omega
  | succ n ih =>
    rw [stPerm_map_range_succ, ih _ (by omega)]
    simp only [SBlock.perm]
    split_ifs <;> omega

/-- The increasing run `b(b + j, b' + j)` (`b' = b + 1`), `j < n`. -/
private theorem stPerm_pairRunUp (b b' n t : ℕ) (hb : b' = b + 1) :
    stPerm ((List.range n).map fun j ↦ SBlock.band (b + j) (b' + j)) t =
      if t = b + n then b else if b ≤ t ∧ t < b + n then t + 1 else t := by
  induction n generalizing t with
  | zero => simp only [List.range_zero, List.map_nil, stPerm]; split_ifs <;> omega
  | succ n ih =>
    rw [stPerm_map_range_succ, ih]
    simp only [SBlock.perm]
    split_ifs <;> omega

/-- The descents `b(a - j, b + j)`, `j < n`, with `a < b`. -/
private theorem stPerm_pairSpread (a b n t : ℕ) (hab : a < b) (hn : n ≤ a + 1) :
    stPerm ((List.range n).map fun j ↦ SBlock.band (a - j) (b + j)) t =
      if t ≤ a ∧ a < t + n then b + (a - t) else if b ≤ t ∧ t < b + n then a - (t - b)
      else t := by
  induction n generalizing t with
  | zero => simp only [List.range_zero, List.map_nil, stPerm]; split_ifs <;> omega
  | succ n ih =>
    rw [stPerm_map_range_succ, ih _ (by omega)]
    simp only [SBlock.perm]
    split_ifs <;> omega

/-- The staircase `b(x - j, y - j)` (`y = x + d`), `j < n`: a strand of the upper part steps
down by `d`, a strand of the lower part climbs to the top of its residue class. -/
private theorem stPerm_pairStair (x y d n t : ℕ) (hy : y = x + d) (hd : 1 ≤ d)
    (hn : n ≤ x + 1) :
    stPerm ((List.range n).map fun j ↦ SBlock.band (x - j) (y - j)) t =
      if y < t + n ∧ t ≤ y then t - d
      else if x < t + n ∧ t ≤ x then y - (y - t) % d else t := by
  induction n generalizing t with
  | zero => simp only [List.range_zero, List.map_nil, stPerm]; split_ifs <;> omega
  | succ n ih =>
    rw [stPerm_map_range_succ, ih _ (by omega)]
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


/-- The arithmetic of an admissible pair: `r + 1 ≤ s`, `E + s + r = c + 3` and `1 ≤ E`. -/
private theorem pairConnected_arith {r s : ℕ} (h : IsTorusPair r s) :
    2 ≤ r ∧ r + 1 ≤ s ∧ 1 ≤ pairRunDown r s ∧
      pairRunDown r s + s + r = pairC r s + 3 := by
  obtain ⟨hr, hrs, -⟩ := h
  obtain ⟨a, rfl⟩ : ∃ a, r = a + 2 := ⟨r - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, s = b + 1 := ⟨s - 1, by omega⟩
  simp only [pairC, pairRunDown, Nat.add_sub_cancel]
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [show a + 2 - 1 = a + 1 by omega]
  ring

/-- The strand map of the pieces of `pairBlocks r s`, numbered in the order in which they act
on a strand (the last block acts first). -/
private def pairStage (r s : ℕ) : ℕ → ℕ → ℕ
  | 0, t => (SBlock.neg (pairTop r s)).perm t
  | 1, t => stPerm ((List.range (r - 2)).map
      fun j ↦ SBlock.band (r - 3 - j) (pairTop r s + 2 - s - r + j)) t
  | 2, t => (SBlock.band (pairTop r s - s) (pairTop r s)).perm t
  | 3, t => (SBlock.band (r - 2) (pairTop r s + 1 - s)).perm t
  | 4, t => stPerm ((List.range (s - 2)).map
      fun j ↦ SBlock.band (pairTop r s - r - 1 - j) (pairTop r s - 1 - j)) t
  | 5, t => (SBlock.neg (pairTop r s)).perm t
  | 6, t => (SBlock.band (pairTop r s - r) (pairTop r s)).perm t
  | 7, t => (SBlock.band (r - 2 + pairRunDown r s + pairRunUp r s) (pairTop r s + 1 - r)).perm t
  | 8, t => stPerm ((List.range (pairRunUp r s)).map
      fun j ↦ SBlock.band (r - 2 + pairRunDown r s + j) (r - 1 + pairRunDown r s + j)) t
  | 9, t => stPerm ((List.range (pairRunDown r s)).map
      fun j ↦ SBlock.band (r + pairRunDown r s - 3 - j) (r + pairRunDown r s - 2 - j)) t
  | 10, t => stPerm ((List.range (r - 2)).map fun i ↦ SBlock.band i (pairTop r s - 1 - i)) t
  | _, t => t

/-- The strand map of `pairBlocks r s` is the composite of the eleven stages. -/
private theorem stPerm_pairBlocks_stages (r s t : ℕ) :
    stPerm (pairBlocks r s) t = pairStage r s 10 (pairStage r s 9 (pairStage r s 8
      (pairStage r s 7 (pairStage r s 6 (pairStage r s 5 (pairStage r s 4 (pairStage r s 3
        (pairStage r s 2 (pairStage r s 1 (pairStage r s 0 t)))))))))) := by
  simp only [pairBlocks, stPerm_append, stPerm, pairStage]

/-- Stage `0` (and `5`): the negative Hopf letter on the top level. -/
private theorem pairStage_zero {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    pairStage r s 0 t = if t + 1 = 2 * pairC r s then 2 * pairC r s
      else if t = 2 * pairC r s then 2 * pairC r s - 1 else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  simp only [pairStage, pairTop]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `5` is stage `0`. -/
private theorem pairStage_five (r s t : ℕ) : pairStage r s 5 t = pairStage r s 0 t := rfl

/-- Stage `1`: the right descents. -/
private theorem pairStage_one {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    pairStage r s 1 t =
      if t + 3 ≤ r ∨ (2 * pairC r s + 1 ≤ t + s + r ∧ t + s + 1 < 2 * pairC r s)
      then 2 * pairC r s - s - 2 - t else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  simp only [pairStage, pairTop]
  rw [stPerm_pairSpread _ _ _ _ (by omega) (by omega)]
  split_ifs <;> omega

/-- Stage `2`: the top-right climb. -/
private theorem pairStage_two {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    pairStage r s 2 t = if t + s + 1 = 2 * pairC r s then 2 * pairC r s - 1
      else if t + 1 = 2 * pairC r s then 2 * pairC r s - 1 - s else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  simp only [pairStage, pairTop]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `3`: the last round of the staircase. -/
private theorem pairStage_three {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    pairStage r s 3 t = if t + 2 = r then 2 * pairC r s - s
      else if t + s = 2 * pairC r s then r - 2 else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  simp only [pairStage, pairTop]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `4`: the staircase rounds. -/
private theorem pairStage_four {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    pairStage r s 4 t = if 2 * pairC r s < t + s ∧ t + 2 ≤ 2 * pairC r s then t - r
      else if 2 * pairC r s < t + s + r ∧ t + r + 2 ≤ 2 * pairC r s then
        2 * pairC r s - 2 - (2 * pairC r s - 2 - t) % r
      else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  simp only [pairStage, pairTop]
  rw [stPerm_pairStair (2 * pairC r s - 1 - r - 1) (2 * pairC r s - 1 - 1) r _ _ (by omega)
    (by omega) (by omega)]
  rw [show 2 * pairC r s - 1 - 1 = 2 * pairC r s - 2 by omega]
  split_ifs <;> omega

/-- Stage `6`: the first round of the staircase. -/
private theorem pairStage_six {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    pairStage r s 6 t = if t + r + 1 = 2 * pairC r s then 2 * pairC r s - 1
      else if t + 1 = 2 * pairC r s then 2 * pairC r s - 1 - r else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  simp only [pairStage, pairTop]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `7`: the big climb. -/
private theorem pairStage_seven {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    pairStage r s 7 t = if t + s + r = 2 * pairC r s then 2 * pairC r s - r
      else if t + r = 2 * pairC r s then 2 * pairC r s - s - r else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  simp only [pairStage, pairTop, pairRunUp]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `8`: the increasing run. -/
private theorem pairStage_eight {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    pairStage r s 8 t = if t + s + r = 2 * pairC r s then pairC r s - s + 1
      else if pairC r s + 1 ≤ t + s ∧ t + s + r < 2 * pairC r s then t + 1 else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  simp only [pairStage, pairRunUp]
  rw [stPerm_pairRunUp _ _ _ _ (by omega)]
  split_ifs <;> omega

/-- Stage `9`: the decreasing run. -/
private theorem pairStage_nine {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    pairStage r s 9 t = if t + 2 = r then pairC r s - s + 1
      else if r ≤ t + 1 ∧ t + s ≤ pairC r s + 1 then t - 1 else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  simp only [pairStage]
  rw [stPerm_pairRunDown _ _ _ _ (by omega) (by omega)]
  split_ifs <;> omega

/-- Stage `10`: the left climbs. -/
private theorem pairStage_ten {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    pairStage r s 10 t = if t + 2 < r ∨ (2 * pairC r s < t + r ∧ t + 2 ≤ 2 * pairC r s)
      then 2 * pairC r s - 2 - t else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  simp only [pairStage, pairTop]
  rw [stPerm_pairNested _ _ _ (by omega)]
  split_ifs <;> omega

/-- Evaluate the stages `0`–`4` of the strand map one after another, discarding the branches
that contradict the hypotheses. -/
local macro "pair_head " h:term : tactic => `(tactic| (
  all_goals (rw [pairStage_zero $h]; split_ifs <;> try omega)
  all_goals (rw [pairStage_one $h]; split_ifs <;> try omega)
  all_goals (rw [pairStage_two $h]; split_ifs <;> try omega)
  all_goals (rw [pairStage_three $h]; split_ifs <;> try omega)
  all_goals (rw [pairStage_four $h]; split_ifs <;> try omega)))

/-- Evaluate the stages `5`–`10` of the strand map one after another. -/
local macro "pair_tail " h:term : tactic => `(tactic| (
  all_goals (rw [pairStage_five, pairStage_zero $h]; split_ifs <;> try omega)
  all_goals (rw [pairStage_six $h]; split_ifs <;> try omega)
  all_goals (rw [pairStage_seven $h]; split_ifs <;> try omega)
  all_goals (rw [pairStage_eight $h]; split_ifs <;> try omega)
  all_goals (rw [pairStage_nine $h]; split_ifs <;> try omega)
  all_goals (rw [pairStage_ten $h]; split_ifs <;> try omega)))

/-- Below the staircase the strand map steps down by one. -/
private theorem stPerm_pairBlocks_down {r s : ℕ} (h : IsTorusPair r s) {t : ℕ}
    (h1 : r ≤ t + 1) (h2 : t + s ≤ pairC r s) : stPerm (pairBlocks r s) t = t - 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  rw [stPerm_pairBlocks_stages]
  pair_head h
  pair_tail h

/-- Along the increasing run the strand map steps up by one. -/
private theorem stPerm_pairBlocks_up {r s : ℕ} (h : IsTorusPair r s) {t : ℕ}
    (h1 : pairC r s + 1 ≤ t + s) (h2 : t + s + r + 1 ≤ 2 * pairC r s) :
    stPerm (pairBlocks r s) t = t + 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  rw [stPerm_pairBlocks_stages]
  pair_head h
  pair_tail h

/-- At the foot of the staircase the strand map jumps up by `s`. -/
private theorem stPerm_pairBlocks_foot {r s : ℕ} (h : IsTorusPair r s) {t : ℕ}
    (h1 : 2 * pairC r s ≤ t + s + r) (h2 : t + s + 2 ≤ 2 * pairC r s) :
    stPerm (pairBlocks r s) t = t + s := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  rw [stPerm_pairBlocks_stages]
  pair_head h
  pair_tail h

/-- The strand `2c - s - 1` goes to the extra strand `2c`. -/
private theorem stPerm_pairBlocks_toExtra {r s : ℕ} (h : IsTorusPair r s) {t : ℕ}
    (h1 : t + s + 1 = 2 * pairC r s) : stPerm (pairBlocks r s) t = 2 * pairC r s := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  rw [stPerm_pairBlocks_stages]
  pair_head h
  pair_tail h

/-- The strand `2c - s` goes to the foot `c - s + 1` of the increasing run. -/
private theorem stPerm_pairBlocks_toRun {r s : ℕ} (h : IsTorusPair r s) {t : ℕ}
    (h1 : t + s = 2 * pairC r s) : stPerm (pairBlocks r s) t = pairC r s - s + 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  rw [stPerm_pairBlocks_stages]
  pair_head h
  pair_tail h

/-- On the staircase the strand map steps down by `r`. -/
private theorem stPerm_pairBlocks_stair {r s : ℕ} (h : IsTorusPair r s) {t : ℕ}
    (h1 : 2 * pairC r s + 1 ≤ t + s) (h2 : t + 1 ≤ 2 * pairC r s) :
    stPerm (pairBlocks r s) t = t - r := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  rw [stPerm_pairBlocks_stages]
  pair_head h
  pair_tail h

/-- A value `a - x % r` only depends on `x` modulo `r`. -/
private theorem pair_sub_mod_congr {a x y r : ℕ} (hxy : x = y ∨ x + r = y) :
    a - x % r = a - y % r := by
  rcases hxy with rfl | rfl
  · rfl
  · rw [Nat.add_mod_right]

/-- The strand of the low index `i < r`: the strand `i` for `i ≤ r - 2`, the extra strand `2c`
for `i = r - 1`. -/
private def pairLowStrand (r s i : ℕ) : ℕ := if i + 1 = r then 2 * pairC r s else i

/-- The first five stages send the low strand of index `i` to `2c - 2 - (s + i) % r`. -/
private theorem pairStage_head_low {r s : ℕ} (h : IsTorusPair r s) {i : ℕ} (hi : i < r) :
    pairStage r s 4 (pairStage r s 3 (pairStage r s 2 (pairStage r s 1 (pairStage r s 0
      (pairLowStrand r s i))))) = 2 * pairC r s - 2 - (s + i) % r := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  unfold pairLowStrand
  split_ifs
  all_goals pair_head h
  all_goals first
    | (apply pair_sub_mod_congr; omega)
    | (have hm : (s + i) % r = s + i - r := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
       omega)

/-- The last six stages, on `2c - 2 - u`, `u ≤ r - 3`: the left climb to `u`. -/
private theorem pairStage_tail_low {r s : ℕ} (h : IsTorusPair r s) {u : ℕ} (hu : u + 3 ≤ r) :
    pairStage r s 10 (pairStage r s 9 (pairStage r s 8 (pairStage r s 7 (pairStage r s 6
      (pairStage r s 5 (2 * pairC r s - 2 - u)))))) = u := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  pair_tail h

/-- The last six stages, on `2c - 2 - (r - 2)`: through the big climb and both runs to `c - s`. -/
private theorem pairStage_tail_mid {r s : ℕ} (h : IsTorusPair r s) {u : ℕ} (hu : u + 2 = r) :
    pairStage r s 10 (pairStage r s 9 (pairStage r s 8 (pairStage r s 7 (pairStage r s 6
      (pairStage r s 5 (2 * pairC r s - 2 - u)))))) = pairC r s - s := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  pair_tail h

/-- The last six stages, on `2c - 2 - (r - 1)`: the first staircase round, to the top `2c - 1`. -/
private theorem pairStage_tail_top {r s : ℕ} (h : IsTorusPair r s) {u : ℕ} (hu : u + 1 = r) :
    pairStage r s 10 (pairStage r s 9 (pairStage r s 8 (pairStage r s 7 (pairStage r s 6
      (pairStage r s 5 (2 * pairC r s - 2 - u)))))) = 2 * pairC r s - 1 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairConnected_arith h
  pair_tail h

/-- The strand map of Artin's action is the strand permutation of the word. -/
private theorem artinWord_fst_eq_strandPerm_pair (m : ℕ) (w : BraidWord) (k : Fin m) :
    (artinWord m w k).1 = strandPerm m w k := by
  induction w with
  | nil => simp [artinWord, strandPerm]
  | cons g w ih =>
    rw [strandPerm, List.map_cons, List.prod_cons, ← strandPerm, Equiv.Perm.mul_apply, ← ih]
    simp only [artinWord]
    generalize (artinWord m w k).1 = l
    by_cases h : g.1 + 1 < m
    · simp only [artinGen, strandSwap, h, dite_true, Equiv.swap_apply_def]
      split_ifs <;> simp only [Fin.ext_iff] at * <;> omega
    · simp [artinGen, strandSwap, h]

/-- The strand permutation of `pairWhiteheadWord r s` is the strand map of its blocks. -/
private theorem strandPerm_pairWhiteheadWord_val {r s : ℕ} (h : IsTorusPair r s)
    (x : Fin (pairStrands r s)) :
    ((strandPerm (pairStrands r s) (pairWhiteheadWord r s) x : Fin (pairStrands r s)) : ℕ) =
      stPerm (pairBlocks r s) x := by
  rw [← artinWord_fst_eq_strandPerm_pair, pairWhiteheadWord,
    artinWord_blocksWord_fst _ (pairBlocks_valid h)]

/-- Two positions lie on the same component of the closure of `pairWhiteheadWord r s`. -/
private def PairLinked (r s x y : ℕ) : Prop :=
  ∃ (hx : x < pairStrands r s) (hy : y < pairStrands r s),
    (strandPerm (pairStrands r s) (pairWhiteheadWord r s)).SameCycle ⟨x, hx⟩ ⟨y, hy⟩

/-- Every position is linked to itself. -/
private theorem pairLinked_refl {r s x : ℕ} (hx : x < pairStrands r s) : PairLinked r s x x :=
  ⟨hx, hx, Equiv.Perm.SameCycle.refl _ _⟩

/-- Linking is symmetric. -/
private theorem pairLinked_symm {r s x y : ℕ} (hxy : PairLinked r s x y) : PairLinked r s y x :=
  let ⟨hx, hy, h⟩ := hxy
  ⟨hy, hx, h.symm⟩

/-- Linking is transitive. -/
private theorem pairLinked_trans {r s x y z : ℕ} (hxy : PairLinked r s x y)
    (hyz : PairLinked r s y z) : PairLinked r s x z :=
  let ⟨hx, _, h1⟩ := hxy
  let ⟨_, hz, h2⟩ := hyz
  ⟨hx, hz, h1.trans h2⟩

/-- A position is linked to its image under the strand map. -/
private theorem pairLinked_stPerm {r s : ℕ} (h : IsTorusPair r s) {x : ℕ}
    (hx : x < pairStrands r s) : PairLinked r s x (stPerm (pairBlocks r s) x) := by
  have hv := strandPerm_pairWhiteheadWord_val h ⟨x, hx⟩
  have hlt : stPerm (pairBlocks r s) x < pairStrands r s :=
    stPerm_lt _ (pairBlocks_valid h) x hx
  refine ⟨hx, hlt, ?_⟩
  have he : (⟨stPerm (pairBlocks r s) x, hlt⟩ : Fin (pairStrands r s)) =
      strandPerm (pairStrands r s) (pairWhiteheadWord r s) ⟨x, hx⟩ := Fin.ext hv.symm
  rw [he]
  exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)

/-- A position is linked to `y` if its image under the strand map is. -/
private theorem pairLinked_of_stPerm {r s : ℕ} (h : IsTorusPair r s) {x y : ℕ}
    (hx : x < pairStrands r s) (hxy : PairLinked r s (stPerm (pairBlocks r s) x) y) :
    PairLinked r s x y :=
  pairLinked_trans (pairLinked_stPerm h hx) hxy

/-- The decreasing run `r - 2 ≤ t ≤ c - s` is linked to its foot `r - 2`. -/
private theorem pairLinked_down {r s : ℕ} (h : IsTorusPair r s) :
    ∀ t, r ≤ t + 2 → t + s ≤ pairC r s → PairLinked r s t (r - 2) := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairConnected_arith h
  intro t
  induction t with
  | zero =>
    intro h1 _
    exact (show r - 2 = 0 by omega) ▸ pairLinked_refl (by simp only [pairStrands]; omega)
  | succ t ih =>
    intro h1 h2
    by_cases ht : t + 1 + 2 = r
    · exact (show r - 2 = t + 1 by omega) ▸ pairLinked_refl (by simp only [pairStrands]; omega)
    · refine pairLinked_of_stPerm h (by simp only [pairStrands]; omega) ?_
      rw [stPerm_pairBlocks_down h (by omega) (by omega), Nat.add_sub_cancel]
      exact ih (by omega) (by omega)

/-- The increasing run `c - s + 1 ≤ t ≤ 2c - s - r` is linked to its top `2c - s - r`. -/
private theorem pairLinked_up {r s : ℕ} (h : IsTorusPair r s) :
    ∀ k t, t + k = 2 * pairC r s - s - r → pairC r s + 1 ≤ t + s →
      PairLinked r s t (2 * pairC r s - s - r) := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairConnected_arith h
  intro k
  induction k with
  | zero =>
    intro t h1 _
    exact (show t = 2 * pairC r s - s - r by omega) ▸
      pairLinked_refl (by simp only [pairStrands]; omega)
  | succ k ih =>
    intro t h1 h2
    refine pairLinked_of_stPerm h (by simp only [pairStrands]; omega) ?_
    rw [stPerm_pairBlocks_up h (by omega) (by omega)]
    exact ih (t + 1) (by omega) (by omega)

/-- The position `2c - s - r + y` of the window and the staircase. -/
private def pairWindow (r s y : ℕ) : ℕ := 2 * pairC r s - s - r + y

/-- Along the staircase a window position `y ∈ [1, r + s - 1]` descends in steps of `r` to a
position `y' ∈ [1, r]` with `y' ≡ y (mod r)`. -/
private theorem pairLinked_window {r s : ℕ} (h : IsTorusPair r s) :
    ∀ y, 1 ≤ y → y + 1 ≤ r + s → ∃ y', 1 ≤ y' ∧ y' ≤ r ∧ y' % r = y % r ∧
      PairLinked r s (pairWindow r s y) (pairWindow r s y') := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairConnected_arith h
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro h1 h2
    by_cases hy : y ≤ r
    · exact ⟨y, h1, hy, rfl, pairLinked_refl (by simp only [pairWindow, pairStrands]; omega)⟩
    · obtain ⟨y', h1', h2', h3', h4'⟩ := ih (y - r) (by omega) (by omega) (by omega)
      refine ⟨y', h1', h2', ?_, ?_⟩
      · rw [h3', Nat.mod_eq_sub_mod (by omega : r ≤ y)]
      · refine pairLinked_of_stPerm h (by simp only [pairWindow, pairStrands]; omega) ?_
        rw [stPerm_pairBlocks_stair h (by simp only [pairWindow]; omega)
          (by simp only [pairWindow]; omega)]
        rw [show pairWindow r s y - r = pairWindow r s (y - r) by simp only [pairWindow]; omega]
        exact h4'

/-- The low strand of index `i` goes to the low strand of index `(s + i) % r`, unless that index
is `r - 1`, in which case it goes to the top `2c - 1` of the staircase. -/
private theorem pairLinked_low_step {r s : ℕ} (h : IsTorusPair r s) {i : ℕ} (hi : i < r) :
    ((s + i) % r + 1 ≠ r →
      PairLinked r s (pairLowStrand r s i) (pairLowStrand r s ((s + i) % r))) ∧
    ((s + i) % r + 1 = r → PairLinked r s (pairLowStrand r s i) (2 * pairC r s - 1)) := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairConnected_arith h
  have hlt : pairLowStrand r s i < pairStrands r s := by
    simp only [pairLowStrand, pairStrands]; split_ifs <;> omega
  have hu : (s + i) % r < r := Nat.mod_lt _ (by omega)
  have hval := stPerm_pairBlocks_stages r s (pairLowStrand r s i)
  rw [pairStage_head_low h hi] at hval
  refine ⟨fun hne ↦ pairLinked_of_stPerm h hlt ?_, fun heq ↦ pairLinked_of_stPerm h hlt ?_⟩
  · have hlow : pairLowStrand r s ((s + i) % r) = (s + i) % r := by
      simp only [pairLowStrand, hne, ite_false]
    rw [hlow]
    by_cases h3 : (s + i) % r + 3 ≤ r
    · rw [hval, pairStage_tail_low h h3]
      exact pairLinked_refl (by simp only [pairStrands]; omega)
    · rw [hval, pairStage_tail_mid h (by omega)]
      rw [show (s + i) % r = r - 2 by omega]
      exact pairLinked_down h _ (by omega) (by omega)
  · rw [hval, pairStage_tail_top h heq]
    exact pairLinked_refl (by simp only [pairStrands]; omega)

/-- The window position of index `y < r`: the foot `2c - s - r + y` of the staircase for
`y ≤ r - 2`, its top `2c - 1` for `y = r - 1`. -/
private def pairHighStrand (r s y : ℕ) : ℕ := if y + 1 = r then 2 * pairC r s - 1 else
  pairWindow r s y

/-- The high strand of index `y` is linked to the high strand of index `(y + s) % r`, unless
that index is `r - 1`, in which case it is linked to the extra strand `2c`. -/
private theorem pairLinked_high_step {r s : ℕ} (h : IsTorusPair r s) {y : ℕ} (hy : y < r) :
    ((y + s) % r + 1 ≠ r →
      PairLinked r s (pairHighStrand r s y) (pairHighStrand r s ((y + s) % r))) ∧
    ((y + s) % r + 1 = r → PairLinked r s (pairHighStrand r s y) (2 * pairC r s)) := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairConnected_arith h
  have hjump : PairLinked r s (pairHighStrand r s y) (pairWindow r s (y + s)) := by
    unfold pairHighStrand
    split_ifs with hy1
    · rw [show 2 * pairC r s - 1 = pairWindow r s (y + s) by simp only [pairWindow]; omega]
      exact pairLinked_refl (by simp only [pairWindow, pairStrands]; omega)
    · refine pairLinked_of_stPerm h (by simp only [pairWindow, pairStrands]; omega) ?_
      rw [stPerm_pairBlocks_foot h (by simp only [pairWindow]; omega)
        (by simp only [pairWindow]; omega)]
      rw [show pairWindow r s y + s = pairWindow r s (y + s) by simp only [pairWindow]; omega]
      exact pairLinked_refl (by simp only [pairWindow, pairStrands]; omega)
  obtain ⟨y', h1, h2, h3, h4⟩ := pairLinked_window h (y + s) (by omega) (by omega)
  have hrun : PairLinked r s (pairWindow r s r) (pairHighStrand r s 0) := by
    refine pairLinked_of_stPerm h (by simp only [pairWindow, pairStrands]; omega) ?_
    rw [stPerm_pairBlocks_toRun h (by simp only [pairWindow]; omega)]
    have h0 : pairHighStrand r s 0 = 2 * pairC r s - s - r := by
      simp only [pairHighStrand, pairWindow]; split_ifs <;> omega
    rw [h0]
    exact pairLinked_up h (2 * pairC r s - s - r - (pairC r s - s + 1)) _ (by omega) (by omega)
  refine ⟨fun hne ↦ pairLinked_trans hjump (pairLinked_trans h4 ?_), fun heq ↦
    pairLinked_trans hjump (pairLinked_trans h4 ?_)⟩
  · by_cases hr' : y' = r
    · subst hr'
      rw [Nat.mod_self] at h3
      rw [← h3]
      exact hrun
    · have hy' : y' % r = y' := Nat.mod_eq_of_lt (by omega)
      rw [hy'] at h3
      have hne' : y' + 1 ≠ r := by omega
      rw [← h3]
      simp only [pairHighStrand, hne', ite_false]
      exact pairLinked_refl (by simp only [pairWindow, pairStrands]; omega)
  · have hy' : y' + 1 = r := by
      by_cases hr' : y' = r
      · subst hr'
        rw [Nat.mod_self] at h3
        omega
      · rw [Nat.mod_eq_of_lt (by omega)] at h3
        omega
    refine pairLinked_of_stPerm h (by simp only [pairWindow, pairStrands]; omega) ?_
    rw [stPerm_pairBlocks_toExtra h (by simp only [pairWindow]; omega)]
    exact pairLinked_refl (by simp only [pairStrands]; omega)

/-- Adding `s` modulo `r` (coprime) runs through all residues: starting from `r - 1`, the
first `r - 1` steps avoid `r - 1`, and every residue is reached in fewer than `r` steps. -/
private theorem pair_mod_orbit {r s : ℕ} (hr : 2 ≤ r) (hcop : Nat.Coprime r s) :
    (∀ k, 1 ≤ k → k < r → (r - 1 + k * s) % r ≠ r - 1) ∧
      ∀ i < r, ∃ k < r, (r - 1 + k * s) % r = i := by
  refine ⟨fun k hk1 hk2 heq ↦ ?_, fun i hi ↦ ?_⟩
  · have h1 : r - 1 + k * s ≡ r - 1 + 0 [MOD r] := by
      unfold Nat.ModEq
      rw [heq, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    have h2 : r ∣ k * s := (Nat.modEq_zero_iff_dvd).1 (Nat.ModEq.add_left_cancel' _ h1)
    have h3 : r ∣ k := hcop.dvd_of_dvd_mul_right h2
    have := Nat.le_of_dvd (by omega) h3
    omega
  · obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm (by omega)
    refine ⟨a * (i + 1) % r, Nat.mod_lt _ (by omega), ?_⟩
    have e2 : s * a ≡ 1 [MOD r] := by
      unfold Nat.ModEq
      rw [ha, Nat.mod_eq_of_lt (by omega)]
    have h1 : a * (i + 1) % r * s ≡ i + 1 [MOD r] :=
      calc a * (i + 1) % r * s ≡ a * (i + 1) * s [MOD r] := (Nat.mod_modEq _ _).mul_right s
        _ = s * a * (i + 1) := by ring
        _ ≡ 1 * (i + 1) [MOD r] := e2.mul_right _
        _ = i + 1 := one_mul _
    have h2 := h1.add_left (r - 1)
    unfold Nat.ModEq at h2
    rw [h2, show r - 1 + (i + 1) = i + r by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

/-- If each anchor `A i` is linked to `A ((i + s) % r)` whenever that index is not `r - 1`,
all anchors are linked to `A (r - 1)`. -/
private theorem pairLinked_cycle {r s : ℕ} (h : IsTorusPair r s) (A : ℕ → ℕ)
    (hA : ∀ i < r, A i < pairStrands r s)
    (hstep : ∀ i < r, (i + s) % r + 1 ≠ r → PairLinked r s (A i) (A ((i + s) % r))) :
    ∀ i < r, PairLinked r s (A (r - 1)) (A i) := by
  obtain ⟨hr, hrs, hcop⟩ := h
  obtain ⟨h1, h2⟩ := pair_mod_orbit hr hcop
  have key : ∀ k < r, PairLinked r s (A (r - 1)) (A ((r - 1 + k * s) % r)) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
      exact pairLinked_refl (hA _ (by omega))
    | succ k ih =>
      intro hk
      have hi : (r - 1 + k * s) % r < r := Nat.mod_lt _ (by omega)
      have e : ((r - 1 + k * s) % r + s) % r = (r - 1 + (k + 1) * s) % r := by
        rw [Nat.mod_add_mod]
        congr 1
        ring
      refine pairLinked_trans (ih (by omega)) ?_
      rw [← e]
      refine hstep _ hi ?_
      rw [e]
      have := h1 (k + 1) (by omega) hk
      omega
  intro i hi
  obtain ⟨k, hk, rfl⟩ := h2 i hi
  exact key k hk

/-- Every position is linked to the extra strand `2c`. -/
private theorem pairLinked_extra {r s : ℕ} (h : IsTorusPair r s) {x : ℕ}
    (hx : x < pairStrands r s) : PairLinked r s x (2 * pairC r s) := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairConnected_arith h
  have hcop := h.2.2
  simp only [pairStrands] at hx
  -- all low strands are linked to `2c = pairLowStrand r s (r - 1)`
  have hlowA : ∀ i < r, PairLinked r s (pairLowStrand r s i) (2 * pairC r s) := by
    intro i hi
    have hc := pairLinked_cycle h (pairLowStrand r s)
      (fun i hi ↦ by simp only [pairLowStrand, pairStrands]; split_ifs <;> omega)
      (fun i hi hne ↦ (pairLinked_low_step h hi).1 (by rwa [Nat.add_comm i s] at hne)
        |> fun hl ↦ by rwa [Nat.add_comm s i] at hl) i hi
    have h2c : pairLowStrand r s (r - 1) = 2 * pairC r s := by
      simp only [pairLowStrand]; split_ifs <;> omega
    rw [h2c] at hc
    exact pairLinked_symm hc
  -- all high strands are linked to `2c - 1 = pairHighStrand r s (r - 1)`
  have hhighA : ∀ y < r, PairLinked r s (pairHighStrand r s y) (2 * pairC r s - 1) := by
    intro y hy
    have hc := pairLinked_cycle h (pairHighStrand r s)
      (fun i hi ↦ by simp only [pairHighStrand, pairWindow, pairStrands]; split_ifs <;> omega)
      (fun i hi hne ↦ (pairLinked_high_step h hi).1 hne) y hy
    have h2c : pairHighStrand r s (r - 1) = 2 * pairC r s - 1 := by
      simp only [pairHighStrand]; split_ifs <;> omega
    rw [h2c] at hc
    exact pairLinked_symm hc
  -- the two families are linked
  have hbridge : PairLinked r s (2 * pairC r s - 1) (2 * pairC r s) := by
    obtain ⟨j, hj, hj'⟩ : ∃ j < r, (s + j) % r + 1 = r := by
      refine ⟨(r - 1 + (r - 1) * s) % r, Nat.mod_lt _ (by omega), ?_⟩
      rw [Nat.add_mod_mod, show s + (r - 1 + (r - 1) * s) = r - 1 + r * s by
        rw [Nat.sub_mul, Nat.one_mul]
        have : s ≤ r * s := Nat.le_mul_of_pos_left s (by omega)
        omega]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      omega
    exact pairLinked_trans (pairLinked_symm ((pairLinked_low_step h hj).2 hj')) (hlowA j hj)
  have hhigh : ∀ y < r, PairLinked r s (pairHighStrand r s y) (2 * pairC r s) :=
    fun y hy ↦ pairLinked_trans (hhighA y hy) hbridge
  have hW0 : PairLinked r s (2 * pairC r s - s - r) (2 * pairC r s) := by
    have h0 : pairHighStrand r s 0 = 2 * pairC r s - s - r := by
      simp only [pairHighStrand, pairWindow]; split_ifs <;> omega
    rw [← h0]
    exact hhigh 0 (by omega)
  -- every position reaches one of the anchors
  by_cases h1 : x + 2 ≤ r
  · have := hlowA x (by omega)
    rwa [show pairLowStrand r s x = x by simp only [pairLowStrand]; split_ifs <;> omega] at this
  by_cases h2 : x = 2 * pairC r s
  · subst h2
    exact pairLinked_refl (by simp only [pairStrands]; omega)
  by_cases h3 : x + s ≤ pairC r s
  · refine pairLinked_trans (pairLinked_down h x (by omega) h3) ?_
    have := hlowA (r - 2) (by omega)
    rwa [show pairLowStrand r s (r - 2) = r - 2 by simp only [pairLowStrand]; split_ifs <;> omega]
      at this
  by_cases h4 : x + s + r ≤ 2 * pairC r s
  · exact pairLinked_trans
      (pairLinked_up h (2 * pairC r s - s - r - x) x (by omega) (by omega)) hW0
  -- the window and the staircase
  obtain ⟨y', h1', h2', -, h4'⟩ := pairLinked_window h (x + s + r - 2 * pairC r s) (by omega)
    (by omega)
  rw [show pairWindow r s (x + s + r - 2 * pairC r s) = x by simp only [pairWindow]; omega] at h4'
  refine pairLinked_trans h4' ?_
  by_cases hy1 : y' + 2 ≤ r
  · have := hhigh y' (by omega)
    rwa [show pairHighStrand r s y' = pairWindow r s y' by
      simp only [pairHighStrand]; split_ifs <;> omega] at this
  by_cases hy2 : y' + 1 = r
  · refine pairLinked_of_stPerm h (by simp only [pairWindow, pairStrands]; omega) ?_
    rw [stPerm_pairBlocks_toExtra h (by simp only [pairWindow]; omega)]
    exact pairLinked_refl (by simp only [pairStrands]; omega)
  · refine pairLinked_of_stPerm h (by simp only [pairWindow, pairStrands]; omega) ?_
    rw [stPerm_pairBlocks_toRun h (by simp only [pairWindow]; omega)]
    exact pairLinked_trans
      (pairLinked_up h (2 * pairC r s - s - r - (pairC r s - s + 1)) _ (by omega) (by omega)) hW0

/-- The closure of `pairWhiteheadWord r s` has one component. -/
theorem connected_pairWhiteheadWord {r s : ℕ} (h : IsTorusPair r s)
    (i j : Fin (pairStrands r s)) :
    ∃ n : ℕ, (strandPerm (pairStrands r s) (pairWhiteheadWord r s) ^ n) i = j := by
  obtain ⟨_, _, hi⟩ := pairLinked_extra h i.isLt
  obtain ⟨_, _, hj⟩ := pairLinked_extra h j.isLt
  exact (hi.trans hj.symm).exists_nat_pow_eq

end AJConjecture
