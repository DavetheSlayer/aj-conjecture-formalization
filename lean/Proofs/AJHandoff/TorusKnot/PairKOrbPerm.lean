import Mathlib
import AJHandoff.TorusKnot.PairKOrbPatPerm

/-!
# The strand map of `pairBlocks r s` in closed form

`stPerm_pairBlocks_orb`: the strand map of `pairBlocks r s` is `pairOrbPerm r s` on every position.
Route: the eleven stages of `AJHandoff.TorusKnot.PairKConnected` (`pairStage`, its evaluations
`pairStage_zero` … `pairStage_ten` and the macros `pair_head`, `pair_tail`, all private there):
copy them here under new names (the pattern lemmas are in `AJHandoff.TorusKnot.PairKOrbPatPerm`),
then split `pairOrbPerm` by region. For a low strand use the analogues of `pairStage_head_low`
(the first five stages send the low strand of index `i` to `2c - 2 - (s + i) % r`) and of
`pairStage_tail_low`, `pairStage_tail_mid`, `pairStage_tail_top`; on the other regions the macros
close the goal as in `stPerm_pairBlocks_down` … `stPerm_pairBlocks_stair`.

The remaining statements are arithmetic on `pairOrbPerm`: the top block `PairOrbTop` is invariant
except at `pairOrbH1`, which goes to `2c`, and the only position outside it that is sent into it
is sent to `T`. They use `pairC r s = (r - 1) s`, `s ≤ c`, `r + 1 ≤ s`, `E + s + r = c + 3`
(`pairConnected_arith`) and `(s + i) % r < r`.
-/

namespace AJConjecture

/-- The strand map of the pieces of `pairBlocks r s`, numbered in the order in which they act
on a strand (the last block acts first). -/
private def orbPermStage (r s : ℕ) : ℕ → ℕ → ℕ
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
private theorem stPerm_pairBlocks_orbStages (r s t : ℕ) :
    stPerm (pairBlocks r s) t = orbPermStage r s 10 (orbPermStage r s 9 (orbPermStage r s 8
      (orbPermStage r s 7 (orbPermStage r s 6 (orbPermStage r s 5 (orbPermStage r s 4
        (orbPermStage r s 3 (orbPermStage r s 2 (orbPermStage r s 1
          (orbPermStage r s 0 t)))))))))) := by
  simp only [pairBlocks, stPerm_append, stPerm, orbPermStage]

/-- The arithmetic of an admissible pair, with `1 ≤ E`. -/
private theorem orbPerm_arith {r s : ℕ} (h : IsTorusPair r s) :
    2 ≤ r ∧ r + 1 ≤ s ∧ 1 ≤ pairRunDown r s ∧ pairRunDown r s + s + r = pairC r s + 3 := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairOrb_arith h
  exact ⟨hr, hrs, by unfold pairRunDown; omega, hE⟩

/-- Stage `zero` of the strand map in closed form. -/
private theorem orbPermStage_zero {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    orbPermStage r s 0 t = if t + 1 = 2 * pairC r s then 2 * pairC r s
      else if t = 2 * pairC r s then 2 * pairC r s - 1 else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  simp only [orbPermStage, pairTop]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `five` of the strand map in closed form. -/
private theorem orbPermStage_five (r s t : ℕ) : orbPermStage r s 5 t = orbPermStage r s 0 t := rfl

/-- Stage `one` of the strand map in closed form. -/
private theorem orbPermStage_one {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    orbPermStage r s 1 t =
      if t + 3 ≤ r ∨ (2 * pairC r s + 1 ≤ t + s + r ∧ t + s + 1 < 2 * pairC r s)
      then 2 * pairC r s - s - 2 - t else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  simp only [orbPermStage, pairTop]
  rw [stPerm_orbSpread _ _ _ _ (by omega) (by omega)]
  split_ifs <;> omega

/-- Stage `two` of the strand map in closed form. -/
private theorem orbPermStage_two {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    orbPermStage r s 2 t = if t + s + 1 = 2 * pairC r s then 2 * pairC r s - 1
      else if t + 1 = 2 * pairC r s then 2 * pairC r s - 1 - s else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  simp only [orbPermStage, pairTop]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `three` of the strand map in closed form. -/
private theorem orbPermStage_three {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    orbPermStage r s 3 t = if t + 2 = r then 2 * pairC r s - s
      else if t + s = 2 * pairC r s then r - 2 else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  simp only [orbPermStage, pairTop]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `four` of the strand map in closed form. -/
private theorem orbPermStage_four {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    orbPermStage r s 4 t = if 2 * pairC r s < t + s ∧ t + 2 ≤ 2 * pairC r s then t - r
      else if 2 * pairC r s < t + s + r ∧ t + r + 2 ≤ 2 * pairC r s then
        2 * pairC r s - 2 - (2 * pairC r s - 2 - t) % r
      else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  simp only [orbPermStage, pairTop]
  rw [stPerm_orbStair (2 * pairC r s - 1 - r - 1) (2 * pairC r s - 1 - 1) r _ _ (by omega)
    (by omega) (by omega)]
  rw [show 2 * pairC r s - 1 - 1 = 2 * pairC r s - 2 by omega]
  split_ifs <;> omega

/-- Stage `six` of the strand map in closed form. -/
private theorem orbPermStage_six {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    orbPermStage r s 6 t = if t + r + 1 = 2 * pairC r s then 2 * pairC r s - 1
      else if t + 1 = 2 * pairC r s then 2 * pairC r s - 1 - r else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  simp only [orbPermStage, pairTop]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `seven` of the strand map in closed form. -/
private theorem orbPermStage_seven {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    orbPermStage r s 7 t = if t + s + r = 2 * pairC r s then 2 * pairC r s - r
      else if t + r = 2 * pairC r s then 2 * pairC r s - s - r else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  simp only [orbPermStage, pairTop, pairRunUp]
  simp only [SBlock.perm]
  split_ifs <;> omega

/-- Stage `eight` of the strand map in closed form. -/
private theorem orbPermStage_eight {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    orbPermStage r s 8 t = if t + s + r = 2 * pairC r s then pairC r s - s + 1
      else if pairC r s + 1 ≤ t + s ∧ t + s + r < 2 * pairC r s then t + 1 else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  simp only [orbPermStage, pairRunUp]
  rw [stPerm_orbRunUp _ _ _ _ (by omega)]
  split_ifs <;> omega

/-- Stage `nine` of the strand map in closed form. -/
private theorem orbPermStage_nine {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    orbPermStage r s 9 t = if t + 2 = r then pairC r s - s + 1
      else if r ≤ t + 1 ∧ t + s ≤ pairC r s + 1 then t - 1 else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  simp only [orbPermStage]
  rw [stPerm_orbRunDown _ _ _ _ (by omega) (by omega)]
  split_ifs <;> omega

/-- Stage `ten` of the strand map in closed form. -/
private theorem orbPermStage_ten {r s : ℕ} (h : IsTorusPair r s) (t : ℕ) :
    orbPermStage r s 10 t = if t + 2 < r ∨ (2 * pairC r s < t + r ∧ t + 2 ≤ 2 * pairC r s)
      then 2 * pairC r s - 2 - t else t := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  simp only [orbPermStage, pairTop]
  rw [stPerm_orbNested _ _ _ (by omega)]
  split_ifs <;> omega

/-- Evaluate the stages `0`–`4` of the strand map one after another. -/
local macro "orb_head " h:term : tactic => `(tactic| (
  all_goals (rw [orbPermStage_zero $h]; split_ifs <;> try omega)
  all_goals (rw [orbPermStage_one $h]; split_ifs <;> try omega)
  all_goals (rw [orbPermStage_two $h]; split_ifs <;> try omega)
  all_goals (rw [orbPermStage_three $h]; split_ifs <;> try omega)
  all_goals (rw [orbPermStage_four $h]; split_ifs <;> try omega)))

/-- Evaluate the stages `5`–`10` of the strand map one after another. -/
local macro "orb_tail " h:term : tactic => `(tactic| (
  all_goals (rw [orbPermStage_five, orbPermStage_zero $h]; split_ifs <;> try omega)
  all_goals (rw [orbPermStage_six $h]; split_ifs <;> try omega)
  all_goals (rw [orbPermStage_seven $h]; split_ifs <;> try omega)
  all_goals (rw [orbPermStage_eight $h]; split_ifs <;> try omega)
  all_goals (rw [orbPermStage_nine $h]; split_ifs <;> try omega)
  all_goals (rw [orbPermStage_ten $h]; split_ifs <;> try omega)))

/-- A value `a - x % r` only depends on `x` modulo `r`. -/
private theorem orbPerm_sub_mod_congr {a x y r : ℕ} (hxy : x = y ∨ x + r = y) :
    a - x % r = a - y % r := by
  rcases hxy with rfl | rfl
  · rfl
  · rw [Nat.add_mod_right]

/-- The first five stages send the low strand of index `i` to `2c - 2 - (s + i) % r`. -/
private theorem orbPermStage_head_low {r s : ℕ} (h : IsTorusPair r s) {i : ℕ} (hi : i < r) :
    orbPermStage r s 4 (orbPermStage r s 3 (orbPermStage r s 2 (orbPermStage r s 1
      (orbPermStage r s 0 (if i + 1 = r then 2 * pairC r s else i))))) =
      2 * pairC r s - 2 - (s + i) % r := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  split_ifs
  all_goals orb_head h
  all_goals first
    | (apply orbPerm_sub_mod_congr; omega)
    | (have hm : (s + i) % r = s + i - r := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
       omega)

/-- The last six stages on `2c - 2 - u`, by the value of `u < r`. -/
private theorem orbPermStage_tail_low {r s : ℕ} (h : IsTorusPair r s) {u : ℕ} (hu : u < r) :
    orbPermStage r s 10 (orbPermStage r s 9 (orbPermStage r s 8 (orbPermStage r s 7
      (orbPermStage r s 6 (orbPermStage r s 5 (2 * pairC r s - 2 - u)))))) =
      if u + 3 ≤ r then u else if u + 2 = r then pairC r s - s else pairTop r s := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  unfold pairTop
  split_ifs
  all_goals orb_tail h

/-- The strand map of `pairBlocks r s` is `pairOrbPerm r s`. -/
theorem stPerm_pairBlocks_orb {r s : ℕ} (h : IsTorusPair r s) {t : ℕ}
    (ht : t < pairStrands r s) : stPerm (pairBlocks r s) t = pairOrbPerm r s t := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  have hst : t < 2 * pairC r s + 1 := ht
  unfold pairOrbPerm
  by_cases hlow : t + 2 ≤ r ∨ t = 2 * pairC r s
  · rw [ite_eq_left hlow]
    have hi : pairOrbLow r s t < r := by unfold pairOrbLow; split_ifs <;> omega
    have ht' : t = if pairOrbLow r s t + 1 = r then 2 * pairC r s else pairOrbLow r s t := by
      unfold pairOrbLow; split_ifs <;> omega
    generalize pairOrbLow r s t = i at hi ht'
    subst ht'
    rw [stPerm_pairBlocks_orbStages, orbPermStage_head_low h hi,
      orbPermStage_tail_low h (Nat.mod_lt _ (by omega))]
    rfl
  · rw [ite_eq_right hlow, stPerm_pairBlocks_orbStages]
    split_ifs
    all_goals orb_head h
    all_goals orb_tail h

/-- `pairOrbPerm` maps positions to positions. -/
theorem pairOrbPerm_lt {r s : ℕ} (h : IsTorusPair r s) {t : ℕ} (ht : t < pairStrands r s) :
    pairOrbPerm r s t < pairStrands r s := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  have hst : t < 2 * pairC r s + 1 := ht
  have hm : pairOrbNext r s (pairOrbLow r s t) < r := Nat.mod_lt _ (by omega)
  unfold pairOrbPerm pairStrands pairTop
  split_ifs <;> omega

/-- The positions `T` and `pairOrbH1` are in the top block, `0` and `2c` are not, and
`pairOrbH1 ≠ T`. -/
theorem pairOrbTop_basic {r s : ℕ} (h : IsTorusPair r s) :
    PairOrbTop r s (pairTop r s) ∧ PairOrbTop r s (pairOrbH1 r s) ∧ ¬ PairOrbTop r s 0 ∧
      ¬ PairOrbTop r s (2 * pairC r s) ∧ pairOrbH1 r s ≠ pairTop r s ∧
      2 * pairC r s < pairStrands r s := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  unfold PairOrbTop pairTop pairOrbH1 pairStrands
  omega

/-- The top block is invariant under `pairOrbPerm` except at `pairOrbH1`. -/
theorem pairOrbPerm_top {r s : ℕ} (h : IsTorusPair r s) {t : ℕ} (ht : PairOrbTop r s t)
    (hH : t ≠ pairOrbH1 r s) : PairOrbTop r s (pairOrbPerm r s t) := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  unfold PairOrbTop pairTop at *
  unfold pairOrbH1 at hH
  unfold pairOrbPerm
  split_ifs <;> omega

/-- A position outside the top block that `pairOrbPerm` sends into it is sent to `T`. -/
theorem pairOrbPerm_enter {r s : ℕ} (h : IsTorusPair r s) {t : ℕ} (ht : t < pairStrands r s)
    (hout : ¬ PairOrbTop r s t) (hin : PairOrbTop r s (pairOrbPerm r s t)) :
    pairOrbPerm r s t = pairTop r s := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  have hst : t < 2 * pairC r s + 1 := ht
  have hm : pairOrbNext r s (pairOrbLow r s t) < r := Nat.mod_lt _ (by omega)
  unfold PairOrbTop at hout hin
  unfold pairOrbPerm at hin ⊢
  unfold pairTop at *
  split_ifs at hin ⊢ <;> omega

/-- The strand `pairOrbH1` goes to `2c`. -/
theorem pairOrbPerm_H1 {r s : ℕ} (h : IsTorusPair r s) :
    pairOrbPerm r s (pairOrbH1 r s) = 2 * pairC r s := by
  obtain ⟨hr, hrs, hc, hE⟩ := orbPerm_arith h
  unfold pairOrbPerm pairOrbH1
  split_ifs <;> omega

/-- Computational check of the arithmetic statements above. -/
def pairOrbCheckRegions (r s : ℕ) : Bool :=
  let top := fun t ↦ decide (pairC r s - s + 1 ≤ t ∧ t ≤ pairTop r s)
  pairOrbPerm r s (pairOrbH1 r s) == 2 * pairC r s &&
    (List.range (pairStrands r s)).all fun t ↦
      decide (pairOrbPerm r s t < pairStrands r s) &&
        (!(top t && t != pairOrbH1 r s) || top (pairOrbPerm r s t)) &&
        (top t || !top (pairOrbPerm r s t) || pairOrbPerm r s t == pairTop r s)

#guard [(2, 3), (2, 5), (3, 4), (3, 5), (3, 7), (4, 5), (5, 7), (4, 9), (5, 8)].all fun p ↦
  pairOrbCheckRegions p.1 p.2

end AJConjecture
