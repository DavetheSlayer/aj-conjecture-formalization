import Mathlib
import AJHandoff.TorusKnot.PairKOrbStage

/-!
# Strand loops of `pairBlocks r s`: the low strands (crux)

The low strand of low index `i` (the position `i ≤ r - 2`, or `2c` for `i = r - 1`) collects,
from the top: the right descents `D'_(r-3) ⋯ D'_(r-2-i)` (the top-right climb `C` for `2c`); on
the staircase stage it climbs to the top of its residue class and collects all rounds
`R_(s-1), …, R_0` except those `R_u` with `u ≡ j + 1 (mod r)`, `j = (s + i) % r`
(`pairOrbSkip`); then the tail `pairOrbSuf r s L j`: the left climbs `A_j ⋯ A_0` if `j ≤ r - 3`,
the big climb, the increasing run, the first block of the decreasing run and all left climbs if
`j = r - 2`, nothing if `j = r - 1` (it then ends at `T`). This is `pairOrbSlotLoop`.

Route: `stLoop_pairBlocks_stages`. The low strand meets stage 1 (`stLoop_orbSpread`), stage 2
(`C`, only for `2c`), stage 3 (`R_(s-1)`, unless `u = s - 1` is skipped) and stage 4 on its lower
part (`stLoop_orbStair` with `d = r`: the blocks `R_(j'+1)` with `(y - t - j') % r ≠ 0`), then
stage 6 (`R_0`), and the tail stages as `pairStage_tail_low/mid/top` in
`AJHandoff.TorusKnot.PairKConnected`. The filtered product of stages 3, 4, 6 is `pairOrbSkip`
after reindexing `u = j' + 1` (stage 4), `u = s - 1` (stage 3), `u = 0` (stage 6); the residue
condition is `(y - t - j') % r ≠ 0 ↔ (j' + 1) % r ≠ (j + 1) % r` with `t = 2c - 2 - u'`-type
positions from `pairStage_head_low`. Checked by computer (`pairOrbCheckLoop`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- Split the conditionals of the goal and close every branch by `omega`. -/
local macro "orb_ifs" : tactic => `(tactic| (split_ifs <;> omega))

/-- A difference is divisible by `r` iff the successors agree modulo `r`. -/
private theorem sub_mod_eq_zero_iff_orbLow {r D j j' : ℕ} (hj' : j' ≤ D) (hDj : D % r = j % r) :
    (D - j') % r = 0 ↔ (j' + 1) % r = (j + 1) % r := by
  rw [← Nat.dvd_iff_mod_eq_zero, ← Nat.modEq_iff_dvd' hj']
  constructor
  · intro h1
    exact Nat.ModEq.add_right 1 (h1.trans hDj)
  · intro h2
    exact (Nat.ModEq.add_right_cancel' 1 h2).trans hDj.symm

/-- Adding `0 < k < r` changes the residue modulo `r`. -/
private theorem add_mod_ne_self_orbLow {a k r : ℕ} (hk : 0 < k) (hkr : k < r) :
    (a + k) % r ≠ a % r := by
  intro h
  have h' : a + k ≡ a + 0 [MOD r] := h
  have := Nat.ModEq.add_left_cancel' a h'
  unfold Nat.ModEq at this
  rw [Nat.mod_eq_of_lt hkr, Nat.zero_mod] at this
  omega

/-- The rounds collected by a low strand, split into the last round, the staircase rounds and the
first round. -/
private theorem pairOrbSkip_split_orbLow (r s : ℕ) (L : ℕ → G) (ρ : ℕ) (hs : 2 ≤ s) :
    pairOrbSkip r s L ρ =
      (if (s - 1) % r = ρ % r then 1 else L (pairIdxR r s (s - 1))) *
        ((List.range (s - 2)).reverse.map fun j ↦
          if (j + 1) % r = ρ % r then 1 else L (pairIdxR r s (j + 1))).prod *
        (if 0 % r = ρ % r then 1 else L (pairIdxR r s 0)) := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 2 := ⟨s - 2, by omega⟩
  unfold pairOrbSkip
  rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega, List.range_succ,
    List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons,
    List.prod_cons, List.range_succ_eq_map, List.reverse_cons, List.map_append,
    List.prod_append, List.map_reverse, List.map_map, ← List.map_reverse, mul_assoc]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Function.comp_def, Nat.succ_eq_add_one]

/-- Stage `4` on its lower part: a low strand climbs and skips one residue class of rounds. -/
private theorem stLoop_pairOrbStage_four_orbLow {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {p D j : ℕ} (hpD : p + D + 2 = 2 * pairC r s)
    (hD1 : s ≤ D + 2) (hD2 : D + 3 ≤ s + r) (hDj : D % r = j % r) :
    stLoop (pairStrands r s) (pairOrbStage r s 4) (runTop (pairStrands r s) (pairOrbPre r s 4) f)
        p = ((List.range (s - 2)).reverse.map fun j' ↦
          (if (j' + 1) % r = (j + 1) % r then 1
            else loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (j' + 1)))).prod := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  rw [stLoop_pairOrbStage_four h]
  congr 1
  refine List.map_congr_left fun j' hj' ↦ ?_
  rw [List.mem_reverse, List.mem_range] at hj'
  have hm := sub_mod_eq_zero_iff_orbLow (j' := j') (show j' ≤ D by omega) hDj
  rw [show pairTop r s - 1 - p - j' = D - j' by omega]
  split_ifs <;> first | rfl | omega

set_option linter.unusedSimpArgs false in
/-- The tail of a low strand whose next low index is `j ≤ r - 3`. -/
private theorem stLoop_low_tail_climb {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t j : ℕ} (hj : j + 3 ≤ r)
    (h5 : pairOrbPos r s 5 t = 2 * pairC r s - 2 - j) (X : G) :
    X * stLoop (pairStrands r s) (pairOrbStage r s 5)
          (runTop (pairStrands r s) (pairOrbPre r s 5) f) (pairOrbPos r s 5 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 6)
          (runTop (pairStrands r s) (pairOrbPre r s 6) f) (pairOrbPos r s 6 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 7)
          (runTop (pairStrands r s) (pairOrbPre r s 7) f) (pairOrbPos r s 7 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 8)
          (runTop (pairStrands r s) (pairOrbPre r s 8) f) (pairOrbPos r s 8 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 9)
          (runTop (pairStrands r s) (pairOrbPre r s 9) f) (pairOrbPos r s 9 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 10)
          (runTop (pairStrands r s) (pairOrbPre r s 10) f) (pairOrbPos r s 10 t) =
      X * ((if 0 % r = (j + 1) % r then 1
            else loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s 0)) *
        pairOrbSuf r s (loopAt (pairStrands r s) (pairBlocks r s) f) j) := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  have e6 : pairOrbPos r s 6 t = 2 * pairC r s - 2 - j := by
    rw [pairOrbPos_succ, h5, stPerm_pairOrbStage_five h]
    orb_ifs
  have e7 : pairOrbPos r s 7 t = 2 * pairC r s - 2 - j := by
    rw [pairOrbPos_succ, e6, stPerm_pairOrbStage_six h]
    orb_ifs
  have e8 : pairOrbPos r s 8 t = 2 * pairC r s - 2 - j := by
    rw [pairOrbPos_succ, e7, stPerm_pairOrbStage_seven h]
    clear e6
    orb_ifs
  have e9 : pairOrbPos r s 9 t = 2 * pairC r s - 2 - j := by
    rw [pairOrbPos_succ, e8, stPerm_pairOrbStage_eight h]
    clear e6 e7
    orb_ifs
  have e10 : pairOrbPos r s 10 t = 2 * pairC r s - 2 - j := by
    rw [pairOrbPos_succ, e9, stPerm_pairOrbStage_nine h]
    clear e6 e7 e8
    orb_ifs
  rw [e6, e7, e8, e9, e10, h5]
  clear e6 e7 e8 e9 e10 h5
  rw [stLoop_pairOrbStage_five_off h f (p := 2 * pairC r s - 2 - j) (by omega),
    stLoop_pairOrbStage_six_on h f (p := 2 * pairC r s - 2 - j) (by omega),
    stLoop_pairOrbStage_seven_off h f (p := 2 * pairC r s - 2 - j) (by omega),
    stLoop_pairOrbStage_eight_eq h f (p := 2 * pairC r s - 2 - j) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_nine_eq h f (p := 2 * pairC r s - 2 - j) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_ten_eq h f (p := 2 * pairC r s - 2 - j) (lo := 0)
      (len := j + 1) (by omega) (fun j hj ↦ by omega)]
  rw [Nat.zero_mod, Nat.mod_eq_of_lt (show j + 1 < r by omega),
    ite_eq_right (show ¬ (0 = j + 1) by omega)]
  unfold pairOrbSuf
  rw [ite_eq_left hj]
  simp only [one_mul, mul_one, descProd_zero_orb, mul_assoc]

set_option linter.unusedSimpArgs false in
/-- The tail of a low strand whose next low index is `r - 2`. -/
private theorem stLoop_low_tail_mid {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t j : ℕ} (hj : j + 2 = r)
    (h5 : pairOrbPos r s 5 t = 2 * pairC r s - 2 - j) (X : G) :
    X * stLoop (pairStrands r s) (pairOrbStage r s 5)
          (runTop (pairStrands r s) (pairOrbPre r s 5) f) (pairOrbPos r s 5 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 6)
          (runTop (pairStrands r s) (pairOrbPre r s 6) f) (pairOrbPos r s 6 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 7)
          (runTop (pairStrands r s) (pairOrbPre r s 7) f) (pairOrbPos r s 7 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 8)
          (runTop (pairStrands r s) (pairOrbPre r s 8) f) (pairOrbPos r s 8 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 9)
          (runTop (pairStrands r s) (pairOrbPre r s 9) f) (pairOrbPos r s 9 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 10)
          (runTop (pairStrands r s) (pairOrbPre r s 10) f) (pairOrbPos r s 10 t) =
      X * ((if 0 % r = (j + 1) % r then 1
            else loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s 0)) *
        pairOrbSuf r s (loopAt (pairStrands r s) (pairBlocks r s) f) j) := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  have e6 : pairOrbPos r s 6 t = 2 * pairC r s - r := by
    rw [pairOrbPos_succ, h5, stPerm_pairOrbStage_five h]
    orb_ifs
  have e7 : pairOrbPos r s 7 t = 2 * pairC r s - r := by
    rw [pairOrbPos_succ, e6, stPerm_pairOrbStage_six h]
    orb_ifs
  have e8 : pairOrbPos r s 8 t = 2 * pairC r s - s - r := by
    rw [pairOrbPos_succ, e7, stPerm_pairOrbStage_seven h]
    clear e6
    orb_ifs
  have e9 : pairOrbPos r s 9 t = pairC r s - s + 1 := by
    rw [pairOrbPos_succ, e8, stPerm_pairOrbStage_eight h]
    clear e6 e7
    orb_ifs
  have e10 : pairOrbPos r s 10 t = pairC r s - s := by
    rw [pairOrbPos_succ, e9, stPerm_pairOrbStage_nine h]
    clear e6 e7 e8
    orb_ifs
  rw [e6, e7, e8, e9, e10, h5]
  clear e6 e7 e8 e9 e10 h5
  rw [stLoop_pairOrbStage_five_off h f (p := 2 * pairC r s - 2 - j) (by omega),
    stLoop_pairOrbStage_six_on h f (p := 2 * pairC r s - r) (by omega),
    stLoop_pairOrbStage_seven_on h f (p := 2 * pairC r s - r) (by omega),
    stLoop_pairOrbStage_eight_eq h f (p := 2 * pairC r s - s - r) (lo := 0)
      (len := pairRunUp r s) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_nine_eq h f (p := pairC r s - s + 1) (lo := 0)
      (len := 1) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_ten_eq h f (p := pairC r s - s) (lo := 0)
      (len := r - 2) (by omega) (fun j hj ↦ by omega)]
  rw [Nat.zero_mod, Nat.mod_eq_of_lt (show j + 1 < r by omega),
    ite_eq_right (show ¬ (0 = j + 1) by omega)]
  unfold pairOrbSuf
  rw [ite_eq_right (show ¬ (j + 3 ≤ r) by omega), ite_eq_left hj,
    descProd_congr_orb (fun j' ↦ loopAt (pairStrands r s) (pairBlocks r s) f
      (r - 2 + pairRunDown r s + j')) (loopAt (pairStrands r s) (pairBlocks r s) f) 0
      (r - 2 + pairRunDown r s) (pairRunUp r s) fun i _ ↦ by rw [Nat.zero_add]]
  simp only [one_mul, mul_one, descProd_one_orb, Nat.add_zero, mul_assoc]

set_option linter.unusedSimpArgs false in
/-- The tail of a low strand whose next low index is `r - 1`. -/
private theorem stLoop_low_tail_top {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t j : ℕ} (hj : j + 1 = r)
    (h5 : pairOrbPos r s 5 t = 2 * pairC r s - 2 - j) (X : G) :
    X * stLoop (pairStrands r s) (pairOrbStage r s 5)
          (runTop (pairStrands r s) (pairOrbPre r s 5) f) (pairOrbPos r s 5 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 6)
          (runTop (pairStrands r s) (pairOrbPre r s 6) f) (pairOrbPos r s 6 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 7)
          (runTop (pairStrands r s) (pairOrbPre r s 7) f) (pairOrbPos r s 7 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 8)
          (runTop (pairStrands r s) (pairOrbPre r s 8) f) (pairOrbPos r s 8 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 9)
          (runTop (pairStrands r s) (pairOrbPre r s 9) f) (pairOrbPos r s 9 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 10)
          (runTop (pairStrands r s) (pairOrbPre r s 10) f) (pairOrbPos r s 10 t) =
      X * ((if 0 % r = (j + 1) % r then 1
            else loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s 0)) *
        pairOrbSuf r s (loopAt (pairStrands r s) (pairBlocks r s) f) j) := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  have e6 : pairOrbPos r s 6 t = 2 * pairC r s - 1 - r := by
    rw [pairOrbPos_succ, h5, stPerm_pairOrbStage_five h]
    orb_ifs
  have e7 : pairOrbPos r s 7 t = 2 * pairC r s - 1 := by
    rw [pairOrbPos_succ, e6, stPerm_pairOrbStage_six h]
    orb_ifs
  have e8 : pairOrbPos r s 8 t = 2 * pairC r s - 1 := by
    rw [pairOrbPos_succ, e7, stPerm_pairOrbStage_seven h]
    clear e6
    orb_ifs
  have e9 : pairOrbPos r s 9 t = 2 * pairC r s - 1 := by
    rw [pairOrbPos_succ, e8, stPerm_pairOrbStage_eight h]
    clear e6 e7
    orb_ifs
  have e10 : pairOrbPos r s 10 t = 2 * pairC r s - 1 := by
    rw [pairOrbPos_succ, e9, stPerm_pairOrbStage_nine h]
    clear e6 e7 e8
    orb_ifs
  rw [e6, e7, e8, e9, e10, h5]
  clear e6 e7 e8 e9 e10 h5
  rw [stLoop_pairOrbStage_five_off h f (p := 2 * pairC r s - 2 - j) (by omega),
    stLoop_pairOrbStage_six_off h f (p := 2 * pairC r s - 1 - r) (by omega),
    stLoop_pairOrbStage_seven_off h f (p := 2 * pairC r s - 1) (by omega),
    stLoop_pairOrbStage_eight_eq h f (p := 2 * pairC r s - 1) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_nine_eq h f (p := 2 * pairC r s - 1) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_ten_eq h f (p := 2 * pairC r s - 1) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega)]
  rw [Nat.zero_mod, hj, Nat.mod_self, ite_eq_left rfl]
  unfold pairOrbSuf
  rw [ite_eq_right (show ¬ (j + 3 ≤ r) by omega), ite_eq_right (show ¬ (j + 2 = r) by omega)]
  simp only [one_mul, mul_one, descProd_zero_orb]

set_option linter.unusedSimpArgs false in
/-- The head of the low strand of index `i ≤ r - 3`. -/
private theorem stLoop_low_head_climb {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t i : ℕ} (hi : i + 3 ≤ r) (ht : t = i) :
    pairOrbPos r s 5 t = 2 * pairC r s - 2 - pairOrbNext r s i ∧
    stLoop (pairStrands r s) (pairOrbStage r s 0)
          (runTop (pairStrands r s) (pairOrbPre r s 0) f) t *
        stLoop (pairStrands r s) (pairOrbStage r s 1)
          (runTop (pairStrands r s) (pairOrbPre r s 1) f) (pairOrbPos r s 1 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 2)
          (runTop (pairStrands r s) (pairOrbPre r s 2) f) (pairOrbPos r s 2 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 3)
          (runTop (pairStrands r s) (pairOrbPre r s 3) f) (pairOrbPos r s 3 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 4)
          (runTop (pairStrands r s) (pairOrbPre r s 4) f) (pairOrbPos r s 4 t) =
      descProd (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxDp r s j))
        (r - 2 - i) i *
        (if (s - 1) % r = (pairOrbNext r s i + 1) % r then 1
            else loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (s - 1))) *
        ((List.range (s - 2)).reverse.map fun j' ↦
          (if (j' + 1) % r = (pairOrbNext r s i + 1) % r then 1
            else loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (j' + 1)))).prod := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  have e1 : pairOrbPos r s 1 t = t := by
    rw [pairOrbPos_succ, pairOrbPos_zero, stPerm_pairOrbStage_zero h]
    orb_ifs
  have e2 : pairOrbPos r s 2 t = 2 * pairC r s - s - 2 - i := by
    rw [pairOrbPos_succ, e1, stPerm_pairOrbStage_one h]
    orb_ifs
  have e3 : pairOrbPos r s 3 t = 2 * pairC r s - s - 2 - i := by
    rw [pairOrbPos_succ, e2, stPerm_pairOrbStage_two h]
    clear e1
    orb_ifs
  have e4 : pairOrbPos r s 4 t = 2 * pairC r s - s - 2 - i := by
    rw [pairOrbPos_succ, e3, stPerm_pairOrbStage_three h]
    clear e1 e2
    orb_ifs
  have hDj : (s + i) % r = pairOrbNext r s i % r := by
    unfold pairOrbNext; rw [Nat.mod_mod]
  refine ⟨?_, ?_⟩
  · rw [pairOrbPos_succ, e4, stPerm_pairOrbStage_four h]
    split_ifs <;> try omega
    unfold pairOrbNext
    rw [show 2 * pairC r s - 2 - (2 * pairC r s - s - 2 - i) = s + i by omega]
  rw [e1, e2, e3, e4]
  clear e1 e2 e3 e4
  rw [stLoop_pairOrbStage_zero_off h f (p := t) (by omega),
    stLoop_pairOrbStage_one_eq h f (p := t) (lo := r - 2 - i)
      (len := i) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_two_off h f (p := 2 * pairC r s - s - 2 - i) (by omega),
    stLoop_pairOrbStage_three_on h f (p := 2 * pairC r s - s - 2 - i) (by omega),
    stLoop_pairOrbStage_four_orbLow h f (p := 2 * pairC r s - s - 2 - i) (D := s + i)
      (by omega) (by omega) (by omega) hDj]
  rw [ite_eq_right (show ¬ ((s - 1) % r = (pairOrbNext r s i + 1) % r) by
    unfold pairOrbNext
    rw [Nat.mod_add_mod, show s + i + 1 = s - 1 + (i + 2) by omega]
    exact fun h' ↦ add_mod_ne_self_orbLow (by omega) (by omega) h'.symm)]
  simp only [one_mul, mul_one]

set_option linter.unusedSimpArgs false in
/-- The head of the low strand of index `i = r - 2`. -/
private theorem stLoop_low_head_mid {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t i : ℕ} (hi : i + 2 = r) (ht : t = i) :
    pairOrbPos r s 5 t = 2 * pairC r s - 2 - pairOrbNext r s i ∧
    stLoop (pairStrands r s) (pairOrbStage r s 0)
          (runTop (pairStrands r s) (pairOrbPre r s 0) f) t *
        stLoop (pairStrands r s) (pairOrbStage r s 1)
          (runTop (pairStrands r s) (pairOrbPre r s 1) f) (pairOrbPos r s 1 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 2)
          (runTop (pairStrands r s) (pairOrbPre r s 2) f) (pairOrbPos r s 2 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 3)
          (runTop (pairStrands r s) (pairOrbPre r s 3) f) (pairOrbPos r s 3 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 4)
          (runTop (pairStrands r s) (pairOrbPre r s 4) f) (pairOrbPos r s 4 t) =
      descProd (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxDp r s j))
        (r - 2 - i) i *
        (if (s - 1) % r = (pairOrbNext r s i + 1) % r then 1
            else loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (s - 1))) *
        ((List.range (s - 2)).reverse.map fun j' ↦
          (if (j' + 1) % r = (pairOrbNext r s i + 1) % r then 1
            else loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (j' + 1)))).prod := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  have e1 : pairOrbPos r s 1 t = t := by
    rw [pairOrbPos_succ, pairOrbPos_zero, stPerm_pairOrbStage_zero h]
    orb_ifs
  have e2 : pairOrbPos r s 2 t = t := by
    rw [pairOrbPos_succ, e1, stPerm_pairOrbStage_one h]
    orb_ifs
  have e3 : pairOrbPos r s 3 t = t := by
    rw [pairOrbPos_succ, e2, stPerm_pairOrbStage_two h]
    clear e1
    orb_ifs
  have e4 : pairOrbPos r s 4 t = 2 * pairC r s - s := by
    rw [pairOrbPos_succ, e3, stPerm_pairOrbStage_three h]
    clear e1 e2
    orb_ifs
  have hDj : (s - 2) % r = pairOrbNext r s i % r := by
    unfold pairOrbNext; rw [Nat.mod_mod, show s + i = s - 2 + r by omega, Nat.add_mod_right]
  refine ⟨?_, ?_⟩
  · rw [pairOrbPos_succ, e4, stPerm_pairOrbStage_four h]
    unfold pairOrbNext
    split_ifs with h1 h2
    · omega
    · rw [show 2 * pairC r s - 2 - (2 * pairC r s - s) = s - 2 by omega,
        show s + i = s - 2 + r by omega, Nat.add_mod_right]
    · have hm : (s + i) % r = s + i - r := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  rw [e1, e2, e3, e4]
  clear e1 e2 e3 e4
  rw [stLoop_pairOrbStage_zero_off h f (p := t) (by omega),
    stLoop_pairOrbStage_one_eq h f (p := t) (lo := r - 2 - i)
      (len := i) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_two_off h f (p := t) (by omega),
    stLoop_pairOrbStage_three_off h f (p := t) (by omega),
    stLoop_pairOrbStage_four_orbLow h f (p := 2 * pairC r s - s) (D := s - 2)
      (by omega) (by omega) (by omega) hDj]
  rw [ite_eq_left (show (s - 1) % r = (pairOrbNext r s i + 1) % r by
    unfold pairOrbNext
    rw [Nat.mod_add_mod, show s + i + 1 = s - 1 + r by omega, Nat.add_mod_right])]
  simp only [one_mul, mul_one]

set_option linter.unusedSimpArgs false in
/-- The head of the low strand `2c` (index `i = r - 1`). -/
private theorem stLoop_low_head_top {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t i : ℕ} (hi : i + 1 = r) (ht : t = 2 * pairC r s) :
    pairOrbPos r s 5 t = 2 * pairC r s - 2 - pairOrbNext r s i ∧
    stLoop (pairStrands r s) (pairOrbStage r s 0)
          (runTop (pairStrands r s) (pairOrbPre r s 0) f) t *
        stLoop (pairStrands r s) (pairOrbStage r s 1)
          (runTop (pairStrands r s) (pairOrbPre r s 1) f) (pairOrbPos r s 1 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 2)
          (runTop (pairStrands r s) (pairOrbPre r s 2) f) (pairOrbPos r s 2 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 3)
          (runTop (pairStrands r s) (pairOrbPre r s 3) f) (pairOrbPos r s 3 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 4)
          (runTop (pairStrands r s) (pairOrbPre r s 4) f) (pairOrbPos r s 4 t) =
      loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxC r s) *
        (if (s - 1) % r = (pairOrbNext r s i + 1) % r then 1
            else loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (s - 1))) *
        ((List.range (s - 2)).reverse.map fun j' ↦
          (if (j' + 1) % r = (pairOrbNext r s i + 1) % r then 1
            else loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (j' + 1)))).prod := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  have e1 : pairOrbPos r s 1 t = 2 * pairC r s - 1 := by
    rw [pairOrbPos_succ, pairOrbPos_zero, stPerm_pairOrbStage_zero h]
    orb_ifs
  have e2 : pairOrbPos r s 2 t = 2 * pairC r s - 1 := by
    rw [pairOrbPos_succ, e1, stPerm_pairOrbStage_one h]
    orb_ifs
  have e3 : pairOrbPos r s 3 t = 2 * pairC r s - 1 - s := by
    rw [pairOrbPos_succ, e2, stPerm_pairOrbStage_two h]
    clear e1
    orb_ifs
  have e4 : pairOrbPos r s 4 t = 2 * pairC r s - 1 - s := by
    rw [pairOrbPos_succ, e3, stPerm_pairOrbStage_three h]
    clear e1 e2
    orb_ifs
  have hDj : (s - 1) % r = pairOrbNext r s i % r := by
    unfold pairOrbNext; rw [Nat.mod_mod, show s + i = s - 1 + r by omega, Nat.add_mod_right]
  refine ⟨?_, ?_⟩
  · rw [pairOrbPos_succ, e4, stPerm_pairOrbStage_four h]
    unfold pairOrbNext
    split_ifs with h1 h2
    · omega
    · rw [show 2 * pairC r s - 2 - (2 * pairC r s - 1 - s) = s - 1 by omega,
        show s + i = s - 1 + r by omega, Nat.add_mod_right]
    · omega
  rw [e1, e2, e3, e4]
  clear e1 e2 e3 e4
  rw [stLoop_pairOrbStage_zero_off h f (p := t) (by omega),
    stLoop_pairOrbStage_one_eq h f (p := 2 * pairC r s - 1) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_two_on h f (p := 2 * pairC r s - 1) (by omega),
    stLoop_pairOrbStage_three_on h f (p := 2 * pairC r s - 1 - s) (by omega),
    stLoop_pairOrbStage_four_orbLow h f (p := 2 * pairC r s - 1 - s) (D := s - 1)
      (by omega) (by omega) (by omega) hDj]
  rw [ite_eq_right (show ¬ ((s - 1) % r = (pairOrbNext r s i + 1) % r) by
    unfold pairOrbNext
    rw [Nat.mod_add_mod, show s + i + 1 = s - 1 + 1 + r by omega, Nat.add_mod_right]
    exact fun h' ↦ add_mod_ne_self_orbLow (by omega) (by omega) h'.symm)]
  simp only [one_mul, mul_one, descProd_zero_orb]

/-- The strand loops of the low strands. -/
theorem stLoop_pairBlocks_low {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    {t : ℕ} (ht : t + 2 ≤ r ∨ t = 2 * pairC r s) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      pairOrbCore r s (loopAt (pairStrands r s) (pairBlocks r s) f) t := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hi : pairOrbLow r s t < r := by unfold pairOrbLow; split_ifs <;> omega
  have ht' : t = if pairOrbLow r s t + 1 = r then 2 * pairC r s else pairOrbLow r s t := by
    unfold pairOrbLow; split_ifs <;> omega
  unfold pairOrbCore
  rw [ite_eq_left ht]
  unfold pairOrbSlotLoop
  generalize pairOrbLow r s t = i at hi ht'
  have hj : pairOrbNext r s i < r := Nat.mod_lt _ (by omega)
  rw [stLoop_pairBlocks_eleven, pairOrbSkip_split_orbLow r s _ _ (by omega)]
  have key : ∀ X : G, pairOrbPos r s 5 t = 2 * pairC r s - 2 - pairOrbNext r s i →
      X * stLoop (pairStrands r s) (pairOrbStage r s 5)
          (runTop (pairStrands r s) (pairOrbPre r s 5) f) (pairOrbPos r s 5 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 6)
          (runTop (pairStrands r s) (pairOrbPre r s 6) f) (pairOrbPos r s 6 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 7)
          (runTop (pairStrands r s) (pairOrbPre r s 7) f) (pairOrbPos r s 7 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 8)
          (runTop (pairStrands r s) (pairOrbPre r s 8) f) (pairOrbPos r s 8 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 9)
          (runTop (pairStrands r s) (pairOrbPre r s 9) f) (pairOrbPos r s 9 t) *
        stLoop (pairStrands r s) (pairOrbStage r s 10)
          (runTop (pairStrands r s) (pairOrbPre r s 10) f) (pairOrbPos r s 10 t) =
        X * ((if 0 % r = (pairOrbNext r s i + 1) % r then 1 else
          loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s 0)) *
          pairOrbSuf r s (loopAt (pairStrands r s) (pairBlocks r s) f) (pairOrbNext r s i)) := by
    intro X h5
    rcases (show pairOrbNext r s i + 3 ≤ r ∨ pairOrbNext r s i + 2 = r ∨
        pairOrbNext r s i + 1 = r by omega) with hj' | hj' | hj'
    · exact stLoop_low_tail_climb h f hj' h5 X
    · exact stLoop_low_tail_mid h f hj' h5 X
    · exact stLoop_low_tail_top h f hj' h5 X
  rcases (show i + 3 ≤ r ∨ i + 2 = r ∨ i + 1 = r by omega) with hi' | hi' | hi'
  · rw [ite_eq_right (show ¬ (i + 1 = r) by omega)] at ht' ⊢
    obtain ⟨h5, hh⟩ := stLoop_low_head_climb h f hi' ht'
    rw [hh, key _ h5]
    simp only [mul_assoc]
  · rw [ite_eq_right (show ¬ (i + 1 = r) by omega)] at ht' ⊢
    obtain ⟨h5, hh⟩ := stLoop_low_head_mid h f hi' ht'
    rw [hh, key _ h5]
    simp only [mul_assoc]
  · rw [ite_eq_left hi'] at ht' ⊢
    obtain ⟨h5, hh⟩ := stLoop_low_head_top h f hi' ht'
    rw [hh, key _ h5]
    simp only [mul_assoc]

end AJConjecture
