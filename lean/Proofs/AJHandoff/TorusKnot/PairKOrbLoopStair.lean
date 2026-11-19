import Mathlib
import AJHandoff.TorusKnot.PairKOrbStage

/-!
# Strand loops of `pairBlocks r s`: the last window position and the staircase

For the positions `2c - s - 1 ≤ t ≤ T` the strand loop is `pairOrbCore`, with the second Hopf
loop in front at `T`:

* `t = pairOrbH1 = 2c - s - 1`: the first Hopf loop `H₁`;
* `t = 2c - s` (bottom of the staircase): `C R_(s-1) A`;
* `2c - s < t < T`: `C R_(T-t) B A`;
* `t = T`: `H₂ R_0 B A`.

Route: as for `AJHandoff.TorusKnot.PairKOrbLoopRun` (`stLoop_pairBlocks_stages`, the pattern
lemmas, `loopAt_pairOrbStage`); here the strand meets stage 4 on its upper part, so
`stLoop_orbStair` collects the single round `R_(T-t)`. Checked by computer (`pairOrbCheckLoop`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- Split the conditionals of the goal and close every branch by `omega`. -/
local macro "orb_ifs" : tactic => `(tactic| (split_ifs <;> omega))

set_option linter.unusedSimpArgs false in
/-- The strand loop of `pairOrbH1`: the first Hopf loop. -/
private theorem stLoop_pairBlocks_H1 {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t : ℕ} (ht : t + s + 1 = 2 * pairC r s) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH1 r s) := by
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
  have e3 : pairOrbPos r s 3 t = 2 * pairC r s - 1 := by
    rw [pairOrbPos_succ, e2, stPerm_pairOrbStage_two h]
    clear e1
    orb_ifs
  have e4 : pairOrbPos r s 4 t = 2 * pairC r s - 1 := by
    rw [pairOrbPos_succ, e3, stPerm_pairOrbStage_three h]
    clear e1 e2
    orb_ifs
  have e5 : pairOrbPos r s 5 t = 2 * pairC r s - 1 := by
    rw [pairOrbPos_succ, e4, stPerm_pairOrbStage_four h]
    clear e1 e2 e3
    orb_ifs
  have e6 : pairOrbPos r s 6 t = 2 * pairC r s := by
    rw [pairOrbPos_succ, e5, stPerm_pairOrbStage_five h]
    clear e1 e2 e3 e4
    orb_ifs
  have e7 : pairOrbPos r s 7 t = 2 * pairC r s := by
    rw [pairOrbPos_succ, e6, stPerm_pairOrbStage_six h]
    clear e1 e2 e3 e4 e5
    orb_ifs
  have e8 : pairOrbPos r s 8 t = 2 * pairC r s := by
    rw [pairOrbPos_succ, e7, stPerm_pairOrbStage_seven h]
    clear e1 e2 e3 e4 e5 e6
    orb_ifs
  have e9 : pairOrbPos r s 9 t = 2 * pairC r s := by
    rw [pairOrbPos_succ, e8, stPerm_pairOrbStage_eight h]
    clear e1 e2 e3 e4 e5 e6 e7
    orb_ifs
  have e10 : pairOrbPos r s 10 t = 2 * pairC r s := by
    rw [pairOrbPos_succ, e9, stPerm_pairOrbStage_nine h]
    clear e1 e2 e3 e4 e5 e6 e7 e8
    orb_ifs
  rw [stLoop_pairBlocks_eleven, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  rw [stLoop_pairOrbStage_zero_off h f (p := t) (by omega),
    stLoop_pairOrbStage_one_eq h f (p := t) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_two_off h f (p := t) (by omega),
    stLoop_pairOrbStage_three_off h f (p := 2 * pairC r s - 1) (by omega),
    stLoop_pairOrbStage_four_eq h f (p := 2 * pairC r s - 1) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by orb_ifs),
    stLoop_pairOrbStage_five_on h f (p := 2 * pairC r s - 1) (by omega),
    stLoop_pairOrbStage_six_off h f (p := 2 * pairC r s) (by omega),
    stLoop_pairOrbStage_seven_off h f (p := 2 * pairC r s) (by omega),
    stLoop_pairOrbStage_eight_eq h f (p := 2 * pairC r s) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_nine_eq h f (p := 2 * pairC r s) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_ten_eq h f (p := 2 * pairC r s) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega)]
  simp only [one_mul, mul_one, descProd_zero_orb, descProd_one_orb]

set_option linter.unusedSimpArgs false in
/-- The strand loop of the bottom `2c - s` of the staircase. -/
private theorem stLoop_pairBlocks_stairBot {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t : ℕ} (ht : t + s = 2 * pairC r s) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxC r s) *
        loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (s - 1)) *
        descProd (loopAt (pairStrands r s) (pairBlocks r s) f) 0 (r - 2) := by
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
  have e4 : pairOrbPos r s 4 t = r - 2 := by
    rw [pairOrbPos_succ, e3, stPerm_pairOrbStage_three h]
    clear e1 e2
    orb_ifs
  have e5 : pairOrbPos r s 5 t = r - 2 := by
    rw [pairOrbPos_succ, e4, stPerm_pairOrbStage_four h]
    clear e1 e2 e3
    orb_ifs
  have e6 : pairOrbPos r s 6 t = r - 2 := by
    rw [pairOrbPos_succ, e5, stPerm_pairOrbStage_five h]
    clear e1 e2 e3 e4
    orb_ifs
  have e7 : pairOrbPos r s 7 t = r - 2 := by
    rw [pairOrbPos_succ, e6, stPerm_pairOrbStage_six h]
    clear e1 e2 e3 e4 e5
    orb_ifs
  have e8 : pairOrbPos r s 8 t = r - 2 := by
    rw [pairOrbPos_succ, e7, stPerm_pairOrbStage_seven h]
    clear e1 e2 e3 e4 e5 e6
    orb_ifs
  have e9 : pairOrbPos r s 9 t = r - 2 := by
    rw [pairOrbPos_succ, e8, stPerm_pairOrbStage_eight h]
    clear e1 e2 e3 e4 e5 e6 e7
    orb_ifs
  have e10 : pairOrbPos r s 10 t = pairC r s - s + 1 := by
    rw [pairOrbPos_succ, e9, stPerm_pairOrbStage_nine h]
    clear e1 e2 e3 e4 e5 e6 e7 e8
    orb_ifs
  rw [stLoop_pairBlocks_eleven, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  rw [stLoop_pairOrbStage_zero_off h f (p := t) (by omega),
    stLoop_pairOrbStage_one_eq h f (p := t) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_two_on h f (p := t) (by omega),
    stLoop_pairOrbStage_three_on h f (p := t) (by omega),
    stLoop_pairOrbStage_four_eq h f (p := r - 2) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by orb_ifs),
    stLoop_pairOrbStage_five_off h f (p := r - 2) (by omega),
    stLoop_pairOrbStage_six_off h f (p := r - 2) (by omega),
    stLoop_pairOrbStage_seven_off h f (p := r - 2) (by omega),
    stLoop_pairOrbStage_eight_eq h f (p := r - 2) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_nine_eq h f (p := r - 2) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_ten_eq h f (p := pairC r s - s + 1) (lo := 0)
      (len := r - 2) (by omega) (fun j hj ↦ by omega)]
  simp only [one_mul, mul_one, descProd_zero_orb, descProd_one_orb]

set_option linter.unusedSimpArgs false in
/-- The strand loop of a position `2c - s < t < T` of the staircase. -/
private theorem stLoop_pairBlocks_stairMid {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t : ℕ} (h1 : 2 * pairC r s < t + s)
    (h2 : t + 1 < 2 * pairC r s) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxC r s) *
        loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (pairTop r s - t)) *
        loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxB r s) *
        descProd (loopAt (pairStrands r s) (pairBlocks r s) f) 0 (r - 2) := by
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
  have e4 : pairOrbPos r s 4 t = t := by
    rw [pairOrbPos_succ, e3, stPerm_pairOrbStage_three h]
    clear e1 e2
    orb_ifs
  have e5 : pairOrbPos r s 5 t = t - r := by
    rw [pairOrbPos_succ, e4, stPerm_pairOrbStage_four h]
    clear e1 e2 e3
    orb_ifs
  have e6 : pairOrbPos r s 6 t = t - r := by
    rw [pairOrbPos_succ, e5, stPerm_pairOrbStage_five h]
    clear e1 e2 e3 e4
    orb_ifs
  have e7 : pairOrbPos r s 7 t = t - r := by
    rw [pairOrbPos_succ, e6, stPerm_pairOrbStage_six h]
    clear e1 e2 e3 e4 e5
    orb_ifs
  have e8 : pairOrbPos r s 8 t = t - r := by
    rw [pairOrbPos_succ, e7, stPerm_pairOrbStage_seven h]
    clear e1 e2 e3 e4 e5 e6
    orb_ifs
  have e9 : pairOrbPos r s 9 t = t - r := by
    rw [pairOrbPos_succ, e8, stPerm_pairOrbStage_eight h]
    clear e1 e2 e3 e4 e5 e6 e7
    orb_ifs
  have e10 : pairOrbPos r s 10 t = t - r := by
    rw [pairOrbPos_succ, e9, stPerm_pairOrbStage_nine h]
    clear e1 e2 e3 e4 e5 e6 e7 e8
    orb_ifs
  rw [stLoop_pairBlocks_eleven, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  rw [stLoop_pairOrbStage_zero_off h f (p := t) (by omega),
    stLoop_pairOrbStage_one_eq h f (p := t) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_two_on h f (p := t) (by omega),
    stLoop_pairOrbStage_three_off h f (p := t) (by omega),
    stLoop_pairOrbStage_four_eq h f (p := t) (lo := 2 * pairC r s - 2 - t)
      (len := 1) (by omega) (fun j hj ↦ by orb_ifs),
    stLoop_pairOrbStage_five_off h f (p := t - r) (by omega),
    stLoop_pairOrbStage_six_off h f (p := t - r) (by omega),
    stLoop_pairOrbStage_seven_on h f (p := t - r) (by omega),
    stLoop_pairOrbStage_eight_eq h f (p := t - r) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_nine_eq h f (p := t - r) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_ten_eq h f (p := t - r) (lo := 0)
      (len := r - 2) (by omega) (fun j hj ↦ by omega)]
  simp only [one_mul, mul_one, descProd_zero_orb, descProd_one_orb]
  rw [show 2 * pairC r s - 2 - t + 1 = pairTop r s - t by omega]

set_option linter.unusedSimpArgs false in
/-- The strand loop of the top position `T`. -/
private theorem stLoop_pairBlocks_stairTop {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t : ℕ} (ht : t = pairTop r s) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH2 r s) *
        (loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s 0) *
          loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxB r s) *
          descProd (loopAt (pairStrands r s) (pairBlocks r s) f) 0 (r - 2)) := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  have e1 : pairOrbPos r s 1 t = 2 * pairC r s := by
    rw [pairOrbPos_succ, pairOrbPos_zero, stPerm_pairOrbStage_zero h]
    orb_ifs
  have e2 : pairOrbPos r s 2 t = 2 * pairC r s := by
    rw [pairOrbPos_succ, e1, stPerm_pairOrbStage_one h]
    orb_ifs
  have e3 : pairOrbPos r s 3 t = 2 * pairC r s := by
    rw [pairOrbPos_succ, e2, stPerm_pairOrbStage_two h]
    clear e1
    orb_ifs
  have e4 : pairOrbPos r s 4 t = 2 * pairC r s := by
    rw [pairOrbPos_succ, e3, stPerm_pairOrbStage_three h]
    clear e1 e2
    orb_ifs
  have e5 : pairOrbPos r s 5 t = 2 * pairC r s := by
    rw [pairOrbPos_succ, e4, stPerm_pairOrbStage_four h]
    clear e1 e2 e3
    orb_ifs
  have e6 : pairOrbPos r s 6 t = 2 * pairC r s - 1 := by
    rw [pairOrbPos_succ, e5, stPerm_pairOrbStage_five h]
    clear e1 e2 e3 e4
    orb_ifs
  have e7 : pairOrbPos r s 7 t = 2 * pairC r s - 1 - r := by
    rw [pairOrbPos_succ, e6, stPerm_pairOrbStage_six h]
    clear e1 e2 e3 e4 e5
    orb_ifs
  have e8 : pairOrbPos r s 8 t = 2 * pairC r s - 1 - r := by
    rw [pairOrbPos_succ, e7, stPerm_pairOrbStage_seven h]
    clear e1 e2 e3 e4 e5 e6
    orb_ifs
  have e9 : pairOrbPos r s 9 t = 2 * pairC r s - 1 - r := by
    rw [pairOrbPos_succ, e8, stPerm_pairOrbStage_eight h]
    clear e1 e2 e3 e4 e5 e6 e7
    orb_ifs
  have e10 : pairOrbPos r s 10 t = 2 * pairC r s - 1 - r := by
    rw [pairOrbPos_succ, e9, stPerm_pairOrbStage_nine h]
    clear e1 e2 e3 e4 e5 e6 e7 e8
    orb_ifs
  rw [stLoop_pairBlocks_eleven, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  rw [stLoop_pairOrbStage_zero_on h f (p := t) (by omega),
    stLoop_pairOrbStage_one_eq h f (p := 2 * pairC r s) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_two_off h f (p := 2 * pairC r s) (by omega),
    stLoop_pairOrbStage_three_off h f (p := 2 * pairC r s) (by omega),
    stLoop_pairOrbStage_four_eq h f (p := 2 * pairC r s) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by orb_ifs),
    stLoop_pairOrbStage_five_off h f (p := 2 * pairC r s) (by omega),
    stLoop_pairOrbStage_six_on h f (p := 2 * pairC r s - 1) (by omega),
    stLoop_pairOrbStage_seven_on h f (p := 2 * pairC r s - 1 - r) (by omega),
    stLoop_pairOrbStage_eight_eq h f (p := 2 * pairC r s - 1 - r) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_nine_eq h f (p := 2 * pairC r s - 1 - r) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_ten_eq h f (p := 2 * pairC r s - 1 - r) (lo := 0)
      (len := r - 2) (by omega) (fun j hj ↦ by omega)]
  simp only [one_mul, mul_one, descProd_zero_orb, descProd_one_orb]
  simp only [mul_assoc]

/-- The strand loops of `pairOrbH1` and of the staircase. -/
theorem stLoop_pairBlocks_stair {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    {t : ℕ} (h1 : 2 * pairC r s ≤ t + s + 1) (h2 : t ≤ pairTop r s) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      (if t = pairTop r s then loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH2 r s)
        else 1) * pairOrbCore r s (loopAt (pairStrands r s) (pairBlocks r s) f) t := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  unfold pairOrbCore
  rw [ite_eq_right (show ¬ (t + 2 ≤ r ∨ t = 2 * pairC r s) by omega),
    ite_eq_right (show ¬ (t + s ≤ pairC r s) by omega),
    ite_eq_right (show ¬ (t + s + r ≤ 2 * pairC r s) by omega),
    ite_eq_right (show ¬ (t + s + 2 ≤ 2 * pairC r s) by omega)]
  by_cases hH : t + s + 1 = 2 * pairC r s
  · rw [ite_eq_left hH, ite_eq_right (show ¬ (t = pairTop r s) by omega), one_mul,
      stLoop_pairBlocks_H1 h f hH]
  rw [ite_eq_right hH]
  by_cases hB : t + s = 2 * pairC r s
  · rw [ite_eq_left hB, ite_eq_right (show ¬ (t = pairTop r s) by omega), one_mul,
      stLoop_pairBlocks_stairBot h f hB]
  rw [ite_eq_right hB]
  by_cases hM : t + 1 < 2 * pairC r s
  · rw [ite_eq_left hM, ite_eq_right (show ¬ (t = pairTop r s) by omega), one_mul,
      stLoop_pairBlocks_stairMid h f (by omega) hM]
  rw [ite_eq_right hM, ite_eq_left (show t = pairTop r s by omega),
    stLoop_pairBlocks_stairTop h f (by omega)]

end AJConjecture
