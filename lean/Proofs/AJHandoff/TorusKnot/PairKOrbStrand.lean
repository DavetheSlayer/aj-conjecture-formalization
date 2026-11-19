import Mathlib
import AJHandoff.TorusKnot.PairKOrbLoopRun
import AJHandoff.TorusKnot.PairKOrbLoopStair
import AJHandoff.TorusKnot.PairKOrbLoopLow
import AJHandoff.TorusKnot.PairKOrbPureTop
import AJHandoff.TorusKnot.PairKOrbPureLow
import AJHandoff.TorusKnot.PairKOrbLabel
import AJHandoff.TorusKnot.PairKOrbCycle

/-!
# The pure step data along the orbit

`stLoop_pairBlocks_core`: every strand loop of `pairBlocks r s` is `pairOrbCore` (with the second
Hopf loop in front at `T`); `pairOrb_step`: off `pairOrbH1`, the core loop of the `k`-th strand of
the orbit is the pure step `K ^ w * y_(ℓ(next)) ^ n` in the frame of `y_0`, and the labels of the
two strands satisfy the label condition.

Route: `stLoop_pairBlocks_core` by cases (`t + 2 ≤ r ∨ t = 2c`: `stLoop_pairBlocks_low`;
`r ≤ t + 1 ∧ t + s + 2 ≤ 2c`: `stLoop_pairBlocks_run`, where `t ≠ T`; otherwise
`stLoop_pairBlocks_stair`). `pairOrb_step` from `pairOrb_pure_low` / `pairOrb_pure_top`,
`pairOrbY_lab_step`, `pairOrbT_succ`, `stPerm_pairBlocks_orb` and `pairOrbT_lt`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- Every strand loop is the core loop, with `H₂` in front at `T`. -/
theorem stLoop_pairBlocks_core {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    {t : ℕ} (ht : t < pairStrands r s) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      (if t = pairTop r s then loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxH2 r s)
        else 1) * pairOrbCore r s (loopAt (pairStrands r s) (pairBlocks r s) f) t := by
  obtain ⟨hr, hrs, hsc, -⟩ := pairOrb_arith h
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hm : pairStrands r s = 2 * pairC r s + 1 := rfl
  by_cases hlow : t + 2 ≤ r ∨ t = 2 * pairC r s
  · have hne : t ≠ pairTop r s := by omega
    rw [stLoop_pairBlocks_low h f hlow, ite_eq_right_iff.mpr (fun h' ↦ absurd h' hne), one_mul]
  · by_cases hrun : t + s + 2 ≤ 2 * pairC r s
    · have hne : t ≠ pairTop r s := by omega
      rw [stLoop_pairBlocks_run h f (by omega) hrun,
        ite_eq_right_iff.mpr (fun h' ↦ absurd h' hne), one_mul]
    · exact stLoop_pairBlocks_stair h f (by omega) (by omega)

/-- The pure step of the `k`-th strand of the orbit. -/
theorem pairOrb_step {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G} (hL : PairGapRels r s L)
    (k : ℕ) (hk : pairOrbT r s k ≠ pairOrbH1 r s) :
    pairOrbConj r s L (pairOrbCore r s L (pairOrbT r s k)) =
        pairOrbK r s L ^ pairOrbW r s (pairOrbT r s k) *
          pairOrbY r s L (pairOrbLab r s (pairOrbT r s (k + 1))) ^ pairOrbN r s (pairOrbT r s k) ∧
      pairOrbY r s L (pairOrbLab r s (pairOrbT r s k)) =
        pairOrbK r s L ^ pairOrbW r s (pairOrbT r s k) *
          pairOrbY r s L (pairOrbLab r s (pairOrbT r s (k + 1))) *
          pairOrbK r s L ^ (-pairOrbW r s (pairOrbT r s k)) := by
  obtain ⟨hr, hrs, hsc, -⟩ := pairOrb_arith h
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hlt := pairOrbT_lt h k
  have hm : pairStrands r s = 2 * pairC r s + 1 := rfl
  rw [pairOrbT_succ, stPerm_pairBlocks_orb h hlt]
  refine ⟨?_, pairOrbY_lab_step h hL hlt hk⟩
  by_cases hlow : pairOrbT r s k + 2 ≤ r ∨ pairOrbT r s k = 2 * pairC r s
  · exact pairOrb_pure_low h hL hlow
  · exact pairOrb_pure_top h hL (by omega) (by omega) hk

end AJConjecture
