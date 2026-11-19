import Mathlib
import AJFamily.Skein.TorusPhaseTwoFinishDown
import AJFamily.Skein.TorusPhaseTwoFinishEnd
import AJFamily.Skein.TorusPhaseTwoFinishPass
import AJFamily.Skein.TorusPhaseTwoFinishTurns

/-!
# Stage E of phase II: the clasp loses its half-twist conjugation

`phaseTwo_stageE`: `phaseTwoWG k`, the target word with `claspWord` conjugated by a half twist,
reaches `torusTargetWord k`. Macro `E1` turns the conjugation into two opposite curls `c₁` and `c₂`.
The curl `c₂` then travels once around the band (down the return strand, around the first cup, up
pass 1, around the closing cap, down the closing arc, around the closing cup, up pass 2, through the
half twists and the hook) and cancels `c₁` (one `kink`).
-/

namespace AJConjecture

/-! ### Chains (proved from the steps) -/

theorem phaseTwo_E_downR (k : ℕ) : ∀ m, m ≤ 2 * k + 1 → MorseReach 1 (phaseTwoER k m) (phaseTwoER k 0)
  | 0, _ => morseReach_refl 1 _
  | m + 1, h => morseReach_trans (phaseTwo_E_downStepR k m (by omega)) (phaseTwo_E_downR k m (by omega))

theorem phaseTwo_E_downA (k : ℕ) : ∀ m, m ≤ 2 * k + 1 → MorseReach 1 (phaseTwoEA k m) (phaseTwoEA k 0)
  | 0, _ => morseReach_refl 1 _
  | m + 1, h => morseReach_trans (phaseTwo_E_downStepA k m (by omega)) (phaseTwo_E_downA k m (by omega))

theorem phaseTwo_E_pass (k : ℕ) (s : Bool) :
    ∀ m, m ≤ 2 * k + 1 → MorseReach 1 (phaseTwoEP k 0 s) (phaseTwoEP k m s)
  | 0, _ => morseReach_refl 1 _
  | m + 1, h => morseReach_trans (phaseTwo_E_pass k s m (by omega)) (phaseTwo_E_passStep k m s (by omega))

/-- Stage E: the clasp loses its half-twist conjugation. -/
theorem phaseTwo_stageE (k : ℕ) (hk : 1 ≤ k) : MorseReach 1 (phaseTwoWG k) (torusTargetWord k) :=
  morseReach_trans (phaseTwo_E1 k hk) <| morseReach_trans (phaseTwo_E_toR k hk) <|
    morseReach_trans (phaseTwo_E_downR k _ le_rfl) <| morseReach_trans (phaseTwo_E_turnBottom k hk) <|
      morseReach_trans (phaseTwo_E_pass k true _ le_rfl) <| morseReach_trans (phaseTwo_E_turnCap k hk) <|
        morseReach_trans (phaseTwo_E_downA k _ le_rfl) <| morseReach_trans (phaseTwo_E_turnCup k hk) <|
          morseReach_trans (phaseTwo_E_pass k false _ le_rfl) (phaseTwo_E_end k hk)

end AJConjecture
