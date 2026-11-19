import Mathlib
import AJHandoff.TorusInput.RJFamilyStep

/-!
# A good family exists for every number of bundles (node RA2.3)

Route. Induction on `r ≥ 1` from `rj_goodFamily_one` and `rj_goodFamily_succ`. Estimate 15–30
lines.
-/

noncomputable section

namespace AJConjecture

/-- For every `r ≥ 1` there is a good fusion family of `f_b^{⊗ r}`. -/
theorem rj_goodFamily_exists (b r : ℕ) (hr : 1 ≤ r) : ∃ L, RJGoodFamily b r L := by
  induction r, hr using Nat.le_induction with
  | base => exact rj_goodFamily_one b
  | succ r hr ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨rjFamilySucc b r L, rj_goodFamily_succ b r hr L hL⟩

end AJConjecture
