import Mathlib
import AJTwist.Select.TwSRangeVal
import AJTwist.Select.TwSRangeGaussPos
import AJTwist.Select.TwSRangeGaussNeg

/-!
# Selection by the actual sequence: all five ranges

Source: Section 6 and Table 1 of the revision-5 manuscript. For both companion chiralities and
every twist `ℓ`, a growth class contains the Gaussian periods `G_c^{(ℓ)}` and not the reduced
satellite sequence `F` (in the saturated sense): `F ∉ 𝒰_ℓ`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **Selection (Section 6).** For every chirality `η`, every `r, s ≥ 2` and every twist `ℓ`, the
selection statement holds for the twisted input `twsInput η r s ℓ`. -/
theorem tws_selects (η : Bool) (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (ℓ : ℤ) :
    TwsSelects ℓ (twsInput η r s ℓ) := by
  cases η
  · rcases lt_or_ge (twIndex false r s ℓ) 0 with h | h
    · exact tws_selects_neg_lt_zero r s hr hs ℓ h
    · exact tws_selects_neg_ge_zero r s hr hs ℓ h
  · rcases lt_trichotomy (twIndex true r s ℓ) 0 with h | h | h
    · exact tws_selects_pos_lt_zero r s hr hs ℓ h
    · exact tws_selects_pos_zero r s hr hs ℓ h
    · exact tws_selects_pos_ge_one r s hr hs ℓ (by omega)

end AJConjecture
