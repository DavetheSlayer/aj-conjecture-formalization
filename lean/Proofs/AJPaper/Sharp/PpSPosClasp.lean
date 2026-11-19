import Mathlib
import AJTwist.Main.TwMJones
import AJPaper.Sharp.PpSNegClasp
import AJPaper.Sharp.PpSMirror
import AJPaper.Sharp.PpSSymbolMirror

/-!
# The whole symbol divides `f_S`: positive clasp, index `a ≠ 0` (Unit PpS, node `PpS_PosClasp`)

Source: Section 8.4 of the paper (`conclusion.tex`): "the mirror identity (mirror-marked) and
meridian inversion give the divisibility for the positive clasp"; Section 8.2:
`(W_(-,ℓ)(T_η))^* = W_(+,-ℓ)(T_(-η))` and `f_{S^*}(M, L) ≐ f_S(M⁻¹, L)`.

The positive-clasp satellite `W_(+,ℓ)(T_η)` is the mirror image of the negative-clasp satellite
`W_(-,-ℓ)(T_(-η))`, whose effective index is `-a`, `a = twIndex η r s ℓ = η r s - ℓ`
(`twIndex_not_neg`). For `a ≠ 0` the symbol `(L - 1) E 𝒫_(-a)` divides the specialization of
every nonzero primitive element of the localized annihilator of the mirror knot
(`pps_symbol_dvd_negClasp`); the mirror transport (`pps_mirror_dvd`) turns it into its meridian
inversion, which is `(L - 1) E^∨ 𝒫_(-a)^rev = ppsSymbolMirror (-a)` up to a unit
(`pps_symbol_mInv_associated`). This is the quantum factor matching the library's classical
bound `(twBound ℓ (-a)).reverse = ((L - 1) 𝒫_ℓ 𝒫_(-a))^rev` of the positive clasp.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The effective index of the mirror knot `W_(-,-ℓ)(T_(-η))` is the opposite of the index of
`W_(-,ℓ)(T_η)`. -/
theorem twIndex_not_neg (η : Bool) (r s : ℕ) (ℓ : ℤ) :
    twIndex (!η) r s (-ℓ) = -(twIndex η r s ℓ) := by
  cases η <;> simp [twIndex] <;> ring

/-- **The whole symbol survives for the positive clasp, `a ≠ 0`** (Section 8.4): for the
satellite `W_(+,ℓ)(T_η)` with `a = η r s - ℓ ≠ 0`, the polynomial `(L - 1) E^∨ 𝒫_(-a)^rev`
(up to a unit, the symbol `(L - 1) E 𝒫_(-a)` of the mirror knot with the meridian inverted)
divides the specialization of every nonzero primitive element of the localized annihilator of
its coloured Jones function, in `ℚ(M)[L, L⁻¹]`. -/
theorem pps_symbol_dvd_posClasp {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ)
    (ha : twIndex η r s ℓ ≠ 0) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive →
      InLocalizedAnnihilator (coloredJones (twFamilyKnot r s h false η ℓ)) Q →
        toComparison (ppsSymbolMirror (-(twIndex η r s ℓ))) ∣ toComparison (specialize Q) := by
  have hbar : ∀ n : ℤ, laurentToField (coloredJones (twFamilyKnot r s h false η ℓ) n) =
      twQBar (laurentToField (coloredJones (twFamilyKnot r s h true (!η) (-ℓ)) n)) := by
    intro n
    have hm := twm_laurentToField_coloredJones_mirror h true (!η) (-ℓ) n
    rwa [Bool.not_true, Bool.not_not, neg_neg] at hm
  have ha' : twIndex (!η) r s (-ℓ) ≠ 0 := by
    rw [twIndex_not_neg]
    exact neg_ne_zero.mpr ha
  intro Q hQ0 hprim hQ
  have h1 := pps_mirror_dvd hbar (pps_symbol_dvd_negClasp h (!η) (-ℓ) ha') Q hQ0 hprim hQ
  rw [twIndex_not_neg] at h1
  exact (pps_symbol_mInv_associated _).symm.dvd.trans h1

end AJConjecture
