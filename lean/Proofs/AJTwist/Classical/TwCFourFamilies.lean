import Mathlib
import AJTwist.Knot.TwKKnot
import AJTwist.Knot.TwKMirrorGroup
import AJTwist.Classical.TwCFamilies
import AJTwist.Classical.TwCPeripheral

/-!
# The classical clauses of the four families (Units C1–C3, assembled)

The classical half of Theorem 1.1 of revision 5 for the marked satellites
`twFamilyKnot r s h σ η ℓ = W_(ε,ℓ)(T_η)` of package TwK (`σ = true`: negative clasp;
`η = true`: companion `T(r, s)`, `η = false`: its mirror `T(r, -s)`), in the shape of the
classical clauses of `PairTClauses` (`TwClassClauses`): an A-polynomial exists; every
A-polynomial divides the bound and is coprime to `G` in `ℚ(M)[L, L⁻¹]`. With
`a = twIndex η r s ℓ = η r s - ℓ`:

* `twClassClauses_twFamilyKnot_neg` (negative clasp, both companions): the bound is
  `(L - 1) 𝒫_(-ℓ) 𝒫_a = twBound (-ℓ) a` (eq. (classicalcontainment)) and `G = E`;
* `twClassClauses_twFamilyKnot_pos` (positive clasp, both companions): the bound is the reverse
  in `L` of `(L - 1) 𝒫_ℓ 𝒫_(-a)` (the bound of the mirror knot `W_(-,-ℓ)(T_(-η))` with `L`
  inverted, Section 8.2) and `G = E^∨`.

Over the mirror companion the knot is the closure of the inverse braid of the satellite over
`T(r, s)` with the opposite clasp and twist; its eigenvalue set is the image under
`(M, L) ↦ (M, L⁻¹)` (`eigenvalueSet_inv`, package TwK), which is all that is used
(`isEigenMirrorOf_inv`).

Both theorems are proved here from the nodes of the packages; this file has no `sorry` of its
own.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The closure of the inverse braid is a mirror image for the eigenvalue sets. -/
theorem isEigenMirrorOf_inv (K : BraidKnot) : IsEigenMirrorOf K.inv K := by
  intro p hp
  rw [eigenvalueSet_inv] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simpa using hq

/-- The classical clauses for the negative clasp, `W_(-,ℓ)(T_η)`, with `G = E`. -/
theorem twClassClauses_twFamilyKnot_neg {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ) :
    TwClassClauses (twFamilyKnot r s h true η ℓ) extraFactor
      (twBound (-ℓ) (twIndex η r s ℓ)) := by
  cases η
  · exact twClassClauses_negClasp_left h (isTwWhSatelliteP_twWhiteheadKnot h (-ℓ))
      (isEigenMirrorOf_inv _)
  · exact twClassClauses_negClasp_right h (isTwWhSatellite_twWhiteheadKnot h ℓ)

/-- The classical clauses for the positive clasp, `W_(+,ℓ)(T_η)`, with `G = E^∨`. -/
theorem twClassClauses_twFamilyKnot_pos {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ) :
    TwClassClauses (twFamilyKnot r s h false η ℓ) extraFactorMirror
      (twBound ℓ (-(twIndex η r s ℓ))).reverse := by
  cases η
  · exact twClassClauses_posClasp_left h (isTwWhSatellite_twWhiteheadKnot h (-ℓ))
      (isEigenMirrorOf_inv _)
  · exact twClassClauses_posClasp_right h (isTwWhSatelliteP_twWhiteheadKnot h ℓ)

end AJConjecture
