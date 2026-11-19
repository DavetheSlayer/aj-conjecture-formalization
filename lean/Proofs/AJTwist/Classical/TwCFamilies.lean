import Mathlib
import AJTwist.TwDefs
import AJTwist.Classical.TwCSatelliteBound
import AJTwist.Classical.TwCClauses

/-!
# The classical clauses of the four families (Units C1 + C3)

Source: revision 5, Theorem 1.1 and Sections 7, 8.2: for `S = W_(ε,ℓ)(T_η)` the A-polynomial
`A_S` divides the containing polynomial and `gcd_R(G, A_S) = 1`, with `G = E` for the negative
clasp and `G = E^∨` for the positive clasp. With `a = twIndex η r s ℓ = η r s - ℓ`:

| clasp | companion | knot | bound | `G` |
|---|---|---|---|---|
| `-` | `T(r, s)` | `K`, `IsTwWhSatellite T K ℓ` | `twBound (-ℓ) a` | `E` |
| `+` | `T(r, s)` | `K`, `IsTwWhSatelliteP T K ℓ` | `(twBound ℓ (-a)).reverse` | `E^∨` |
| `-` | `T(r, -s)` | `K*`, `IsTwWhSatelliteP T K (-ℓ)` | `twBound (-ℓ) a` | `E` |
| `+` | `T(r, -s)` | `K*`, `IsTwWhSatellite T K (-ℓ)` | `(twBound ℓ (-a)).reverse` | `E^∨` |

(`T = torusPairKnot r s h`; `K*` is a mirror image of `K`; the last two rows are the mirror images
`W_(∓,ℓ)(T(r, -s)) = (W_(±,-ℓ)(T(r, s)))*` of eq. (mirror-marked).) For the negative clasp the
bound is `(L - 1) 𝒫_(-ℓ) 𝒫_a` of eq. (classicalcontainment); for the positive clasp it is the
bound `(L - 1) 𝒫_ℓ 𝒫_(-a)` of the mirror knot with `L` inverted.

The two mirror rows use one fact about the mirror image, stated here as a relation between two
knots so that it does not depend on how the mirror braid is written:
`IsEigenMirrorOf K' K`, every point `(M, L)` of the eigenvalue set of `K'` has `(M, L⁻¹)` in the
eigenvalue set of `K`. For `K' = K.inv` it follows from `eigenvalueSet_inv` of package TwK
(`AJTwist.Knot.TwKMirrorGroup`); see `AJTwist.Classical.TwCFourFamilies`.

The structure hypotheses are Unit C2 (`AJTwist.Classical.TwCPeripheral`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The eigenvalue set of `K'` is contained in the image of the eigenvalue set of `K` under
`(M, L) ↦ (M, L⁻¹)`: `K'` is a mirror image of `K` as far as the bound is concerned. -/
def IsEigenMirrorOf (K' K : BraidKnot) : Prop :=
  ∀ p ∈ eigenvalueSet K', (p.1, p.2⁻¹) ∈ eigenvalueSet K

/-- Negative clasp over `T(r, s)`. -/
theorem twClassClauses_negClasp_right {r s : ℕ} (h : IsTorusPair r s) {K : BraidKnot} {ℓ : ℤ}
    (hK : IsTwWhSatellite (torusPairKnot r s h) K ℓ) :
    TwClassClauses K extraFactor (twBound (-ℓ) (twIndex true r s ℓ)) := by
  rw [twIndex, ite_eq_left rfl]
  exact twClassClauses_neg fun p hp ↦
    evalPoint_twBound_of_twWhSatellite (companionDichotomyZ_torusPairKnot h) hK hp

/-- Positive clasp over `T(r, s)`. -/
theorem twClassClauses_posClasp_right {r s : ℕ} (h : IsTorusPair r s) {K : BraidKnot} {ℓ : ℤ}
    (hK : IsTwWhSatelliteP (torusPairKnot r s h) K ℓ) :
    TwClassClauses K extraFactorMirror (twBound ℓ (-(twIndex true r s ℓ))).reverse := by
  rw [twIndex, ite_eq_left rfl, neg_sub]
  exact twClassClauses_pos fun p hp ↦
    evalPoint_twBound_of_twWhSatelliteP (companionDichotomyZ_torusPairKnot h) hK hp

/-- Negative clasp over the mirror companion `T(r, -s)`: a mirror image `K'` of the positive
clasp `K` over `T(r, s)` with twist `-ℓ`. -/
theorem twClassClauses_negClasp_left {r s : ℕ} (h : IsTorusPair r s) {K K' : BraidKnot} {ℓ : ℤ}
    (hK : IsTwWhSatelliteP (torusPairKnot r s h) K (-ℓ)) (hmir : IsEigenMirrorOf K' K) :
    TwClassClauses K' extraFactor (twBound (-ℓ) (twIndex false r s ℓ)) := by
  rw [twIndex, ite_eq_right Bool.false_ne_true, show -((r * s : ℕ) : ℤ) - ℓ = -ℓ - ((r * s : ℕ) : ℤ) by
    ring]
  refine twClassClauses_neg fun p hp ↦ ?_
  have h1 := evalPoint_twBound_of_twWhSatelliteP (companionDichotomyZ_torusPairKnot h) hK
    (hmir p hp)
  rwa [inv_inv] at h1

/-- Positive clasp over the mirror companion `T(r, -s)`: a mirror image `K'` of the negative
clasp `K` over `T(r, s)` with twist `-ℓ`. -/
theorem twClassClauses_posClasp_left {r s : ℕ} (h : IsTorusPair r s) {K K' : BraidKnot} {ℓ : ℤ}
    (hK : IsTwWhSatellite (torusPairKnot r s h) K (-ℓ)) (hmir : IsEigenMirrorOf K' K) :
    TwClassClauses K' extraFactorMirror (twBound ℓ (-(twIndex false r s ℓ))).reverse := by
  rw [twIndex, ite_eq_right Bool.false_ne_true,
    show -(-((r * s : ℕ) : ℤ) - ℓ) = ((r * s : ℕ) : ℤ) - -ℓ by ring]
  refine twClassClauses_pos fun p hp ↦ ?_
  have h1 := evalPoint_twBound_of_twWhSatellite (companionDichotomyZ_torusPairKnot h) hK
    (hmir p hp)
  rwa [neg_neg] at h1

end AJConjecture
