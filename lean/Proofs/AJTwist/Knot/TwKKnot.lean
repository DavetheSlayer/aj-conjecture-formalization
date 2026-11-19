import Mathlib
import AJTwist.Knot.TwKConnected
import AJTwist.Knot.TwKMirrorGroup

/-!
# The four families of twisted Whitehead doubles as closed braids

`twWhiteheadKnot r s h ℓ σ` is the closure of `twWhiteheadWord r s ℓ σ`: the satellite
`W_{ε,ℓ}(T(r, s))` of the paper over the right-handed torus knot, with `ℓ` full twists of the band
and the clasp of sign `σ` (`σ = true`: negative clasp, `σ = false`: positive clasp). For `ℓ = 0`,
`σ = true` it is `pairWhiteheadKnot r s h`. The two families over the left-handed companion are
mirror images (`conclusion.tex`, eq. (mirror-marked): `(W_{-,ℓ}(T_η))^* = W_{+,-ℓ}(T_{-η})`),
realized as the closures of the inverse braids (`BraidKnot.inv`: the mirror image with the
opposite orientation; the coloured Jones function and the eigenvalue set do not see the
orientation, and the knot group of the inverse braid is that of the braid with the inverse
longitude, `exists_knotGroup_inv_equiv`).

Conventions, checked on the unknot companion (`SCR/K/tools/chk_sign.py`): the band-and-clasp
diagram with `2ℓ` half twists and the clasp `σ = true` is the figure-eight knot for `ℓ = -1` and a
trefoil for `ℓ = 1`, as in the paper for the negative clasp.
-/

namespace AJConjecture

/-- `W_{ε,ℓ}(T(r, s))` as a closed braid (`σ = true`: negative clasp). -/
def twWhiteheadKnot (r s : ℕ) (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool) : BraidKnot where
  strands := twStrands r s ℓ
  word := twWhiteheadWord r s ℓ σ
  strands_pos := Nat.add_pos_left (Nat.succ_pos _) _
  isOnStrands := isOnStrands_twWhiteheadWord h ℓ σ
  connected := connected_twWhiteheadWord h ℓ σ

/-- Two closed braids with the same number of strands and the same word are equal. -/
private theorem braidKnot_ext_twKKnot {K K' : BraidKnot} (hs : K.strands = K'.strands)
    (hw : K.word = K'.word) : K = K' := by
  cases K
  cases K'
  dsimp only at hs hw
  subst hs hw
  rfl

/-- The untwisted negative-clasp double is the knot of Theorem T. -/
theorem twWhiteheadKnot_zero_true {r s : ℕ} (h : IsTorusPair r s) :
    twWhiteheadKnot r s h 0 true = pairWhiteheadKnot r s h :=
  braidKnot_ext_twKKnot (by simp [twWhiteheadKnot, pairWhiteheadKnot, twStrands, twExtra])
    (twWhiteheadWord_zero_true h)

/-- The marked satellite `W_{ε,ℓ}(T_η)`: clasp sign `σ` (`true`: negative), companion `T(r, s)`
for `η = true` and its mirror `T(r, -s)` for `η = false`, twist `ℓ`. Over the mirror companion
it is the mirror image (closure of the inverse braid) of the satellite over `T(r, s)` with the
opposite clasp and twist. -/
def twFamilyKnot (r s : ℕ) (h : IsTorusPair r s) (σ η : Bool) (ℓ : ℤ) : BraidKnot :=
  if η then twWhiteheadKnot r s h ℓ σ else (twWhiteheadKnot r s h (-ℓ) (!σ)).inv

theorem twFamilyKnot_true (r s : ℕ) (h : IsTorusPair r s) (σ : Bool) (ℓ : ℤ) :
    twFamilyKnot r s h σ true ℓ = twWhiteheadKnot r s h ℓ σ := rfl

theorem twFamilyKnot_false (r s : ℕ) (h : IsTorusPair r s) (σ : Bool) (ℓ : ℤ) :
    twFamilyKnot r s h σ false ℓ = (twWhiteheadKnot r s h (-ℓ) (!σ)).inv := rfl

/-- The mirror identity of the paper: `(W_{ε,ℓ}(T_η))^* = W_{-ε,-ℓ}(T_{-η})` for `η = +`. -/
theorem inv_twFamilyKnot_true (r s : ℕ) (h : IsTorusPair r s) (σ : Bool) (ℓ : ℤ) :
    (twFamilyKnot r s h σ true ℓ).inv = twFamilyKnot r s h (!σ) false (-ℓ) := by
  rw [twFamilyKnot_true, twFamilyKnot_false, neg_neg, Bool.not_not]

end AJConjecture
