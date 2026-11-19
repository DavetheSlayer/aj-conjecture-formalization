import Mathlib
import AJTwist.Knot.TwKKnot
import AJTwist.Knot.TwKBandClasp
import AJTwist.Quantum.TwQJonesTorus

/-!
# The coloured Jones functions of the four families (Unit M1, first half)

Source: revision 5, Theorem 1.1 and Section 8.2 (`conclusion.tex`, eq. (mirror-marked):
`(W_{-,ℓ}(T_η))^* = W_{+,-ℓ}(T_{-η})`; "in zero framing `Φ_{S^*}(N; t) = Φ_S(N; t⁻¹)` on all
signed colours").

For the marked satellites `twFamilyKnot r s h σ η ℓ = W_{ε,ℓ}(T_η)` of the knot package
(`σ = true`: negative clasp; `η = true`: companion `T(r, s)`):

* `twm_coloredJones_mirror`: the coloured Jones function of `W_{-ε,-ℓ}(T_{-η})` is the bar
  (`laurentBar`, `t ↦ t⁻¹`) of that of `W_{ε,ℓ}(T_η)`: one of the two knots is the closure of the
  inverse braid of the other (`coloredJones_inv`);
* `twm_coloredJones_negClasp`: for the negative clasp and both companions the coloured Jones
  function is the formula `twFormula η r s ℓ` of the quantum package
  (`twQ_coloredJones_negClasp` for `η = true`; `twQ_coloredJones_mirror_of_posClasp` for
  `η = false`), with the band-and-clasp identity and the writhe of the knot package
  (`isBandClasp_twWhiteheadKnot`, `writhe_twWhiteheadKnot`);
* `twm_coloredJones_posClasp`: for the positive clasp it is the bar of the formula of the mirror
  knot, `twQBar (twFormula (!η) r s (-ℓ))`.

This file has no `sorry` of its own.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The coloured Jones function of `W_{-,ℓ}(T(r, s))` (`twQ_coloredJones_negClasp` with the
band-and-clasp identity and the writhe of the knot package). -/
theorem twm_coloredJones_whitehead_neg {r s : ℕ} (h : IsTorusPair r s) (ℓ n : ℤ) :
    laurentToField (coloredJones (twWhiteheadKnot r s h ℓ true) n) = twFormula true r s ℓ n := by
  refine twQ_coloredJones_negClasp h ℓ _ (isBandClasp_twWhiteheadKnot h ℓ true) ?_ n
  rw [writhe_twWhiteheadKnot, ite_eq_left rfl]
  ring

/-- The coloured Jones function of `W_{+,ℓ}(T(r, s))`: the bar of the formula of
`W_{-,-ℓ}(T(r, -s))` (`twQ_coloredJones_posClasp`). -/
theorem twm_coloredJones_whitehead_pos {r s : ℕ} (h : IsTorusPair r s) (ℓ n : ℤ) :
    laurentToField (coloredJones (twWhiteheadKnot r s h ℓ false) n) =
      twQBar (twFormula false r s (-ℓ) n) := by
  refine twQ_coloredJones_posClasp h (-ℓ) _ ?_ ?_ n
  · have e : -(2 * -ℓ) - 2 * (((r - 1) * s : ℕ) : ℤ) = 2 * ℓ - 2 * (((r - 1) * s : ℕ) : ℤ) := by
      ring
    rw [e]
    exact isBandClasp_twWhiteheadKnot h ℓ false
  · rw [writhe_twWhiteheadKnot, ite_eq_right Bool.false_ne_true]
    ring

/-- **The mirror identity on the coloured Jones function** (eq. (mirror-marked) and
`Φ_{S^*}(N; t) = Φ_S(N; t⁻¹)`): the coloured Jones function of `W_{-ε,-ℓ}(T_{-η})` is the bar of
that of `W_{ε,ℓ}(T_η)`, at every integer colour. -/
theorem twm_coloredJones_mirror {r s : ℕ} (h : IsTorusPair r s) (σ η : Bool) (ℓ n : ℤ) :
    coloredJones (twFamilyKnot r s h (!σ) (!η) (-ℓ)) n =
      laurentBar (coloredJones (twFamilyKnot r s h σ η ℓ) n) := by
  cases η
  · rw [Bool.not_false, twFamilyKnot_true, twFamilyKnot_false, coloredJones_inv,
      laurentBar_laurentBar]
  · rw [Bool.not_true, twFamilyKnot_true, twFamilyKnot_false, neg_neg, Bool.not_not,
      coloredJones_inv]

/-- The mirror identity in `ℚ(t)`. -/
theorem twm_laurentToField_coloredJones_mirror {r s : ℕ} (h : IsTorusPair r s) (σ η : Bool)
    (ℓ n : ℤ) :
    laurentToField (coloredJones (twFamilyKnot r s h (!σ) (!η) (-ℓ)) n) =
      twQBar (laurentToField (coloredJones (twFamilyKnot r s h σ η ℓ) n)) := by
  rw [twm_coloredJones_mirror, twQBar_laurentToField]
  rfl

/-- **The coloured Jones function of the negative-clasp satellites** `W_{-,ℓ}(T_η)`, both
companions and every twist: the formula `twFormula η r s ℓ` with index `a = twIndex η r s ℓ`. -/
theorem twm_coloredJones_negClasp {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ n : ℤ) :
    laurentToField (coloredJones (twFamilyKnot r s h true η ℓ) n) = twFormula η r s ℓ n := by
  cases η
  · have hm := twm_laurentToField_coloredJones_mirror h false true (-ℓ) n
    rw [Bool.not_false, Bool.not_true, neg_neg, twFamilyKnot_true] at hm
    rw [hm, twm_coloredJones_whitehead_pos, neg_neg, twQBar_twQBar]
  · rw [twFamilyKnot_true]
    exact twm_coloredJones_whitehead_neg h ℓ n

/-- **The coloured Jones function of the positive-clasp satellites** `W_{+,ℓ}(T_η)`: the bar of
the formula of the mirror knot `W_{-,-ℓ}(T_{-η})`. -/
theorem twm_coloredJones_posClasp {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ n : ℤ) :
    laurentToField (coloredJones (twFamilyKnot r s h false η ℓ) n) =
      twQBar (twFormula (!η) r s (-ℓ) n) := by
  have hm := twm_laurentToField_coloredJones_mirror h true (!η) (-ℓ) n
  rw [Bool.not_true, Bool.not_not, neg_neg] at hm
  rw [hm, twm_coloredJones_negClasp]

end AJConjecture
