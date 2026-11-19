import Mathlib
import AJTwist.Knot.TwKHalfLinePos
import AJTwist.Knot.TwKCayley

/-!
# The band-and-clasp identity for the twisted Whitehead doubles of `T(r, s)`

`isBandClasp_twWhiteheadKnot`: for every twist `ℓ ∈ ℤ` and both clasp signs,
`IsBandClasp (twWhiteheadKnot r s h ℓ σ) (torusPairKnot r s h) (2ℓ - 2(r-1)s) σ`, and the writhe
of the braid word is `2(r-1)s - 2ℓ ∓ 2` (`writhe_twWhiteheadKnot`). These are the two inputs of
the quantum package (the hypotheses `hK`, `hw` of the satellite formula).

Proof: `longKnotOp = twSrcOp (halfTwistZ c (2ℓ))` (`TwKSourceOp`), the half line `ℓ ≤ 0`
(`TwKHalfLine`, `TwKHalfLinePos`) and the Cayley–Hamilton extension (`TwKCayley`).
-/

noncomputable section

namespace AJConjecture

/-- The band-and-clasp identity, negative clasp, every twist. -/
theorem isBandClasp_twWhiteheadKnot_neg {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) :
    IsBandClasp (twWhiteheadKnot r s h ℓ true) (torusPairKnot r s h)
      (2 * ℓ - 2 * (((r - 1) * s : ℕ) : ℤ)) true := by
  intro c
  rw [longKnotOp_twWhiteheadKnot_eq_twSrcOp]
  exact twSrcOp_eq_of_halfLine h true c (fun n ↦ twSrcOp_halfLine h c n) ℓ

/-- The band-and-clasp identity, positive clasp, every twist. -/
theorem isBandClasp_twWhiteheadKnot_pos {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) :
    IsBandClasp (twWhiteheadKnot r s h ℓ false) (torusPairKnot r s h)
      (2 * ℓ - 2 * (((r - 1) * s : ℕ) : ℤ)) false := by
  intro c
  rw [longKnotOp_twWhiteheadKnot_eq_twSrcOp]
  exact twSrcOp_eq_of_halfLine h false c (fun n ↦ twSrcOp_halfLine_pos h c n) ℓ

/-- The band-and-clasp identity for the two families over the right-handed companion. -/
theorem isBandClasp_twWhiteheadKnot {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool) :
    IsBandClasp (twWhiteheadKnot r s h ℓ σ) (torusPairKnot r s h)
      (2 * ℓ - 2 * (((r - 1) * s : ℕ) : ℤ)) σ := by
  cases σ
  · exact isBandClasp_twWhiteheadKnot_pos h ℓ
  · exact isBandClasp_twWhiteheadKnot_neg h ℓ

/-- The writhe of the braid word of `W_{ε,ℓ}(T(r, s))`. -/
theorem writhe_twWhiteheadKnot {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool) :
    writhe (twWhiteheadKnot r s h ℓ σ).word =
      2 * (((r - 1) * s : ℕ) : ℤ) - 2 * ℓ + (if σ then -2 else 2) :=
  writhe_twWhiteheadWord h ℓ σ

end AJConjecture
