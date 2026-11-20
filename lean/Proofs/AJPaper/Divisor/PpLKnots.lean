import Mathlib
import AJTwist.Main.TwMNegClasp
import AJTwist.Main.TwMJones
import AJPaper.Sharp.PpSTail
import AJPaper.Sharp.PpSSymbol
import AJPaper.Sharp.PpSMirror
import AJPaper.Sharp.PpSSymbolMirror
import AJPaper.Sharp.PpSPosClasp
import AJPaper.Divisor.PpLIrreducible

/-!
# The whole symbol divides `f_S` for every index, and `L - 1 ∣ f_S` (Unit PpL, node
`PpL_Knots`)

Source: Section 8.4 of the paper (`conclusion.tex`), after Corollary 8.3: "For a negative-clasp
satellite with `ℓ ≠ 0`, the same selection and specialization give `(L - 1) 𝒫_a ∣ f_S` when
`a ≠ 0`. At `a = 0` we only need the factor `L - 1`, since `𝒫_0 = 1`. Lê's general divisibility
[Lê 2006, Prop. 2.3] gives it for the primitive minimum in the signed unreduced convention …
This is a statement about `f_S`, even if the selected divisor specializes to the quadratic
alone."

Here the factor `L - 1` at `a = 0` is obtained without Lê's proposition: `P_0` is irreducible
(`ppl_irreducible`), so the selected divisor is all of `P_0`, and the argument of the package
`AJPaper/Sharp` for `a ≠ 0` runs for every integer `a`. The result is a single statement:

* `ppl_symbol_dvd_of_formula`, `ppl_symbol_dvd_negClasp`: for the negative-clasp satellite
  `W_(-,ℓ)(T_η)` and **every** twist `ℓ`, `(L - 1) E 𝒫_a = ppsSymbol a` divides the
  specialization of every nonzero primitive element of the localized annihilator, in
  `ℚ(M)[L, L⁻¹]` (`a = twIndex η r s ℓ`; `pps_symbol_dvd_negClasp` is the case `a ≠ 0`).
* `ppl_symbol_dvd_posClasp`: for the positive clasp, `(L - 1) E^∨ 𝒫_(-a)^rev =
  ppsSymbolMirror (-a)` does.
* `ppl_zero_dvd_negClasp`, `ppl_zero_dvd_posClasp`: at `a = 0` (`ℓ = η r s`) the factor is
  `(L - 1) E`, resp. `(L - 1) E^∨`.
* `ppl_sub_one_dvd`: **`L - 1 ∣ f_S`** for all four families and every twist (Lê's divisibility
  for these knots).

Dependencies on the package `AJPaper/Sharp` (statements only): `ppsSymbol`,
`pps_specialize_twTransferOp_associated` (`PpSSymbol`); `pps_specialize_dvd_of_tail`,
`pps_dvd_specialize_of_formula` (`PpSTail`); `pps_mirror_dvd` (`PpSMirror`); `ppsSymbolMirror`,
`pps_symbol_mInv_associated` (`PpSSymbolMirror`); `twIndex_not_neg` (`PpSPosClasp`).

This file is proved from `ppl_irreducible` and these statements; it has no `sorry` of its own.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **The whole symbol survives, every index.** For a knot whose coloured Jones function is
`twFormula η r s ℓ`, the polynomial `(L - 1) E 𝒫_a`, `a = η r s - ℓ`, divides the specialization
of every nonzero primitive element of the localized annihilator, in `ℚ(M)[L, L⁻¹]`. -/
theorem ppl_symbol_dvd_of_formula {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ)
    (K : BraidKnot)
    (hseq : ∀ n : ℤ, laurentToField (coloredJones K n) = twFormula η r s ℓ n) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
      toComparison (ppsSymbol (twIndex η r s ℓ)) ∣ toComparison (specialize Q) := by
  have hr : 2 ≤ r := h.1
  have hs : 2 ≤ s := hr.trans h.2.1.le
  refine pps_dvd_specialize_of_formula K (twsInput η r s ℓ) hseq fun Q hQ hann ↦ ?_
  have hsel := tws_selects η r s hr hs ℓ
  have h1 : toComparison (specialize (twTransferOp (twIndex η r s ℓ))) ∣
      toComparison (specialize Q) :=
    pps_specialize_dvd_of_tail (twsInput η r s ℓ) (specialize_twTransferOp_ne_zero _)
      (fun hQ' ↦ tws_tail_annihilator_of_selects hsel (twTransferOp_ne_zero _)
        (fun hβ _ _ hfac ↦ ppl_irreducible _ hβ hfac) (twQ_transfer_mem_periodSpan η r s ℓ)
        hQ') hQ hann
  exact (pps_specialize_twTransferOp_associated _).symm.dvd.trans h1

/-- **The whole symbol survives for the negative clasp, every twist** (Section 8.4): for the
satellite `W_(-,ℓ)(T_η)` the polynomial `(L - 1) E 𝒫_a`, `a = η r s - ℓ`, divides the
specialization of every nonzero primitive element of the localized annihilator of its coloured
Jones function, in `ℚ(M)[L, L⁻¹]`. -/
theorem ppl_symbol_dvd_negClasp {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive →
      InLocalizedAnnihilator (coloredJones (twFamilyKnot r s h true η ℓ)) Q →
        toComparison (ppsSymbol (twIndex η r s ℓ)) ∣ toComparison (specialize Q) :=
  ppl_symbol_dvd_of_formula h η ℓ _ (twm_coloredJones_negClasp h η ℓ)

/-- **The whole symbol survives for the positive clasp, every twist** (Section 8.4): for the
satellite `W_(+,ℓ)(T_η)` the polynomial `(L - 1) E^∨ 𝒫_(-a)^rev`, `a = η r s - ℓ` (up to a
unit, the symbol of the mirror knot with the meridian inverted), divides the specialization of
every nonzero primitive element of the localized annihilator of its coloured Jones function, in
`ℚ(M)[L, L⁻¹]`. -/
theorem ppl_symbol_dvd_posClasp {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive →
      InLocalizedAnnihilator (coloredJones (twFamilyKnot r s h false η ℓ)) Q →
        toComparison (ppsSymbolMirror (-(twIndex η r s ℓ))) ∣ toComparison (specialize Q) := by
  have hbar : ∀ n : ℤ, laurentToField (coloredJones (twFamilyKnot r s h false η ℓ) n) =
      twQBar (laurentToField (coloredJones (twFamilyKnot r s h true (!η) (-ℓ)) n)) := by
    intro n
    have hm := twm_laurentToField_coloredJones_mirror h true (!η) (-ℓ) n
    rwa [Bool.not_true, Bool.not_not, neg_neg] at hm
  intro Q hQ0 hprim hQ
  have h1 := pps_mirror_dvd hbar (ppl_symbol_dvd_negClasp h (!η) (-ℓ)) Q hQ0 hprim hQ
  rw [twIndex_not_neg] at h1
  exact (pps_symbol_mInv_associated _).symm.dvd.trans h1

/-- **Index `a = 0`, negative clasp** (Section 8.4): for `W_(-,ℓ)(T_η)` with `ℓ = η r s`, the
polynomial `(L - 1) E` divides the specialization of every nonzero primitive element of the
localized annihilator, in `ℚ(M)[L, L⁻¹]`. -/
theorem ppl_zero_dvd_negClasp {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ)
    (ha : twIndex η r s ℓ = 0) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive →
      InLocalizedAnnihilator (coloredJones (twFamilyKnot r s h true η ℓ)) Q →
        toComparison ((X - 1) * extraFactor) ∣ toComparison (specialize Q) := by
  intro Q hQ0 hprim hQ
  have h1 := ppl_symbol_dvd_negClasp h η ℓ Q hQ0 hprim hQ
  rwa [ha, ppsSymbol, twP_zero, mul_one] at h1

/-- **Index `a = 0`, positive clasp**: for `W_(+,ℓ)(T_η)` with `ℓ = η r s`, the polynomial
`(L - 1) E^∨` divides the specialization of every nonzero primitive element of the localized
annihilator, in `ℚ(M)[L, L⁻¹]`. -/
theorem ppl_zero_dvd_posClasp {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ)
    (ha : twIndex η r s ℓ = 0) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive →
      InLocalizedAnnihilator (coloredJones (twFamilyKnot r s h false η ℓ)) Q →
        toComparison ((X - 1) * extraFactorMirror) ∣ toComparison (specialize Q) := by
  intro Q hQ0 hprim hQ
  have h1 := ppl_symbol_dvd_posClasp h η ℓ Q hQ0 hprim hQ
  have hrev : (1 : ℤ[X][X]).reverse = 1 := by
    rw [← C_1, reverse_C]
  rwa [ha, neg_zero, ppsSymbolMirror, twP_zero, hrev, mul_one] at h1

/-- **`L - 1 ∣ f_S` for the four families** (Lê's divisibility, [Lê 2006, Prop. 2.3], for these
knots): for both clasp signs, both companions and every twist, `L - 1` divides the
specialization of every nonzero primitive element of the localized annihilator of the coloured
Jones function, in `ℚ(M)[L, L⁻¹]`. -/
theorem ppl_sub_one_dvd {r s : ℕ} (h : IsTorusPair r s) (σ η : Bool) (ℓ : ℤ) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive →
      InLocalizedAnnihilator (coloredJones (twFamilyKnot r s h σ η ℓ)) Q →
        toComparison (X - 1) ∣ toComparison (specialize Q) := by
  intro Q hQ0 hprim hQ
  cases σ
  · have hd : (X - 1 : ℤ[X][X]) ∣ ppsSymbolMirror (-(twIndex η r s ℓ)) :=
      ⟨extraFactorMirror * (twP (-(twIndex η r s ℓ))).reverse, by rw [ppsSymbolMirror]; ring⟩
    exact (_root_.map_dvd toComparison hd).trans
      (ppl_symbol_dvd_posClasp h η ℓ Q hQ0 hprim hQ)
  · have hd : (X - 1 : ℤ[X][X]) ∣ ppsSymbol (twIndex η r s ℓ) :=
      ⟨extraFactor * twP (twIndex η r s ℓ), by rw [ppsSymbol]; ring⟩
    exact (_root_.map_dvd toComparison hd).trans
      (ppl_symbol_dvd_negClasp h η ℓ Q hQ0 hprim hQ)

end AJConjecture
