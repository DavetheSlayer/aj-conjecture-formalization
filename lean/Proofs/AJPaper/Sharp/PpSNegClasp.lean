import Mathlib
import AJTwist.Main.TwMNegClasp
import AJTwist.Main.TwMJones
import AJPaper.Sharp.PpSTail
import AJPaper.Sharp.PpSSymbol

/-!
# The whole symbol divides `f_S`: negative clasp, index `a ≠ 0` (Unit PpS, node `PpS_NegClasp`)

Source: Section 8.4 of the paper (`conclusion.tex`), the proof of Corollary 8.3 and the
paragraph after it: "Section 6.7 selects the full monic form of `P_a`. The Gauss specialization
of Section 8.1 then gives `(L - 1) E 𝒫_a ∣ f_S`" and "for a negative-clasp satellite with
`ℓ ≠ 0`, the same selection and specialization give `(L - 1) 𝒫_a ∣ f_S` when `a ≠ 0`".

The library's `tws_survival` keeps only the factor `E`. For `a ≠ 0` the transfer operator
`P_a` is irreducible (`twf_irreducible`), so every tail annihilator of the reduced sequence is a
left pseudo-multiple of `P_a` itself (`tws_tail_annihilator_of_selects`), and the signed return
for the whole symbol (`pps_specialize_dvd_of_tail`) gives the whole symbol
`(L - 1) E 𝒫_a = ppsSymbol a` (`pps_specialize_twTransferOp_associated`).

* `pps_symbol_dvd_of_formula`: for a knot whose coloured Jones function is `twFormula η r s ℓ`
  with `a = twIndex η r s ℓ ≠ 0`.
* `pps_symbol_dvd_negClasp`: for the negative-clasp satellites `W_(-,ℓ)(T_η)` of the library.

The case `a = 0` (`ℓ = η r s`) is not covered: there the selected divisor may be a proper right
factor of `P_0` and the library only has `E ∣ f_S`; see `pps_symbol_zero_dvd`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **The whole symbol survives, `a ≠ 0`.** For a knot whose coloured Jones function is
`twFormula η r s ℓ` with effective index `a = η r s - ℓ ≠ 0`, the polynomial `(L - 1) E 𝒫_a`
divides the specialization of every nonzero primitive element of the localized annihilator, in
`ℚ(M)[L, L⁻¹]`. -/
theorem pps_symbol_dvd_of_formula {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ)
    (ha : twIndex η r s ℓ ≠ 0) (K : BraidKnot)
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
        (fun hβ _ _ hfac ↦ twf_irreducible _ ha hβ hfac) (twQ_transfer_mem_periodSpan η r s ℓ)
        hQ') hQ hann
  exact (pps_specialize_twTransferOp_associated _).symm.dvd.trans h1

/-- **The whole symbol survives for the negative clasp, `a ≠ 0`** (Section 8.4): for the
satellite `W_(-,ℓ)(T_η)` with `a = η r s - ℓ ≠ 0`, the polynomial `(L - 1) E 𝒫_a` divides the
specialization of every nonzero primitive element of the localized annihilator of its coloured
Jones function, in `ℚ(M)[L, L⁻¹]`. -/
theorem pps_symbol_dvd_negClasp {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ)
    (ha : twIndex η r s ℓ ≠ 0) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive →
      InLocalizedAnnihilator (coloredJones (twFamilyKnot r s h true η ℓ)) Q →
        toComparison (ppsSymbol (twIndex η r s ℓ)) ∣ toComparison (specialize Q) :=
  pps_symbol_dvd_of_formula h η ℓ ha _ (twm_coloredJones_negClasp h η ℓ)

end AJConjecture
