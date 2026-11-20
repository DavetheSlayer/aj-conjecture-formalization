import Mathlib
import AJTwist.Knot.TwKFamilyWord
import AJPaper.Sharp.PpSUntwisted

/-!
# Section 8.4 in braid-word form (Unit PpS, node `PpS_Release`)

The statements of Section 8.4 stated, as `release_theoremFourFamilies` of the release repository,
so that every constant they mention is a data definition (a number of strands, a braid word, a
polynomial) or a baseline predicate: the knots are all `K : BraidKnot` with the number of strands
`twFamilyStrands r s η ℓ` and the braid word `twFamilyWord r s σ η ℓ` (`σ = true`: negative
clasp; `η = true`: companion `T(r, s)`, `η = false`: `T(r, -s)`), of which there is exactly one
(`eq_twFamilyKnot_of_word`).

* `release_corollaryUntwisted`: **Corollary 8.3**. For coprime `2 ≤ r < s`, both clasp signs and
  both companions, a closed braid with the data of the untwisted double (`ℓ = 0`) exists; each
  one has a recurrence polynomial and an A-polynomial, and every A-polynomial divides the
  nonzero specialization of every nonzero primitive element of the localized annihilator of its
  coloured Jones function, in `ℚ(M)[L, L⁻¹]`.
* `release_wholeSymbol`: the statement after Corollary 8.3, with the whole symbol. For every
  twist `ℓ` with `a = η r s - ℓ ≠ 0`: for the negative clasp `(L - 1) E 𝒫_a` divides these
  specializations, and for the positive clasp `(L - 1) E^∨ 𝒫_(-a)^rev` does (up to a unit of
  `ℚ(M)[L, L⁻¹]`, the symbol `(L - 1) E 𝒫_(-a)` of the mirror knot with the meridian inverted:
  `pps_symbol_mInv_associated`).

Both are proved here from the nodes of the package; this file has no `sorry` of its own.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **Corollary 8.3 in braid-word form.** For coprime `2 ≤ r < s`, both clasp signs `σ` and both
companions `η`: a closed braid with `twFamilyStrands r s η 0` strands and the word
`twFamilyWord r s σ η 0` exists, and for each one a recurrence polynomial and an A-polynomial
exist and every A-polynomial `A_S` divides `f_S` in `ℚ(M)[L, L⁻¹]`, where `f_S` is the nonzero
specialization of any nonzero primitive element of the localized annihilator. -/
theorem release_corollaryUntwisted :
    (∀ r s : ℕ, IsTorusPair r s → ∀ σ η : Bool, ∃ K : BraidKnot,
      K.strands = twFamilyStrands r s η 0 ∧ K.word = twFamilyWord r s σ η 0) ∧
    ∀ r s : ℕ, IsTorusPair r s → ∀ (σ η : Bool) (K : BraidKnot),
      K.strands = twFamilyStrands r s η 0 → K.word = twFamilyWord r s σ η 0 →
        (∃ α : RecOp, IsRecurrencePolynomial (coloredJones K) α) ∧
        (∃ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A) ∧
        ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
          ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
            specialize Q ≠ 0 ∧ toComparison A ∣ toComparison (specialize Q) := by
  refine ⟨fun r s h σ η ↦ ⟨twFamilyKnot r s h σ η 0, strands_twFamilyKnot r s h σ η 0,
    word_twFamilyKnot r s h σ η 0⟩, fun r s h σ η K hs hw ↦ ?_⟩
  rw [eq_twFamilyKnot_of_word h σ η 0 hs hw]
  exact corollary_untwisted_reverse h σ η

/-- **The whole symbol in braid-word form** (Section 8.4, after Corollary 8.3). For coprime
`2 ≤ r < s`, both companions `η` and every twist `ℓ` with `a = η r s - ℓ ≠ 0`: for every closed
braid with the data of the negative-clasp satellite, `(L - 1) E 𝒫_a` divides the specialization
of every nonzero primitive element of the localized annihilator; for the positive clasp
`(L - 1) E^∨ 𝒫_(-a)^rev` does; both in `ℚ(M)[L, L⁻¹]`. -/
theorem release_wholeSymbol :
    (∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ), twIndex η r s ℓ ≠ 0 →
      ∀ K : BraidKnot, K.strands = twFamilyStrands r s η ℓ →
        K.word = twFamilyWord r s true η ℓ →
          ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
            toComparison ((X - 1) * extraFactor * twP (twIndex η r s ℓ)) ∣
              toComparison (specialize Q)) ∧
    ∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ), twIndex η r s ℓ ≠ 0 →
      ∀ K : BraidKnot, K.strands = twFamilyStrands r s η ℓ →
        K.word = twFamilyWord r s false η ℓ →
          ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
            toComparison ((X - 1) * extraFactorMirror * (twP (-(twIndex η r s ℓ))).reverse) ∣
              toComparison (specialize Q) := by
  refine ⟨fun r s h η ℓ ha K hs hw ↦ ?_, fun r s h η ℓ ha K hs hw ↦ ?_⟩
  · rw [eq_twFamilyKnot_of_word h true η ℓ hs hw]
    exact pps_symbol_dvd_negClasp h η ℓ ha
  · rw [eq_twFamilyKnot_of_word h false η ℓ hs hw]
    exact pps_symbol_dvd_posClasp h η ℓ ha

end AJConjecture
