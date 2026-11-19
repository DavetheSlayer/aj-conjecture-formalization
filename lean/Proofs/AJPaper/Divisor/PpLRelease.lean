import Mathlib
import AJTwist.Knot.TwKFamilyWord
import AJPaper.Divisor.PpLKnots

/-!
# Section 8.4 for every twist, in braid-word form (Unit PpL, node `PpL_Release`)

The statements of `AJPaper/Divisor/PpLKnots.lean` stated, as `release_wholeSymbol` of
`AJPaper/Sharp/PpSRelease.lean`, so that every constant they mention is a data definition (a
number of strands, a braid word, a polynomial) or a baseline predicate: the knots are all
`K : BraidKnot` with the number of strands `twFamilyStrands r s η ℓ` and the braid word
`twFamilyWord r s σ η ℓ` (`σ = true`: negative clasp; `η = true`: companion `T(r, s)`,
`η = false`: `T(r, -s)`), of which there is exactly one (`eq_twFamilyKnot_of_word`).

* `release_wholeSymbolAllTwists`: `release_wholeSymbol` without the hypothesis `a ≠ 0`. For
  coprime `2 ≤ r < s`, both companions and **every** twist `ℓ`, with `a = η r s - ℓ`: for the
  negative clasp `(L - 1) E 𝒫_a` divides the specialization of every nonzero primitive element
  of the localized annihilator, and for the positive clasp `(L - 1) E^∨ 𝒫_(-a)^rev` does.
* `release_subOneDvd`: the statement of Section 8.4 at `a = 0` and Lê's divisibility for the
  four families: `L - 1 ∣ f_S` for both clasp signs, both companions and every twist.
* `release_indexZero`: at `a = 0` the factor is `(L - 1) E` for the negative clasp and
  `(L - 1) E^∨` for the positive clasp.

All three are proved here from `AJPaper/Divisor/PpLKnots.lean`; this file has no `sorry` of its
own.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **The whole symbol in braid-word form, every twist** (Section 8.4). For coprime
`2 ≤ r < s`, both companions `η` and every twist `ℓ`, with `a = η r s - ℓ`: for every closed
braid with the data of the negative-clasp satellite, `(L - 1) E 𝒫_a` divides the specialization
of every nonzero primitive element of the localized annihilator; for the positive clasp
`(L - 1) E^∨ 𝒫_(-a)^rev` does; both in `ℚ(M)[L, L⁻¹]`. -/
theorem release_wholeSymbolAllTwists :
    (∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ) (K : BraidKnot),
      K.strands = twFamilyStrands r s η ℓ → K.word = twFamilyWord r s true η ℓ →
        ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
          toComparison ((X - 1) * extraFactor * twP (twIndex η r s ℓ)) ∣
            toComparison (specialize Q)) ∧
    ∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ) (K : BraidKnot),
      K.strands = twFamilyStrands r s η ℓ → K.word = twFamilyWord r s false η ℓ →
        ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
          toComparison ((X - 1) * extraFactorMirror * (twP (-(twIndex η r s ℓ))).reverse) ∣
            toComparison (specialize Q) := by
  refine ⟨fun r s h η ℓ K hs hw ↦ ?_, fun r s h η ℓ K hs hw ↦ ?_⟩
  · rw [eq_twFamilyKnot_of_word h true η ℓ hs hw]
    exact ppl_symbol_dvd_negClasp h η ℓ
  · rw [eq_twFamilyKnot_of_word h false η ℓ hs hw]
    exact ppl_symbol_dvd_posClasp h η ℓ

/-- **`L - 1 ∣ f_S` in braid-word form** (Section 8.4, the case `a = 0`, and all other
indices): for coprime `2 ≤ r < s`, both clasp signs, both companions and every twist `ℓ`, for
every closed braid with the data of the satellite, `L - 1` divides the specialization of every
nonzero primitive element of the localized annihilator of its coloured Jones function, in
`ℚ(M)[L, L⁻¹]`. -/
theorem release_subOneDvd :
    ∀ r s : ℕ, IsTorusPair r s → ∀ (σ η : Bool) (ℓ : ℤ) (K : BraidKnot),
      K.strands = twFamilyStrands r s η ℓ → K.word = twFamilyWord r s σ η ℓ →
        ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
          toComparison (X - 1) ∣ toComparison (specialize Q) := by
  intro r s h σ η ℓ K hs hw
  rw [eq_twFamilyKnot_of_word h σ η ℓ hs hw]
  exact ppl_sub_one_dvd h σ η ℓ

/-- **Index `a = 0` in braid-word form**: for coprime `2 ≤ r < s`, both companions and the
twist `ℓ` with `η r s - ℓ = 0`: for the negative clasp `(L - 1) E` divides the specialization of
every nonzero primitive element of the localized annihilator, and for the positive clasp
`(L - 1) E^∨` does; both in `ℚ(M)[L, L⁻¹]`. -/
theorem release_indexZero :
    (∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ), twIndex η r s ℓ = 0 →
      ∀ K : BraidKnot, K.strands = twFamilyStrands r s η ℓ →
        K.word = twFamilyWord r s true η ℓ →
          ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
            toComparison ((X - 1) * extraFactor) ∣ toComparison (specialize Q)) ∧
    ∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ), twIndex η r s ℓ = 0 →
      ∀ K : BraidKnot, K.strands = twFamilyStrands r s η ℓ →
        K.word = twFamilyWord r s false η ℓ →
          ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
            toComparison ((X - 1) * extraFactorMirror) ∣ toComparison (specialize Q) := by
  refine ⟨fun r s h η ℓ ha K hs hw ↦ ?_, fun r s h η ℓ ha K hs hw ↦ ?_⟩
  · rw [eq_twFamilyKnot_of_word h true η ℓ hs hw]
    exact ppl_zero_dvd_negClasp h η ℓ ha
  · rw [eq_twFamilyKnot_of_word h false η ℓ hs hw]
    exact ppl_zero_dvd_posClasp h η ℓ ha

end AJConjecture
