import Mathlib
import AJHandoff.TorusKnot.PairKMarkCalib
import AJPaper.Finger.PpFLower
import AJPaper.Finger.PpFTrefoil
import AJPaper.Finger.PpFTrefoilMirror

/-!
# Corollary 9.2: the torus-companion fingerprints of the Whitehead patterns (Unit PpF, main)

Source: Section 9 of the paper (`fingerprints.tex`), Corollary 9.2 ("Whitehead patterns"): "For
the two marked Whitehead patterns of this paper, `F_tor(W_-) ≐ E`, `F_tor(W_+) ≐ E^∨`."

* `isFingerprintOf_associated_iff`: the fingerprint of a set of knots is determined up to
  association (it is a greatest common divisor in a domain).
* `isTorusFingerprint_extraFactor`: `E` is a fingerprint of `W_-`: every tested satellite has an
  extra support (`ppf_exists_isExtraSupportOf`), `E` divides all of them
  (`ppf_twFamilyFactor_dvd`), and a common divisor divides the extra support `E` of the trefoil
  test (`ppf_isExtraSupportOf_trefoil`).
* `isTorusFingerprint_extraFactorMirror`: the same for `W_+` with `E^∨` and the mirror trefoil
  test (`ppf_isExtraSupportOf_trefoilMirror`).
* `corollary_whitehead_fingerprint`: **Corollary 9.2**: the fingerprints of `W_-` are exactly
  the elements of `ℚ(M)[L, L⁻¹]` associated to `E`, and those of `W_+` the elements associated
  to `E^∨`.

This file has no `sorry` of its own.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A fingerprint is determined up to association. -/
theorem isFingerprintOf_associated_iff {𝒦 : Set BraidKnot} {F F' : ComparisonRing}
    (hF : IsFingerprintOf 𝒦 F) : IsFingerprintOf 𝒦 F' ↔ Associated F' F := by
  constructor
  · intro hF'
    exact associated_of_dvd_dvd (hF.2.2 F' hF'.2.1) (hF'.2.2 F hF.2.1)
  · intro hassoc
    exact ⟨hF.1, fun K hK Δ hΔ ↦ hassoc.dvd.trans (hF.2.1 K hK Δ hΔ),
      fun d hd ↦ (hF.2.2 d hd).trans hassoc.symm.dvd⟩

/-- `E` is a torus-companion fingerprint of the negative-clasp Whitehead pattern. -/
theorem isTorusFingerprint_extraFactor : IsTorusFingerprint true (toComparison extraFactor) := by
  refine ⟨fun K hK ↦ ppf_exists_isExtraSupportOf hK, fun K hK Δ hΔ ↦ ?_, fun d hd ↦ ?_⟩
  · exact ppf_twFamilyFactor_dvd hK hΔ
  · exact hd _ ((ppf_mem_testSet_iff true _).mpr ⟨2, 3, isTorusPair_two_three, true, 0, rfl⟩) _
      (ppf_isExtraSupportOf_trefoil isTorusPair_two_three)

/-- `E^∨` is a torus-companion fingerprint of the positive-clasp Whitehead pattern. -/
theorem isTorusFingerprint_extraFactorMirror :
    IsTorusFingerprint false (toComparison extraFactorMirror) := by
  refine ⟨fun K hK ↦ ppf_exists_isExtraSupportOf hK, fun K hK Δ hΔ ↦ ?_, fun d hd ↦ ?_⟩
  · exact ppf_twFamilyFactor_dvd hK hΔ
  · exact hd _ ((ppf_mem_testSet_iff false _).mpr ⟨2, 3, isTorusPair_two_three, false, 0, rfl⟩) _
      (ppf_isExtraSupportOf_trefoilMirror isTorusPair_two_three)

/-- **Corollary 9.2 (Whitehead patterns).** `F_tor(W_-) ≐ E` and `F_tor(W_+) ≐ E^∨`: the
torus-companion fingerprints of the negative-clasp Whitehead pattern are exactly the elements
of `ℚ(M)[L, L⁻¹]` associated to `E = L² - (M⁴ - 4M² + 1) L + M⁴`, and those of the
positive-clasp pattern are exactly the elements associated to `E^∨ = M⁴ E(M⁻¹, L)`. -/
theorem corollary_whitehead_fingerprint :
    (∀ F : ComparisonRing, IsTorusFingerprint true F ↔
      Associated F (toComparison extraFactor)) ∧
    ∀ F : ComparisonRing, IsTorusFingerprint false F ↔
      Associated F (toComparison extraFactorMirror) :=
  ⟨fun _ ↦ isFingerprintOf_associated_iff isTorusFingerprint_extraFactor,
    fun _ ↦ isFingerprintOf_associated_iff isTorusFingerprint_extraFactorMirror⟩

end AJConjecture
