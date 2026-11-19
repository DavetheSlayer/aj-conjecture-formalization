import Mathlib
import AJConjecture.QAlgOreMulZero
import AJTwist.Select.TwSSelection
import AJTwist.Select.TwSSignedReturn

/-!
# Survival of the factor `E` in every primitive signed annihilator

Source: Sections 6.7 and 8.1 of the revision-5 manuscript: "`E ∣ f_S ≠ 0` for each negative-clasp
satellite", in the form of the third clause of `PairTClauses`
(`AJHandoff.TorusKnot.PairKTheoremT`).

Inputs taken as hypotheses (proved by the packages TwQ and TwF, see `DESIGN.md`):

* the transfer operator `P` (the row `P_a`, written with the forward shift) with
  `specialize P ≠ 0` and `E ∣ P(-1, M, L)` in `ℚ(M)[L, L⁻¹]`;
* the transfer in module form `TwsForcingInPeriods ℓ u P` (eq. (finite-module-force));
* for `a ≠ 0`: no right pseudo-factor of `P` of intermediate order (irreducibility over
  `ℚ(t, M)`); for `a = 0`: `P` of order at most `3` without right pseudo-factor of order one.

No existence of a nonzero annihilator is assumed or proved here.

* `tws_extraFactor_dvd_specialize_of_irreducible`, `tws_extraFactor_dvd_specialize_of_no_linear`:
  for any input `u` with `TwsSelects ℓ u`.
* `tws_survival`: for the twisted input `twsInput η r s ℓ` and a knot whose coloured Jones
  function is `pairQFormula (twsInput η r s ℓ)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Survival of `E`, irreducible case (`a ≠ 0`). -/
theorem tws_extraFactor_dvd_specialize_of_irreducible {ℓ : ℤ} {u : ℕ → RatFunc ℚ}
    (hsel : TwsSelects ℓ u) {P : RecOp} (hP : specialize P ≠ 0)
    (hE : toComparison extraFactor ∣ toComparison (specialize P))
    (hirr : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree = 0 ∨ R.natDegree = P.natDegree)
    (hforce : TwsForcingInPeriods ℓ u P) {Q : RecOp} (hQ : Q.IsPrimitive)
    (hann : ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (pairQFormula u) n = 0) :
    toComparison extraFactor ∣ toComparison (specialize Q) := by
  have hP0 : P ≠ 0 := fun h ↦ hP (by rw [h, map_zero])
  exact tws_extraFactor_dvd_specialize_of_tail u hP hE
    (fun hQ' ↦ tws_tail_annihilator_of_selects hsel hP0 hirr hforce hQ') hQ hann

/-- Survival of `E`, the case of no first-order right divisor (`a = 0`). -/
theorem tws_extraFactor_dvd_specialize_of_no_linear {ℓ : ℤ} {u : ℕ → RatFunc ℚ}
    (hsel : TwsSelects ℓ u) {P : RecOp} (hP : specialize P ≠ 0)
    (hE : toComparison extraFactor ∣ toComparison (specialize P)) (hdeg : P.natDegree ≤ 3)
    (hlin : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree ≠ 1)
    (hforce : TwsForcingInPeriods ℓ u P) {Q : RecOp} (hQ : Q.IsPrimitive)
    (hann : ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (pairQFormula u) n = 0) :
    toComparison extraFactor ∣ toComparison (specialize Q) := by
  have hP0 : P ≠ 0 := fun h ↦ hP (by rw [h, map_zero])
  obtain ⟨R, hRdeg, ⟨β, hβ, S, hfac⟩, hR⟩ := tws_selected_divisor_of_selects hsel hP0 hlin hforce
  have hne : oreMul coeffShift S R ≠ 0 := hfac ▸ mul_ne_zero (C_ne_zero.mpr hβ) hP0
  have hS0 : S ≠ 0 := by
    rintro rfl
    exact hne (oreMul_zero_left _ _)
  have hR0 : R ≠ 0 := by
    rintro rfl
    exact hne (oreMul_zero_right _ _)
  have hS : S.natDegree ≤ 1 := by
    have h1 := natDegree_oreMul coeffShift_injective hS0 hR0
    rw [← hfac, natDegree_C_mul hβ] at h1
    omega
  obtain ⟨R', hR'0, hER', a, rfl⟩ :=
    tws_extraFactor_dvd_specialize_of_pseudoFactor hβ hfac hP hE hS
  refine tws_extraFactor_dvd_specialize_of_tail u hR'0 hER' (fun hQ' ↦ ?_) hQ hann
  obtain ⟨β', hβ', T, hT⟩ := hR hQ'
  refine ⟨β', hβ', oreMul coeffShift T (C (C ((X + 1 : ℤ[X]) ^ a))), ?_⟩
  rw [hT, oreMul_assoc, oreMul_C_left]

/-- **Selection and signed return (Sections 6 and 8.1).** Let `K` be a knot whose coloured Jones
function is the formula of the twisted input `twsInput η r s ℓ` (the negative-clasp satellite
`W_{-,ℓ}(T(r, ± s))`), and `P` a transfer operator with `P F` in the module of the Gaussian
periods, whose specialization is nonzero and divisible by `E`, irreducible if `a ≠ 0` and of
order at most three without first-order right divisor if `a = 0`. Then every nonzero primitive
element of the localized annihilator of the coloured Jones function has nonzero specialization
divisible by `E` in `ℚ(M)[L, L⁻¹]`. -/
theorem tws_survival (η : Bool) (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (ℓ : ℤ) {P : RecOp}
    (hP : specialize P ≠ 0) (hE : toComparison extraFactor ∣ toComparison (specialize P))
    (hirr : twIndex η r s ℓ ≠ 0 → ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp},
      C β * P = oreMul coeffShift S R → R.natDegree = 0 ∨ R.natDegree = P.natDegree)
    (hzero : twIndex η r s ℓ = 0 → P.natDegree ≤ 3 ∧ ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp},
      C β * P = oreMul coeffShift S R → R.natDegree ≠ 1)
    (hforce : TwsForcingInPeriods ℓ (twsInput η r s ℓ) P) (K : BraidKnot)
    (hseq : ∀ n : ℤ, laurentToField (coloredJones K n) = pairQFormula (twsInput η r s ℓ) n) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
      specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q) := by
  refine tws_survival_of_formula K _ hseq fun Q hQ hann ↦ ?_
  have hsel := tws_selects η r s hr hs ℓ
  by_cases ha : twIndex η r s ℓ = 0
  · exact tws_extraFactor_dvd_specialize_of_no_linear hsel hP hE (hzero ha).1 (hzero ha).2 hforce
      hQ hann
  · exact tws_extraFactor_dvd_specialize_of_irreducible hsel hP hE (hirr ha) hforce hQ hann

end AJConjecture
