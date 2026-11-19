import Mathlib
import AJHandoff.TorusQuantum.PairQTorusInput
import AJHandoff.TorusQuantum.PairQMinimum
import AJHandoff.TorusQuantum.PairQSymbolPackage

/-!
# The quantum package of Theorem T for every torus pair

* `pairQ_formula_package` (unconditional): for every admissible pair `(r, s)` the formula
  `f = pairQFormula (pairQOddColor r s)` has a nonzero annihilator (up to a nonzero left
  coefficient), and every nonzero primitive operator in its localized annihilator has nonzero
  specialization divisible by `E` in `ℚ(M)[L, L⁻¹]`. These are the analogues of
  `exists_annihilator_torusWhiteheadFormula` and
  `extraFactor_dvd_specialize_of_annihilates_torusWhiteheadFormula`.
* `pairQ_knot_package` (conditional on the companion input `PairQTorusInput r s h`): for every
  braid knot `K` satisfying the band-and-clasp long-knot identity over `T(r, s)` with
  `2 (r - 1) s` negative half twists and of writhe `2 (r - 1) s - 2` (the output of the knot
  package P2 for `pairWhiteheadKnot r s h`), T-JONES and T-MIN hold for `K`.

The unconditional knot statement is `pairQ_knot_package` applied to `pairQ_torusInput` (crux).
-/

open Polynomial

noncomputable section

namespace AJConjecture

theorem pairQ_formula_package (r s : ℕ) (h : IsTorusPair r s) :
    (∃ Q : RecOp, Q ≠ 0 ∧ ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (pairQFormula (pairQOddColor r s)) n = 0) ∧
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive →
      (∃ c : Coeff, c ≠ 0 ∧
        ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (pairQFormula (pairQOddColor r s)) n = 0) →
      specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q) :=
  ⟨pairQ_exists_annihilator r s h, fun _ _ hprim hann ↦
    ⟨specialize_ne_zero_of_isPrimitive hprim, pairQ_extraFactor_dvd_specialize r s h hprim hann⟩⟩

theorem pairQ_knot_package (r s : ℕ) (h : IsTorusPair r s) (hT : PairQTorusInput r s h)
    (K : BraidKnot)
    (hK : ∀ c : ℕ, longKnotOp K c =
      ptrTail c (2 * c) (longKnotOp (torusPairKnot r s h) (2 * c) *
        (halfTwist c false ^ (2 * ((r - 1) * s)) * claspOp c)))
    (hw : writhe K.word = 2 * (((r - 1) * s : ℕ) : ℤ) - 2) :
    (∀ n : ℤ, laurentToField (coloredJones K n) = pairQFormula (pairQOddColor r s) n) ∧
      (∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q) ∧
      (∃ α : RecOp, IsRecurrencePolynomial (coloredJones K) α) ∧
      ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
        specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q) := by
  have hseq : ∀ n : ℤ, laurentToField (coloredJones K n) = pairQFormula (pairQOddColor r s) n :=
    pairQ_coloredJones_of_longKnotOp_torusPair hT K hK hw
  exact ⟨hseq, pairQ_tmin r s h K hseq⟩

end AJConjecture
