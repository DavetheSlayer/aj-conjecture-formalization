import Mathlib
import AJFamily.Assembly.ConditionalCounterexample
import AJHandoff.TorusKnot.PairKAPolyHorizontal
import AJHandoff.TorusKnot.PairKLongKnot
import AJHandoff.TorusQuantum.PairQPackage

/-!
# T-AJ: each `Wh⁻₀(T(r, s))` is a counterexample (given the companion input)

`pairWhiteheadKnot_counterexample_of_input`: for every admissible pair, given the odd-colour
input `PairQTorusInput r s h` of package P1, the localized square-free `SL₂` AJ statement fails
for `pairWhiteheadKnot r s h`, `E` divides the nonzero specialisation of every nonzero primitive
element of the localized annihilator, and `E` is coprime to every A-polynomial. Inputs:

* P1 (`pairQ_formula_package`, `pairQ_knot_package`): the colour sequence is
  `pairQFormula (pairQOddColor r s)`, it has a nonzero annihilator, and `E` divides the
  specialisation of every primitive annihilator of the formula;
* this package: the long-knot identity and the writhe (T-KNOT), the bound
  `evalPoint_famBound_pair`, the zero of `E` off the bound and the A-polynomial (T-CLASS,
  T-AEX);
* the generic assembly `conditional_counterexample` of the library.
-/

open Polynomial

namespace AJConjecture

/-- T-AJ for every admissible pair, given the companion input of P1. -/
theorem pairWhiteheadKnot_counterexample_of_input {r s : ℕ} (h : IsTorusPair r s)
    (hT : PairQTorusInput r s h) :
    ¬ AJSquareFree (pairWhiteheadKnot r s h) ∧
      (∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive →
        InLocalizedAnnihilator (coloredJones (pairWhiteheadKnot r s h)) Q →
          specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q)) ∧
      ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A →
        IsCoprime (toComparison extraFactor) (toComparison A) := by
  have hq := pairQ_formula_package r s h
  have hk := pairQ_knot_package r s h hT (pairWhiteheadKnot r s h)
    (longKnotOp_pairWhiteheadKnot h) (writhe_pairWhiteheadKnot h)
  obtain ⟨A, hA, -, -⟩ := exists_aPolynomial_pair h
  exact conditional_counterexample (pairWhiteheadKnot r s h) (pairQFormula (pairQOddColor r s))
    hk.1 hq.1 (fun Q hprim hann ↦ (hq.2 Q hprim.ne_zero hprim hann).2) (famBound (r * s))
    (fun p hp ↦ evalPoint_famBound_pair h hp) (exists_extraFactor_zero_not_famBound_pair h)
    ⟨A, hA⟩

end AJConjecture
