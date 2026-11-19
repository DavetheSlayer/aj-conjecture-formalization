import Mathlib
import AJConjecture.ColoredJones
import AJConjecture.FieldActionBridge
import AJConjecture.ExtraFactorPrime
import AJConjecture.QAlgPseudoFactorNormalize
import AJHandoff.TorusQuantum.PairQAnnihilator

/-!
# The return to the signed sequence

Source: Section 8.1 of the revision-5 manuscript (`conclusion.tex`, "Return to the signed
sequence") and Section 6.7 (`selection.tex`, "The selected right divisor").

On the positive tail the unreduced sequence is `[N] F_N`. For a primitive `Q` in the localized
annihilator of the signed sequence, the gauge `gaugeOp Q` annihilates a tail of `F`
(`pairQ_exists_tail_annihilator_gaugeOp`), hence is a left pseudo-multiple of the selected right
divisor `R`; the specialization at `t = -1` is multiplicative on Ore products and the gauge
multiplies it by `M² - 1` (`toComparison_specialize_dvd_of_oreMul`, `specialize_gaugeOp`), so the
factors of `R(-1, M, L)` divide `Q(-1, M, L)` in `ℚ(M)[L, L⁻¹]`.

* `tws_extraFactor_dvd_specialize_of_tail`: the signed return for a selected divisor `R` whose
  specialization is nonzero and divisible by `E`.
* `tws_extraFactor_dvd_specialize_of_pseudoFactor`: the selected divisor at `a = 0`: if
  `β P = S ⋆ R` with `S` of order at most one and `E` divides `P(-1, M, L) ≠ 0`, then `R` is a
  power of `t + 1` times an operator whose specialization is nonzero and divisible by `E` (`E` is
  prime and of degree two in `L`, so it cannot divide the specialization of `S`).
* `tws_survival_of_formula`: the third clause of `PairTClauses` for a knot whose coloured Jones
  function is the formula of an input `u`; no existence of an annihilator is assumed.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **Signed return.** If every tail annihilator of the reduced sequence of `u` is a left
pseudo-multiple of `R`, and `E` divides the nonzero specialization of `R`, then `E` divides the
specialization of every primitive operator in the localized annihilator of the signed unreduced
sequence `pairQFormula u`. -/
theorem tws_extraFactor_dvd_specialize_of_tail (u : ℕ → RatFunc ℚ) {R : RecOp}
    (hR : specialize R ≠ 0) (hER : toComparison extraFactor ∣ toComparison (specialize R))
    (htail : ∀ {Q' : RecOp} {n₁ : ℤ},
      (∀ n : ℤ, n₁ ≤ n → opApplyField Q' (pairQReducedFormulaEven u) n = 0) →
      ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q' = oreMul coeffShift T R)
    {Q : RecOp} (hQ : Q.IsPrimitive)
    (hann : ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (pairQFormula u) n = 0) :
    toComparison extraFactor ∣ toComparison (specialize Q) := by
  obtain ⟨n₁, hn₁⟩ := pairQ_exists_tail_annihilator_gaugeOp u hann
  obtain ⟨β, hβ, T, hT⟩ := htail hn₁
  have hX : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
    intro h0
    have h1 := congrArg (Polynomial.eval 0) h0
    norm_num at h1
  have hspec : specialize (gaugeOp Q) ≠ 0 := by
    rw [specialize_gaugeOp]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hX) (specialize_ne_zero_of_isPrimitive hQ)
  have h1 : toComparison (specialize R) ∣ toComparison (specialize (gaugeOp Q)) :=
    toComparison_specialize_dvd_of_oreMul hβ hT hspec hR
  have h2 := hER.trans h1
  rw [specialize_gaugeOp, map_mul] at h2
  exact (isUnit_toComparison_coeff_of_ne_zero hX).dvd_mul_left.mp h2

/-- **The selected divisor at `a = 0`.** A right pseudo-factor `R` of `P` with cofactor of order
at most one inherits the factor `E` of the nonzero specialization of `P`, after removal of a
power of `t + 1`. -/
theorem tws_extraFactor_dvd_specialize_of_pseudoFactor {P S R : RecOp} {β : Coeff} (hβ : β ≠ 0)
    (hfac : C β * P = oreMul coeffShift S R) (hP : specialize P ≠ 0)
    (hE : toComparison extraFactor ∣ toComparison (specialize P)) (hS : S.natDegree ≤ 1) :
    ∃ R' : RecOp, specialize R' ≠ 0 ∧
      toComparison extraFactor ∣ toComparison (specialize R') ∧
      ∃ a : ℕ, R = C (C ((X + 1 : ℤ[X]) ^ a)) * R' := by
  obtain ⟨β', S', R', hβ', hS', hR', hdS, -, hfac', a, ha⟩ :=
    exists_normalized_pseudoFactor hP hβ hfac
  refine ⟨R', hR', ?_, a, ha⟩
  have hspec := congrArg (fun p ↦ toComparison (specialize p)) hfac'
  simp only [specialize_oreMul, map_mul] at hspec
  have hdvd : toComparison extraFactor ∣
      toComparison (specialize S') * toComparison (specialize R') :=
    hspec ▸ Dvd.dvd.mul_left hE _
  rcases prime_toComparison_extraFactor.dvd_or_dvd hdvd with h | h
  · exfalso
    have h2 : extraFactor.natDegree ≤ (specialize S').natDegree :=
      natDegree_le_of_dvd (extraFactor_dvd_of_toComparison_dvd h) hS'
    have h3 : (specialize S').natDegree ≤ S'.natDegree := natDegree_map_le
    have h4 : (2 : ℕ) ≤ extraFactor.natDegree := by
      refine le_natDegree_of_ne_zero ?_
      have hc : extraFactor.coeff 2 = 1 := by
        simp only [extraFactor, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X,
          coeff_C]
        simp
      rw [hc]
      exact one_ne_zero
    omega
  · exact h

/-- The survival clause for a knot whose coloured Jones function is the formula of `u`: if `E`
divides the specialization of every primitive operator in the localized annihilator of the
formula, then every nonzero primitive element of the localized annihilator of the coloured Jones
function has nonzero specialization divisible by `E` in `ℚ(M)[L, L⁻¹]`. -/
theorem tws_survival_of_formula (K : BraidKnot) (u : ℕ → RatFunc ℚ)
    (hseq : ∀ n : ℤ, laurentToField (coloredJones K n) = pairQFormula u n)
    (hE : ∀ Q : RecOp, Q.IsPrimitive →
      (∃ c : Coeff, c ≠ 0 ∧ ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (pairQFormula u) n = 0) →
        toComparison extraFactor ∣ toComparison (specialize Q)) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
      specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q) := by
  intro Q _ hprim hQ
  refine ⟨specialize_ne_zero_of_isPrimitive hprim, hE Q hprim ?_⟩
  obtain ⟨c, hc, hann⟩ := hQ
  refine ⟨c, hc, fun n ↦ ?_⟩
  have h := congrArg laurentToField (hann n)
  have hfun : (fun m ↦ laurentToField (coloredJones K m)) = pairQFormula u := funext hseq
  rwa [map_zero, laurentToField_opApply, hfun] at h

end AJConjecture
