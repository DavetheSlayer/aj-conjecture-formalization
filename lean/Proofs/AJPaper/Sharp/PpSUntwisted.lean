import Mathlib
import AJTwist.Main.TwMTheorem
import AJPaper.Sharp.PpSNegClasp
import AJPaper.Sharp.PpSPosClasp

/-!
# Corollary 8.3: `A_S ∣ f_S` for the untwisted doubles (Unit PpS, node `PpS_Untwisted`)

Source: Section 8.4 of the paper (`conclusion.tex`), Corollary 8.3 ("Untwisted classical
divisibility"): "For either clasp sign and either companion chirality in Theorem 1.1, if
`ℓ = 0`, then `A_S ∣ f_S` in `R`."

Proof of the paper: at `ℓ = 0` the index is `a = η r s ≠ 0`, so `(L - 1) E 𝒫_a ∣ f_S`
(`pps_symbol_dvd_negClasp`); the classical bound `(L - 1) 𝒫_(-ℓ) 𝒫_a` at `ℓ = 0` is
`(L - 1) 𝒫_a` since `𝒫_0 = 1` (`twClassClauses_twFamilyKnot_neg`, `twP_zero`). The positive
clasp is the mirror image (`pps_symbol_dvd_posClasp`, `twClassClauses_twFamilyKnot_pos`); there
the bound is `((L - 1) 𝒫_0 𝒫_(-a)).reverse = (1 - L) 𝒫_(-a)^rev`.

* `PpsReverseClauses K`: a recurrence polynomial and an A-polynomial of `K` exist, and every
  A-polynomial divides, in `R = ℚ(M)[L, L⁻¹]`, the nonzero specialization of every nonzero
  primitive element of the localized annihilator (in particular of the recurrence polynomial:
  `ppsReverseClauses_dvd_isRecurrencePolynomial`).
* `twIndex_zero_ne_zero`: at `ℓ = 0` the index is `± r s ≠ 0`.
* `pps_aPolynomial_mul_factor_dvd_untwisted`: the proof gives more: `A_S · G ∣ f_S`, with
  `G = E` or `E^∨` the obstruction factor of Theorem 1.1.
* `corollary_untwisted_reverse`: **Corollary 8.3** for the four families.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The clauses of Corollary 8.3 for one knot `K`: a recurrence polynomial exists, an
A-polynomial exists, and every A-polynomial divides the nonzero specialization of every nonzero
primitive element of the localized annihilator of the coloured Jones function, in
`ℚ(M)[L, L⁻¹]`. -/
def PpsReverseClauses (K : BraidKnot) : Prop :=
  (∃ α : RecOp, IsRecurrencePolynomial (coloredJones K) α) ∧
    (∃ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A) ∧
    ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
      ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
        specialize Q ≠ 0 ∧ toComparison A ∣ toComparison (specialize Q)

/-- The clauses give `A_K ∣ f_K = α_K(-1, M, L)` for the recurrence polynomial `α_K`. -/
theorem ppsReverseClauses_dvd_isRecurrencePolynomial {K : BraidKnot} (hK : PpsReverseClauses K)
    {α : RecOp} (hα : IsRecurrencePolynomial (coloredJones K) α) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet K) A) :
    toComparison A ∣ toComparison (specialize α) :=
  (hK.2.2 A hA α hα.1 hα.2.2.2 hα.2.1).2

/-- Without twist the effective index `a = ± r s` is not zero. -/
theorem twIndex_zero_ne_zero {r s : ℕ} (h : IsTorusPair r s) (η : Bool) :
    twIndex η r s 0 ≠ 0 := by
  have hr : 2 ≤ r := h.1
  have hs : r < s := h.2.1
  have hm : (1 : ℤ) ≤ ((r * s : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  cases η <;> simp only [twIndex, sub_zero] <;> simp <;> omega

/-- The reverse of `L - 1` is `1 - L`. -/
private theorem reverse_X_sub_one_ppsUntwisted : (X - 1 : ℤ[X][X]).reverse = 1 - X := by
  have h : (X - 1 : ℤ[X][X]) = X + C (-1) := by
    rw [map_neg, map_one, sub_eq_add_neg]
  have hX : (X : ℤ[X][X]).reverse = 1 := by
    have h1 := reverse_mul_X (1 : ℤ[X][X])
    rwa [one_mul, ← C_1, reverse_C] at h1
  rw [h, reverse_add_C, natDegree_X, hX, map_neg, map_one]
  ring

/-- Negative clasp without twist: `A_S · E ∣ f_S`. -/
private theorem aPolynomial_mul_factor_dvd_neg_ppsUntwisted {r s : ℕ} (h : IsTorusPair r s)
    (η : Bool) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (twFamilyKnot r s h true η 0)) A) (Q : RecOp)
    (hQ0 : Q ≠ 0) (hprim : Q.IsPrimitive)
    (hQ : InLocalizedAnnihilator (coloredJones (twFamilyKnot r s h true η 0)) Q) :
    toComparison (A * extraFactor) ∣ toComparison (specialize Q) := by
  have hb := ((twClassClauses_twFamilyKnot_neg h η 0).2 A hA).1
  rw [twBound, neg_zero, twP_zero, mul_one] at hb
  have hs := pps_symbol_dvd_negClasp h η 0 (twIndex_zero_ne_zero h η) Q hQ0 hprim hQ
  refine dvd_trans ?_ hs
  rw [ppsSymbol, mul_right_comm, map_mul, map_mul]
  exact mul_dvd_mul_right hb _

/-- Positive clasp without twist: `A_S · E^∨ ∣ f_S`. -/
private theorem aPolynomial_mul_factor_dvd_pos_ppsUntwisted {r s : ℕ} (h : IsTorusPair r s)
    (η : Bool) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (twFamilyKnot r s h false η 0)) A) (Q : RecOp)
    (hQ0 : Q ≠ 0) (hprim : Q.IsPrimitive)
    (hQ : InLocalizedAnnihilator (coloredJones (twFamilyKnot r s h false η 0)) Q) :
    toComparison (A * extraFactorMirror) ∣ toComparison (specialize Q) := by
  have hb := ((twClassClauses_twFamilyKnot_pos h η 0).2 A hA).1
  rw [twBound, twP_zero, mul_one, reverse_mul_of_domain, reverse_X_sub_one_ppsUntwisted] at hb
  have hs := pps_symbol_dvd_posClasp h η 0 (twIndex_zero_ne_zero h η) Q hQ0 hprim hQ
  have he : (1 - X) * (twP (-(twIndex η r s 0))).reverse * extraFactorMirror =
      -ppsSymbolMirror (-(twIndex η r s 0)) := by
    rw [ppsSymbolMirror]
    ring
  refine dvd_trans ?_ hs
  rw [← dvd_neg, ← map_neg, ← he, map_mul, map_mul _ _ extraFactorMirror]
  exact mul_dvd_mul_right hb _

/-- **The proof of Corollary 8.3 gives `A_S · G ∣ f_S`.** For the untwisted double
`W_(ε,0)(T_η)`, every A-polynomial times the obstruction factor of Theorem 1.1 (`E` for the
negative clasp, `E^∨` for the positive clasp) divides the specialization of every nonzero
primitive element of the localized annihilator, in `ℚ(M)[L, L⁻¹]`. -/
theorem pps_aPolynomial_mul_factor_dvd_untwisted {r s : ℕ} (h : IsTorusPair r s) (σ η : Bool)
    {A : ℤ[X][X]} (hA : IsAPolynomialOf (eigenvalueSet (twFamilyKnot r s h σ η 0)) A) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive →
      InLocalizedAnnihilator (coloredJones (twFamilyKnot r s h σ η 0)) Q →
        toComparison (A * twFamilyFactor σ) ∣ toComparison (specialize Q) := by
  intro Q hQ0 hprim hQ
  cases σ
  · exact aPolynomial_mul_factor_dvd_pos_ppsUntwisted h η hA Q hQ0 hprim hQ
  · exact aPolynomial_mul_factor_dvd_neg_ppsUntwisted h η hA Q hQ0 hprim hQ

/-- **Corollary 8.3 (untwisted classical divisibility).** For coprime `2 ≤ r < s`, both clasp
signs `σ` and both companions `η`, the untwisted double `W_(ε,0)(T_η)` has a recurrence
polynomial and an A-polynomial, and every A-polynomial `A_S` divides `f_S` in
`R = ℚ(M)[L, L⁻¹]`, for `f_S` the nonzero specialization of any nonzero primitive element of the
localized annihilator. -/
theorem corollary_untwisted_reverse {r s : ℕ} (h : IsTorusPair r s) (σ η : Bool) :
    PpsReverseClauses (twFamilyKnot r s h σ η 0) := by
  have hc := twFamilyClauses_twFamilyKnot h σ η 0
  refine ⟨hc.2.1, hc.2.2.2.1, fun A hA Q hQ0 hprim hQ ↦
    ⟨specialize_ne_zero_of_isPrimitive hprim, ?_⟩⟩
  have h1 := pps_aPolynomial_mul_factor_dvd_untwisted h σ η hA Q hQ0 hprim hQ
  rw [map_mul] at h1
  exact (dvd_mul_right _ _).trans h1

end AJConjecture
