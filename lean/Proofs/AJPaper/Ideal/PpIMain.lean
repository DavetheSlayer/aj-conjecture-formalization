import Mathlib
import AJTwist.Knot.TwKFamilyWord
import AJPaper.Ideal.PpIInteger
import AJPaper.Ideal.PpIComplex
import AJPaper.Ideal.PpIPoint
import AJPaper.Ideal.PpISeparate

/-!
# Section 8.5: the ideal formulations fail for the four families (Unit PpI, node `PpI_Main`)

Source: Section 8.5 of the paper (`conclusion.tex`, "The invariant recurrence ideal"): "The same
extra curve separates the radical ideals in Sikora's `sl₂` formulation [Conj. 9] and the
`t = -1` formulation in [Tran, Sec. 1.2, Conj. 2]."

`PpiIdealClauses K G` collects, for a knot `K` and its obstruction factor `G`:

1. `G` divides `Q(-1, M, L)` in `ℤ[M][L]` for every `Q` in the localized annihilator of the
   coloured Jones function, primitive or not (in particular for every polynomial operator
   annihilating it at all integers);
2. for every element `P` of the recurrence ideal of the quantum torus over `ℂ[t^{±1}]` (a raw
   Laurent-polynomial annihilator with complex coefficients), `ε(P)` vanishes at every point
   `(M, L)`, `M, L ≠ 0`, of `G = 0`;
3. there is a point `p` of `G = 0` with nonzero coordinates such that neither `p` nor its image
   under `(M, L) ↦ (M⁻¹, L⁻¹)` lies in the Zariski closure of the eigenvalue set of `K`;
4. Tran's Conjecture 2 (`PpiTranConjecture`) fails for `K`;
5. Sikora's Conjecture 9 for `sl₂`, `G = SL(2, ℂ)` (`PpiSikoraConjecture`) fails for `K`.

`theoremIdealFormulations`: the clauses hold for all four families, with `G = E` for the
negative clasp and `G = E^∨` for the positive clasp. `release_idealFormulations` is the same
statement for every closed braid with the strands and the word of the family.

The formal predicates interpret the two sources at the points listed in
`AJPaper.Ideal.PpIConjectures`. This file has no `sorry` of its own.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The clauses of Section 8.5 for one knot `K` with obstruction factor `G`. -/
def PpiIdealClauses (K : BraidKnot) (G : ℤ[X][X]) : Prop :=
  (∀ Q : RecOp, InLocalizedAnnihilator (coloredJones K) Q → G ∣ specialize Q) ∧
    (∀ P : PpiOp ℂ, PpiAnnihilates P K → ∀ p : ℂ × ℂ, p.1 ≠ 0 → p.2 ≠ 0 →
      evalPoint (mapC G) p = 0 → ppiEval p (ppiEps P) = 0) ∧
    (∃ p : ℂ × ℂ, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ evalPoint (mapC G) p = 0 ∧
      p ∉ zariskiClosure (eigenvalueSet K) ∧
      (p.1⁻¹, p.2⁻¹) ∉ zariskiClosure (eigenvalueSet K)) ∧
    ¬ PpiTranConjecture K ∧ ¬ PpiSikoraConjecture K

/-- **Section 8.5 (the ideal formulations).** For coprime `2 ≤ r < s`, both clasp signs, both
companions and every twist, the satellite `W_(ε,ℓ)(T_η)` satisfies `PpiIdealClauses` with the
factor `E` (negative clasp), respectively `E^∨` (positive clasp): every raw annihilator
specializes to a function vanishing on the extra curve, a point of the extra curve lies outside
the closure of the classical eigenvalue image, and the `t = -1` ideal formulation and Sikora's
`sl₂` formulation of the AJ conjecture both fail. -/
theorem theoremIdealFormulations {r s : ℕ} (h : IsTorusPair r s) (σ η : Bool) (ℓ : ℤ) :
    PpiIdealClauses (twFamilyKnot r s h σ η ℓ) (twFamilyFactor σ) := by
  have hvan : ∀ P : PpiOp ℂ, PpiAnnihilates P (twFamilyKnot r s h σ η ℓ) → ∀ p : ℂ × ℂ,
      p.1 ≠ 0 → p.2 ≠ 0 → evalPoint (mapC (twFamilyFactor σ)) p = 0 →
        ppiEval p (ppiEps P) = 0 := fun P hP p h1 h2 hp ↦
    ppi_eval_eps_eq_zero (ppi_factor_dvd_specialize_of_annihilates h σ η ℓ) hP h1 h2 hp
  obtain ⟨p, h1, h2, hG, hp, hp'⟩ := ppi_exists_point h σ η ℓ
  exact ⟨ppi_factor_dvd_specialize h σ η ℓ, hvan, ⟨p, h1, h2, hG, hp, hp'⟩,
    not_ppiTranConjecture_of_point h1 h2 hp fun P hP ↦ hvan P hP p h1 h2 hG,
    not_ppiSikoraConjecture_of_point h1 h2 hp fun P hP ↦ hvan P hP p h1 h2 hG⟩

/-- **Section 8.5 in braid-word form**: every closed braid with `twFamilyStrands r s η ℓ`
strands and the word `twFamilyWord r s σ η ℓ` satisfies `PpiIdealClauses` with the factor `E`
for the negative clasp (`σ = true`) and `E^∨` for the positive clasp. -/
theorem release_idealFormulations :
    (∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ) (K : BraidKnot),
      K.strands = twFamilyStrands r s η ℓ → K.word = twFamilyWord r s true η ℓ →
        PpiIdealClauses K extraFactor) ∧
    ∀ r s : ℕ, IsTorusPair r s → ∀ (η : Bool) (ℓ : ℤ) (K : BraidKnot),
      K.strands = twFamilyStrands r s η ℓ → K.word = twFamilyWord r s false η ℓ →
        PpiIdealClauses K extraFactorMirror := by
  refine ⟨fun r s h η ℓ K hs hw ↦ ?_, fun r s h η ℓ K hs hw ↦ ?_⟩
  · rw [eq_twFamilyKnot_of_word h true η ℓ hs hw]
    exact theoremIdealFormulations h true η ℓ
  · rw [eq_twFamilyKnot_of_word h false η ℓ hs hw]
    exact theoremIdealFormulations h false η ℓ

end AJConjecture
