import Mathlib
import AJConjecture.QAlgCoeffShiftBasic

/-!
# The coefficient field `K = ℚ(t, M)` of the sequence theorem

`K` is the fraction field of the library's coefficient ring `ℤ[t][M]`, and `τ(M) = t² M`,
`τ(t) = t` is the extension of `coeffShift` (injective). It is an automorphism of `K` (its inverse
is `M ↦ t⁻² M`); the left skew Laurent ring `K[L, L⁻¹; τ]` is a principal ideal domain. Only the
polynomial ring `K[L; τ]` is used below: an operator of positive Laurent span is a unit `L^j`
times a polynomial operator with nonzero constant coefficient.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The coefficient field `K = ℚ(t, M)`, the fraction field of `ℤ[t][M]`. -/
abbrev SeqField : Type := FractionRing Coeff

/-- The shift `τ(M) = t² M` of `K`. -/
def seqShift : SeqField →+* SeqField :=
  IsFractionRing.lift (g := (algebraMap Coeff SeqField).comp coeffShift)
    ((IsFractionRing.injective Coeff SeqField).comp coeffShift_injective)

theorem seqShift_algebraMap (c : Coeff) :
    seqShift (algebraMap Coeff SeqField c) = algebraMap Coeff SeqField (coeffShift c) := by
  unfold seqShift
  rw [IsFractionRing.lift_algebraMap, RingHom.comp_apply]

/-- The image of `ℤ[t][M]` lies in the range of `τ`. -/
private theorem algebraMap_mem_fieldRange_seqShift (c : Coeff) :
    algebraMap Coeff SeqField c ∈ seqShift.fieldRange := by
  have hC : ∀ a : ℤ[X], algebraMap Coeff SeqField (C a) ∈ seqShift.fieldRange := fun a ↦
    ⟨algebraMap Coeff SeqField (C a), by
      rw [seqShift_algebraMap]
      congr 1
      show (C a).comp (C (X ^ 2) * X : Coeff) = C a
      rw [Polynomial.C_comp]⟩
  have hX : algebraMap Coeff SeqField X ∈ seqShift.fieldRange := by
    have h1 : algebraMap Coeff SeqField (C (X ^ 2) * X) ∈ seqShift.fieldRange :=
      ⟨algebraMap Coeff SeqField X, by
        rw [seqShift_algebraMap]
        congr 1
        show (X : Coeff).comp (C (X ^ 2) * X : Coeff) = C (X ^ 2) * X
        rw [Polynomial.X_comp]⟩
    have hne : algebraMap Coeff SeqField (C (X ^ 2)) ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff, Polynomial.C_eq_zero]
      exact pow_ne_zero 2 Polynomial.X_ne_zero
    have h2 := seqShift.fieldRange.div_mem h1 (hC (X ^ 2))
    rwa [map_mul, mul_div_cancel_left₀ _ hne] at h2
  induction c using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add]; exact seqShift.fieldRange.add_mem hp hq
  | monomial n a _ =>
    rw [pow_succ, ← mul_assoc, map_mul]
    exact seqShift.fieldRange.mul_mem ‹_› hX

/-- `τ` is an automorphism of `K`. -/
theorem seqShift_bijective : Function.Bijective seqShift := by
  refine ⟨seqShift.injective, fun z ↦ ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Coeff) z
  exact seqShift.fieldRange.div_mem (algebraMap_mem_fieldRange_seqShift a)
    (algebraMap_mem_fieldRange_seqShift b)

end AJConjecture
