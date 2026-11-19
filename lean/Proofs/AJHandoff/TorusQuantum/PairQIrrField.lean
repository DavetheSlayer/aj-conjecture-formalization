import Mathlib
import AJHandoff.TorusQuantum.PairQSymbolPackage
import AJHandoff.LocalTheory.LocPseudoField

/-!
# T-IRR over the field `ℚ(t, M)`

The transfer operator `P_rs` is irreducible in the skew polynomial ring over the fraction field of
`ℤ[t][M]` (`≅ ℚ(t, M)` after clearing integers), with the shift `M ↦ t² M` extended to the field.
This is the field form of `pairQ_transferOp_irreducible` (no right pseudo-factor of intermediate
order over `ℤ[t][M]`), via `oreIrreducible_map_iff`.
-/

namespace AJConjecture

/-- The shift `M ↦ t² M`, followed by the inclusion into the fraction field, is injective. -/
theorem coeffShiftField_injective :
    Function.Injective ((algebraMap Coeff (FractionRing Coeff)).comp coeffShift) :=
  (IsFractionRing.injective Coeff (FractionRing Coeff)).comp coeffShift_injective

/-- The shift `M ↦ t² M` on the fraction field of `ℤ[t][M]`. -/
noncomputable def coeffShiftField : FractionRing Coeff →+* FractionRing Coeff :=
  IsFractionRing.lift coeffShiftField_injective

/-- T-IRR over the field: `P_rs` is irreducible in `Frac(ℤ[t][M])[L; τ]`. -/
theorem pairQ_transferOp_oreIrreducible (r s : ℕ) (h : IsTorusPair r s) :
    OreIrreducible coeffShiftField
      ((famTransferOp (r * s)).map (algebraMap Coeff (FractionRing Coeff))) := by
  obtain ⟨hdeg, hirr⟩ := pairQ_transferOp_irreducible r s h
  rw [oreIrreducible_map_iff coeffShift coeffShiftField
    (fun a ↦ IsFractionRing.lift_algebraMap coeffShiftField_injective a) (by omega)]
  intro β hβ S R hSR
  rw [hdeg]
  exact hirr hβ hSR

end AJConjecture
