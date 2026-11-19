import Mathlib
import AJHandoff.LocalTheory.LocUnitCoboundary
import AJHandoff.LocalTheory.LocQuotientMinors
import AJHandoff.LocalTheory.LocCoboundaryResidue

/-!
# I-INT: integrality of the normalized determinant residue of a rational quotient (Lemma 1)

Let `V = F^d` carry the semilinear map `v ↦ A σ(v)` with `A ∈ GL_d(R₀)` (hypothesis (JL)) at
`z₀ ≠ 0`, and let `W = F^r` with `w ↦ B σ(w)` be any rational quotient: a surjective `F`-linear
`Q : V → W` with `B σ(Q) = Q A`, in any `F`-rational basis of `W`. Then `D = det B` satisfies
`v_h(D) = 0`, `D₀` is a unit at `z₀`, and `Res_{z₀} (D₁/D₀) dz/(c z) ∈ ℤ` (with at most a
simple pole).

The quotient matrix `B` need not be jointly regular, and its zeros and poles may move and
coalesce at any rate: the theorem makes no assumption on `B` beyond the intertwining relation.
The source's hypothesis `v_h(D) = 0` is a conclusion here (it holds for every quotient of a (JL)
module, since `v_h(σ(g)/g) = 0` for every `g ∈ F^×`).

Proof (replacing the source's Puiseux/meridian-DVR argument). By `span_det_mul_quotMinor_eq`
the minors of `Q` span an `R₀`-submodule `𝔟 ≠ 0` with `det B · σ(𝔟) = 𝔟`. `R₀` is a unique
factorisation domain (a localisation of `ℂ[[h]][z]`) with fraction field `F`, and `σ` restricts
to an automorphism of `R₀` (`locDilationJointShift`). So
`det B = v σ(γ)/γ` with `v ∈ R₀^×`, `γ ∈ F^×` (`exists_unit_mul_coboundary_of_span_eq_of_ne_zero`),
and `hasNormalizedIndex_int_of_coboundary` concludes.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **Lemma 1 (I-INT).** The determinant of any rational quotient of a jointly regular
difference module has `v_h = 0`, a unit reduction at `z₀`, and integral normalized index. -/
theorem exists_hasNormalizedIndex_int_of_quotient (δ : LocDilation) {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    {d r : ℕ} {A : Matrix (Fin d) (Fin d) LocField} (hA : IsJointRegular z₀ A)
    {Q : Matrix (Fin r) (Fin d) LocField} (hQ : Function.Surjective Q.mulVecLin)
    {B : Matrix (Fin r) (Fin r) LocField} (hBQ : B * Q.map δ.fieldShift = Q * A) :
    ∃ D₀ D₁ : RatFunc ℂ, HasHJet B.det D₀ D₁ ∧ IsUnitAt z₀ D₀ ∧
      ∃ n : ℤ, HasNormalizedIndex δ.c z₀ D₀ D₁ n := by
  obtain ⟨A', hA', rfl⟩ := hA
  have hspan := span_det_mul_quotMinor_eq (O := LocJointRing z₀) δ.fieldShiftHom hA' hBQ
  obtain ⟨v, γ, hγ, hvγ⟩ := exists_unit_mul_coboundary_of_span_eq_of_ne_zero
    (O := LocJointRing z₀) (F := LocField) (locDilationJointShift δ z₀) δ.fieldShiftHom
    (fun a ↦ by exact (algebraMap_jointShift δ z₀ a).symm) (quotMinor Q)
    (exists_quotMinor_ne_zero hQ) B.det hspan
  exact hasNormalizedIndex_int_of_coboundary δ hz₀ v hγ hvγ

end AJConjecture
