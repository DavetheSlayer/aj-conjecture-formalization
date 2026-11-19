import Mathlib
import AJHandoff.LocalTheory.LocNormalize

/-!
# I-PART: factorizations partition the residual blocks, with degrees retained (Lemma 2)

Let `P ∈ ℂ[[h]][z][u]` have residual symbol `P₀` of full degree (`v_h` of the leading
coefficient is `0`, the "monic" normalization) with nonzero constant coefficient, square-free
over `ℂ(z)`. For a normalized pseudo-factorization `β P = S ⋆ R` (`β₀ ≠ 0`), the residual symbols
satisfy `S₀ R₀ = β₀ P₀`, keep the degrees of `S` and `R`, keep nonzero constant coefficients
(no endpoint is lost), and are coprime over `ℂ(z)`. So the irreducible factors of `P₀` over
`ℂ(z)` are partitioned between `R₀` and `S₀`, both parts nonempty when `0 < deg R < deg P`.
A general pseudo-factorization is first normalized by `exists_normalized_locPseudoFactor`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **Lemma 2 (I-PART).** -/
theorem locResidual_partition (δ : LocDilation) {P S R : LocOp} {β : LocPoly}
    (hβ : locJet0 β ≠ 0) (h : C β * P = oreMul δ.shiftHom S R)
    (hdeg : (opJet0 P).natDegree = P.natDegree) (hconst : (opJet0 P).coeff 0 ≠ 0)
    (hsqf : Squarefree ((opJet0 P).map (algebraMap ℂ[X] (RatFunc ℂ)))) :
    opJet0 S * opJet0 R = C (locJet0 β) * opJet0 P ∧
      (opJet0 R).natDegree = R.natDegree ∧ (opJet0 S).natDegree = S.natDegree ∧
      (opJet0 R).coeff 0 ≠ 0 ∧ (opJet0 S).coeff 0 ≠ 0 ∧
      IsCoprime ((opJet0 S).map (algebraMap ℂ[X] (RatFunc ℂ)))
        ((opJet0 R).map (algebraMap ℂ[X] (RatFunc ℂ))) := by
  have hprod : opJet0 S * opJet0 R = C (locJet0 β) * opJet0 P := by
    rw [← opJet0_oreMul δ, ← h, opJet0, Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hP0 : opJet0 P ≠ 0 := fun h0 ↦ hconst (by rw [h0, coeff_zero])
  have hβP : C (locJet0 β) * opJet0 P ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hβ) hP0
  have hS0 : opJet0 S ≠ 0 := fun h0 ↦ hβP (by rw [← hprod, h0, zero_mul])
  have hR0 : opJet0 R ≠ 0 := fun h0 ↦ hβP (by rw [← hprod, h0, mul_zero])
  have hSd : (opJet0 S).natDegree ≤ S.natDegree := Polynomial.natDegree_map_le
  have hRd : (opJet0 R).natDegree ≤ R.natDegree := Polynomial.natDegree_map_le
  have hS : S ≠ 0 := by rintro rfl; exact hS0 (by rw [opJet0, Polynomial.map_zero])
  have hR : R ≠ 0 := by rintro rfl; exact hR0 (by rw [opJet0, Polynomial.map_zero])
  have hsum : S.natDegree + R.natDegree = (opJet0 S).natDegree + (opJet0 R).natDegree := by
    have hβ0 : β ≠ 0 := by rintro rfl; exact hβ (map_zero _)
    rw [← natDegree_oreMul (σ := δ.shiftHom) δ.shift.injective hS hR, ← h,
      ← Polynomial.natDegree_mul hS0 hR0, hprod, Polynomial.natDegree_C_mul hβ, Polynomial.natDegree_C_mul hβ0, hdeg]
  have hcoeff : (opJet0 S).coeff 0 * (opJet0 R).coeff 0 ≠ 0 := by
    rw [← Polynomial.mul_coeff_zero, hprod, Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero]
    exact mul_ne_zero hβ hconst
  refine ⟨hprod, by omega, by omega, right_ne_zero_of_mul hcoeff, left_ne_zero_of_mul hcoeff, ?_⟩
  have hβK : algebraMap ℂ[X] (RatFunc ℂ) (locJet0 β) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).mpr hβ
  have hsq : Squarefree ((opJet0 S).map (algebraMap ℂ[X] (RatFunc ℂ)) *
      (opJet0 R).map (algebraMap ℂ[X] (RatFunc ℂ))) := by
    rw [← Polynomial.map_mul, hprod, Polynomial.map_mul, Polynomial.map_C]
    exact (associated_unit_mul_left _ _
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hβK))).symm.squarefree_iff.mp hsqf
  exact isRelPrime_iff_isCoprime.mp (IsRelPrime.of_squarefree_mul hsq)

end AJConjecture
