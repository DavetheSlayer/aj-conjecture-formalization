import Mathlib
import AJConjecture.QAlgNodeJet
import AJConjecture.QAlgOreMulDegree
import AJConjecture.QAlgSpecializeOreMul

/-!
# The end coefficients of a normalised right pseudo-factor survive at `t = -1`

Let `β P = S ⋆ R` with `β₀ = β(-1, M) ≠ 0`, `deg P₀ = deg P` and `P₀(0) ≠ 0`. Then
`β₀ P₀ = S₀ R₀` (`specialize_oreMul`) is not zero; comparing degrees
(`deg P = deg S + deg R` by `natDegree_oreMul`, `deg S₀ ≤ deg S`, `deg R₀ ≤ deg R`) gives
`deg R₀ = deg R`, so the coefficient of `R₀` in degree `deg R` is not zero; and the constant
coefficient `β₀ p₀ = s₀ r₀` gives `r₀ ≠ 0`. Hence `nodeDenom R ≠ 0`.
-/

open Polynomial

namespace AJConjecture

/-- The denominator `r_0⁰ r_d⁰` of the logarithmic first jet is not zero for a normalised right
pseudo-factor of an operator whose symbol has full degree and nonzero constant coefficient. -/
theorem nodeDenom_ne_zero_of_pseudoFactor {P S R : RecOp} {β : Coeff}
    (hβ : β.map (Polynomial.evalRingHom (-1)) ≠ 0) (h : C β * P = oreMul coeffShift S R)
    (hdeg : (specialize P).natDegree = P.natDegree) (hconst : (specialize P).coeff 0 ≠ 0) :
    nodeDenom R ≠ 0 := by
  have hspecC : specialize (C β) = C (β.map (Polynomial.evalRingHom (-1))) := by
    rw [specialize, coe_mapRingHom, Polynomial.map_C, coe_mapRingHom]
  have I1 : C (β.map (Polynomial.evalRingHom (-1))) * specialize P =
      specialize S * specialize R := by
    rw [← specialize_oreMul, ← h, map_mul, hspecC]
  have hP0 : specialize P ≠ 0 := fun h0 ↦ hconst (by rw [h0, coeff_zero])
  have hprod : specialize S * specialize R ≠ 0 := by
    rw [← I1]
    exact mul_ne_zero (C_ne_zero.mpr hβ) hP0
  have hS0 : specialize S ≠ 0 := left_ne_zero_of_mul hprod
  have hR0 : specialize R ≠ 0 := right_ne_zero_of_mul hprod
  have hS : S ≠ 0 := fun h0 ↦ hS0 (by rw [h0, map_zero])
  have hR : R ≠ 0 := fun h0 ↦ hR0 (by rw [h0, map_zero])
  have hβ' : β ≠ 0 := fun h0 ↦ hβ (by rw [h0, Polynomial.map_zero])
  have hn : P.natDegree = S.natDegree + R.natDegree := by
    rw [← natDegree_oreMul coeffShift_injective hS hR, ← h, natDegree_C_mul hβ']
  have hd1 : (specialize S * specialize R).natDegree = P.natDegree := by
    rw [← I1, natDegree_C_mul hβ, hdeg]
  rw [natDegree_mul hS0 hR0] at hd1
  have hSle : (specialize S).natDegree ≤ S.natDegree := by
    rw [specialize, coe_mapRingHom]
    exact natDegree_map_le
  have hRle : (specialize R).natDegree ≤ R.natDegree := by
    rw [specialize, coe_mapRingHom]
    exact natDegree_map_le
  have hRdeg : (specialize R).natDegree = R.natDegree := by omega
  have hlead : (specialize R).coeff R.natDegree ≠ 0 := by
    rw [← hRdeg]
    exact leadingCoeff_ne_zero.mpr hR0
  have hc := congrArg (fun q ↦ q.coeff 0) I1
  simp only [mul_coeff_zero, coeff_C_zero] at hc
  have hconstR : (specialize R).coeff 0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc
    exact mul_ne_zero hβ hconst hc
  exact mul_ne_zero hconstR hlead

end AJConjecture
