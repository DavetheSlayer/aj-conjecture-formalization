import Mathlib
import AJConjecture.QAlgNodeDenomNeZero
import AJConjecture.QAlgNodeIndexIntegral
import AJConjecture.QAlgPseudoFactorNormalize
import AJConjecture.QAlgToComparisonUnit
import AJFamily.Quantum.NodeIndexWeylCollision

/-!
# The index criterion at a collision-free node

The index criterion `toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision` at a node
satisfying `NodeCollisionFree`; it is applied at the two nodes of the family operator.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- At a simple transversal collision-free node of `G` and `D` where the Weyl subprincipal symbol
vanishes, there is no factorisation `β P = S ⋆ R` with `β(-1, M) ≠ 0`, `G ∣ R₀` and `D ∣ S₀`. -/
private theorem not_separating_of_weylSymbol_eq_zero_collision {P : RecOp} {G D T : ℤ[X][X]} {κ₁ κ₂ : ℤ[X]}
    (hsym : C κ₁ * specialize P = C κ₂ * (G * D * T)) {m₀ l₀ : ℂ} (hm₀ : m₀ ≠ 0)
    (hl₀ : l₀ ≠ 0) (hκ₁ : (κ₁.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hκ₂ : (κ₂.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hdeg : (specialize P).natDegree = P.natDegree)
    (hlead : ((specialize P).leadingCoeff.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hconst : (((specialize P).coeff 0).map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hG : evalIntPoint G m₀ l₀ = 0) (hD : evalIntPoint D m₀ l₀ = 0)
    (hT : evalIntPoint T m₀ l₀ ≠ 0)
    (hGL : evalIntPoint (derivative G) m₀ l₀ ≠ 0)
    (hDL : evalIntPoint (derivative D) m₀ l₀ ≠ 0)
    (hJac : evalIntPoint (derivative G) m₀ l₀ * evalIntPoint (coeffDerivative D) m₀ l₀ -
      evalIntPoint (coeffDerivative G) m₀ l₀ * evalIntPoint (derivative D) m₀ l₀ ≠ 0)
    (hcoll : NodeCollisionFree G D T m₀ l₀)
    (hW : evalIntPoint (weylSymbol P) m₀ l₀ = 0) {β : Coeff}
    (hβ : β.map (Polynomial.evalRingHom (-1)) ≠ 0) {S R : RecOp}
    (h : C β * P = oreMul coeffShift S R)
    (hGR : toComparison G ∣ toComparison (specialize R))
    (hDS : toComparison D ∣ toComparison (specialize S)) : False := by
  have hconst0 : (specialize P).coeff 0 ≠ 0 := fun h0 ↦
    hconst (by rw [h0, Polynomial.map_zero, eval_zero])
  have hΔ0 : nodeDenom R ≠ 0 := nodeDenom_ne_zero_of_pseudoFactor hβ h hdeg hconst0
  have hΔ : (nodeDenom R).map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.castRingHom ℂ).injective_int).mpr hΔ0
  have hβ0 : β ≠ 0 := fun h0 ↦ hβ (by rw [h0, Polynomial.map_zero])
  have hlead' : (complexSpec (coeffToComplex P.leadingCoeff)).eval m₀ ≠ 0 := by
    rw [complexSpec_coeffToComplex, Polynomial.leadingCoeff, ← coeff_specialize, ← hdeg]
    exact hlead
  have hconst' : (complexSpec (coeffToComplex (P.coeff 0))).eval m₀ ≠ 0 := by
    rw [complexSpec_coeffToComplex, ← coeff_specialize]
    exact hconst
  obtain ⟨j, hj⟩ := exists_nat_pow_dvd_nodeNumer_of_pseudoFactor hβ0 h hlead' hconst'
  have hsep := pow_dvd_nodeNumer_of_separating_collision hsym hl₀ hκ₁ hκ₂ hdeg hlead hconst hG hD hT hGL
    hDL hJac hcoll hβ h hGR hDS
  rw [hW, zero_mul, C_0, zero_mul, add_zero] at hsep
  have hc : l₀ *
      (evalIntPoint (derivative G) m₀ l₀ * evalIntPoint (coeffDerivative D) m₀ l₀ -
        evalIntPoint (coeffDerivative G) m₀ l₀ * evalIntPoint (derivative D) m₀ l₀) *
      evalIntPoint T m₀ l₀ * (κ₂.map (Int.castRingHom ℂ)).eval m₀ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hl₀ hJac) hT) hκ₂
  rw [(isUnit_C.mpr (IsUnit.mk0 _ hc)).dvd_mul_left] at hsep
  have hj0 : (2 * (j : ℂ) + 1) * m₀ ≠ 0 := by
    refine mul_ne_zero ?_ hm₀
    exact_mod_cast Nat.succ_ne_zero (2 * j)
  have hdiff := dvd_sub hj hsep
  have hrw : (X - C m₀) * (nodeNumer R).map (Int.castRingHom ℂ) +
        C (2 * (j : ℂ) * m₀) * (nodeDenom R).map (Int.castRingHom ℂ) -
      ((X - C m₀) * (nodeNumer R).map (Int.castRingHom ℂ) -
        C m₀ * (nodeDenom R).map (Int.castRingHom ℂ)) =
      C ((2 * (j : ℂ) + 1) * m₀) * (nodeDenom R).map (Int.castRingHom ℂ) := by
    simp only [C_mul, C_add, C_1]
    ring
  rw [hrw, (isUnit_C.mpr (IsUnit.mk0 _ hj0)).dvd_mul_left] at hdiff
  exact absurd ((le_rootMultiplicity_iff hΔ).mpr hdiff) (Nat.not_succ_le_self _)

/-- The index criterion at a collision-free node: if the Weyl subprincipal symbol of `P`
vanishes at a simple transversal node of factors `G`, `D` of its symbol, every right
pseudo-factor of `P` with symbol divisible by `G` has symbol divisible by `D`. -/
theorem toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision {P : RecOp} {G D T : ℤ[X][X]}
    {κ₁ κ₂ : ℤ[X]} (hsym : C κ₁ * specialize P = C κ₂ * (G * D * T))
    (hprime : Prime (toComparison D)) {m₀ l₀ : ℂ} (hm₀ : m₀ ≠ 0) (hl₀ : l₀ ≠ 0)
    (hκ₁ : (κ₁.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hκ₂ : (κ₂.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hdeg : (specialize P).natDegree = P.natDegree)
    (hlead : ((specialize P).leadingCoeff.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hconst : (((specialize P).coeff 0).map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hG : evalIntPoint G m₀ l₀ = 0) (hD : evalIntPoint D m₀ l₀ = 0)
    (hT : evalIntPoint T m₀ l₀ ≠ 0)
    (hGL : evalIntPoint (derivative G) m₀ l₀ ≠ 0)
    (hDL : evalIntPoint (derivative D) m₀ l₀ ≠ 0)
    (hJac : evalIntPoint (derivative G) m₀ l₀ * evalIntPoint (coeffDerivative D) m₀ l₀ -
      evalIntPoint (coeffDerivative G) m₀ l₀ * evalIntPoint (derivative D) m₀ l₀ ≠ 0)
    (hcoll : NodeCollisionFree G D T m₀ l₀)
    (hW : evalIntPoint (weylSymbol P) m₀ l₀ = 0) {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * P = oreMul coeffShift S R)
    (hGR : toComparison G ∣ toComparison (specialize R)) :
    toComparison D ∣ toComparison (specialize R) := by
  by_contra hnd
  have hP0 : specialize P ≠ 0 := by
    intro h0
    apply hlead
    rw [h0, leadingCoeff_zero, Polynomial.map_zero, eval_zero]
  obtain ⟨β', S', R', hβ', -, -, -, -, h', a, ha⟩ := exists_normalized_pseudoFactor hP0 hβ h
  have hspecC : ∀ c : Coeff, specialize (C c) = C (c.map (Polynomial.evalRingHom (-1))) := by
    intro c
    rw [specialize, coe_mapRingHom, Polynomial.map_C, coe_mapRingHom]
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  swap
  · apply hnd
    have h0 : specialize R = 0 := by
      rw [ha, map_mul, hspecC, Polynomial.map_C, coe_evalRingHom, eval_pow, eval_add, eval_X,
        eval_one, neg_add_cancel, zero_pow ha0.ne', map_zero, map_zero, zero_mul]
    rw [h0, map_zero]
    exact dvd_zero _
  rw [ha0, pow_zero, map_one, map_one, one_mul] at ha
  subst ha
  have hκ₁0 : κ₁ ≠ 0 := by
    rintro rfl
    exact hκ₁ (by rw [Polynomial.map_zero, eval_zero])
  have hprod : toComparison (C κ₁) *
      (toComparison (specialize S') * toComparison (specialize R)) =
      toComparison D *
        toComparison (C (β'.map (Polynomial.evalRingHom (-1)) * κ₂) * (G * T)) := by
    have h1 : specialize S' * specialize R =
        C (β'.map (Polynomial.evalRingHom (-1))) * specialize P := by
      rw [← specialize_oreMul, ← h', map_mul, hspecC]
    have h2 : C κ₁ * (C (β'.map (Polynomial.evalRingHom (-1))) * specialize P) =
        D * (C (β'.map (Polynomial.evalRingHom (-1)) * κ₂) * (G * T)) := by
      rw [mul_left_comm, hsym, C_mul]
      ring
    rw [← map_mul toComparison, ← map_mul toComparison, ← map_mul toComparison, h1, h2]
  rcases hprime.dvd_or_dvd ⟨_, hprod⟩ with h1 | h1
  · exact hprime.not_isUnit (isUnit_of_dvd_unit h1 (isUnit_toComparison_coeff_of_ne_zero hκ₁0))
  rcases hprime.dvd_or_dvd h1 with h2 | h2
  · exact not_separating_of_weylSymbol_eq_zero_collision hsym hm₀ hl₀ hκ₁ hκ₂ hdeg hlead hconst hG hD hT
      hGL hDL hJac hcoll hW hβ' h' hGR h2
  · exact hnd h2

end AJConjecture
