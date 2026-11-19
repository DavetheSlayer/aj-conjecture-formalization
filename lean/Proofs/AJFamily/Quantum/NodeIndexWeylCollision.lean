import Mathlib
import AJConjecture.QAlgNodeContentEnds
import AJConjecture.QAlgNodeContentPseudoFactor
import AJConjecture.QAlgNodeIndexArith
import AJConjecture.QAlgNodeIndexEquation
import AJConjecture.QAlgNodeIndexEval
import AJConjecture.QAlgSyzygyResidue
import AJFamily.Quantum.NodeFibreSeparatingCollision

/-!
# The node index divisibility, with collisions

For a separating factorisation `β P = S ⋆ R` (`G ∣ R₀`, `D ∣ S₀`) at a collision-free simple
transversal node, a power of `M - m₀` divides a combination of the node numerator and denominator
of `R` and the Weyl subprincipal symbol of `P` at the node.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

theorem pow_dvd_nodeNumer_of_separating_collision {P : RecOp} {G D T : ℤ[X][X]} {κ₁ κ₂ : ℤ[X]}
    (hsym : C κ₁ * specialize P = C κ₂ * (G * D * T)) {m₀ l₀ : ℂ} (hl₀ : l₀ ≠ 0)
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
    {β : Coeff} (hβ : β.map (Polynomial.evalRingHom (-1)) ≠ 0) {S R : RecOp}
    (h : C β * P = oreMul coeffShift S R)
    (hGR : toComparison G ∣ toComparison (specialize R))
    (hDS : toComparison D ∣ toComparison (specialize S)) :
    (X - C m₀) ^ (((nodeDenom R).map (Int.castRingHom ℂ)).rootMultiplicity m₀ + 1) ∣
      C (l₀ *
            (evalIntPoint (derivative G) m₀ l₀ * evalIntPoint (coeffDerivative D) m₀ l₀ -
              evalIntPoint (coeffDerivative G) m₀ l₀ * evalIntPoint (derivative D) m₀ l₀) *
            evalIntPoint T m₀ l₀ * (κ₂.map (Int.castRingHom ℂ)).eval m₀) *
          ((X - C m₀) * (nodeNumer R).map (Int.castRingHom ℂ) -
            C m₀ * (nodeDenom R).map (Int.castRingHom ℂ)) +
        C (evalIntPoint (weylSymbol P) m₀ l₀ * (κ₁.map (Int.castRingHom ℂ)).eval m₀) *
          (nodeDenom R).map (Int.castRingHom ℂ) := by
  have hP0 : evalIntPoint (specialize P) m₀ 0 ≠ 0 := by
    rw [evalIntPoint, evalPoint, eval₂_at_zero, coeff_map]
    exact hconst
  -- 1. contents
  obtain ⟨a, b, βs, Ss, Rs, hR, hS, hβ0, hβs, hfac⟩ :=
    exists_nodeContent_of_pseudoFactor (m₀ := m₀) hβ h hlead
  -- 2. the fibre at the node
  obtain ⟨Rc, hRc, hSroot, hcop, hJs⟩ :=
    exists_nodeFibre_of_separating_collision hsym hl₀ hκ₁ hκ₂ hP0 hG hD hT hGL hDL hcoll hGR hDS
      hR hS hβs hfac
  have hRroot : (Rs.map (Polynomial.evalRingHom m₀)).eval l₀ = 0 := by
    rw [hRc, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
  have hJne : (derivative (Rs.map (Polynomial.evalRingHom m₀))).eval l₀ *
        ((innerDerivative Ss).map (Polynomial.evalRingHom m₀)).eval l₀ -
      (derivative (Ss.map (Polynomial.evalRingHom m₀))).eval l₀ *
        ((innerDerivative Rs).map (Polynomial.evalRingHom m₀)).eval l₀ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hJs
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hβs hκ₂) hT) hJac hJs.symm
  -- 3. end coefficients
  obtain ⟨hn, hd, hdegR, hlc, hss, hrs, hr0s, hΔ⟩ :=
    nodeContent_ends hβ h hdeg hlead hconst hR hS hβs hfac hRroot
  -- 4. the divided first-jet equation
  obtain ⟨U, hU⟩ := exists_nodeSyzygy_of_content h hn hR hS hβ0
  have hY : (C ((X - C m₀) ^ (2 * b) * Ss.coeff S.natDegree) *
        (jetNumer R).map (Polynomial.mapRingHom (Int.castRingHom ℂ))).natDegree <
      (Rs.map (Polynomial.evalRingHom m₀)).natDegree := by
    rw [hdegR]
    exact (natDegree_C_mul_le _ _).trans_lt
      (natDegree_map_le.trans_lt (natDegree_jetNumer_lt hd))
  -- 5. the abstract residue theorem
  obtain ⟨y, hy, hres⟩ :=
    exists_mul_eq_pow_mul_of_syzygy (2 * a + 2 * b) hU hY hRc hSroot hcop hJne
  have hY0 : (C ((X - C m₀) ^ (2 * b) * Ss.coeff S.natDegree) *
        (jetNumer R).map (Polynomial.mapRingHom (Int.castRingHom ℂ))).coeff 0 =
      (X - C m₀) ^ (2 * b) * Ss.coeff S.natDegree * (nodeNumer R).map (Int.castRingHom ℂ) := by
    rw [coeff_C_mul, coeff_map, coeff_zero_jetNumer, coe_mapRingHom]
  rw [hY0] at hy
  have hy' : (X - C m₀) * (Ss.coeff S.natDegree * (nodeNumer R).map (Int.castRingHom ℂ)) =
      (X - C m₀) ^ (2 * a) * y := by
    apply mul_left_cancel₀ (pow_ne_zero (2 * b) (X_sub_C_ne_zero m₀))
    linear_combination hy
  have hR0 : (Rs.map (Polynomial.evalRingHom m₀)).coeff 0 = (Rs.coeff 0).eval m₀ := by
    rw [coeff_map, coe_evalRingHom]
  rw [hR0] at hres
  -- 6. the last evaluation and the residue identity
  have hN := eval_nodeRemainder_of_content (P := P) (m₀ := m₀) (l₀ := l₀) hβs hfac hlc hRroot
    hSroot
  have key : ∀ yv Nb r0 rsv ssv PW J Jac Tv k1 k2 bs : ℂ, yv * (l₀ * J) = -(Nb * r0) →
      Nb = ssv * rsv * (bs * PW - l₀ * m₀ * J) → k1 * J = bs * k2 * Tv * Jac → l₀ * J ≠ 0 →
      l₀ * Jac * Tv * k2 * yv + (PW * k1 - l₀ * Jac * Tv * k2 * m₀) * (r0 * rsv * ssv) = 0 := by
    intro yv Nb r0 rsv ssv PW J Jac Tv k1 k2 bs h1 h2 h3 h4
    apply mul_left_cancel₀ h4
    linear_combination (l₀ * Jac * Tv * k2) * h1 - (l₀ * Jac * Tv * k2) * r0 * h2 +
      r0 * rsv * ssv * PW * l₀ * h3
  exact pow_dvd_of_residue_identity hΔ hss hr0s hrs hy'
    (key _ _ _ _ _ _ _ _ _ _ _ _ hres hN hJs (mul_ne_zero hl₀ hJne))

end AJConjecture
