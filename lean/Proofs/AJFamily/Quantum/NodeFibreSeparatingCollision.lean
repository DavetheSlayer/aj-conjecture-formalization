import Mathlib
import AJConjecture.QAlgNodeFibreCrossing
import AJConjecture.QAlgNodeFibreTangent
import AJFamily.Quantum.NodeCollision
import AJFamily.Quantum.NodeFibreCollision

/-!
# The node fibre of a separating factorisation, with collisions

The fibre `M = m₀` of a separating factorisation at a simple transversal node satisfying
`NodeCollisionFree`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The value at a complex point of `∂p/∂L` is the value of the derivative of the fibre. -/
private theorem evalIntPoint_derivative_fibre_sepCollision (p : ℤ[X][X]) (m l : ℂ) :
    evalIntPoint (derivative p) m l =
      (derivative ((p.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map
        (Polynomial.evalRingHom m))).eval l := by
  rw [evalIntPoint_eq_eval, derivative_map, derivative_map]

/-- If `G ∣ F` in the comparison ring and `F = μ^a F*` over `ℂ`, then at a fibre where `G` does
not vanish identically, the fibre of `G` divides `L^n` times the fibre of `F*`. -/
private theorem exists_fibre_dvd_X_pow_mul_sepCollision {G F : ℤ[X][X]} {m₀ : ℂ}
    (hdvd : toComparison G ∣ toComparison F)
    (hG : (G.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map (Polynomial.evalRingHom m₀) ≠ 0)
    {a : ℕ} {Fs : ℂ[X][X]}
    (hF : F.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) = C ((X - C m₀) ^ a) * Fs) :
    ∃ n : ℕ, (G.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map (Polynomial.evalRingHom m₀) ∣
      X ^ n * Fs.map (Polynomial.evalRingHom m₀) := by
  obtain ⟨u, n, Q, hu, hQ⟩ := exists_local_dvd_of_toComparison_dvd hdvd hG hF
  have hmap := congrArg (Polynomial.map (Polynomial.evalRingHom m₀)) hQ
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    coe_evalRingHom] at hmap
  refine ⟨n, C (u.eval m₀)⁻¹ * Q.map (Polynomial.evalRingHom m₀), ?_⟩
  rw [mul_left_comm, ← hmap, ← mul_assoc, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hu, C_1, one_mul]

/-- At a simple transversal node of `G` and `D` satisfying the collision hypothesis, the
primitive parts `R*`, `S*` with `β* P₀ = S* R*` cross simply: `l₀` is a simple root of the fibre
of `R*` with cofactor coprime to the fibre of `S*`, and the Jacobians are related by
`κ₁ J* = β* κ₂ T Jac`. -/
theorem exists_nodeFibre_of_separating_collision {P₀ R₀ S₀ G D T : ℤ[X][X]} {κ₁ κ₂ : ℤ[X]}
    (hsym : C κ₁ * P₀ = C κ₂ * (G * D * T)) {m₀ l₀ : ℂ} (hl₀ : l₀ ≠ 0)
    (hκ₁ : (κ₁.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hκ₂ : (κ₂.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hP0 : evalIntPoint P₀ m₀ 0 ≠ 0)
    (hG : evalIntPoint G m₀ l₀ = 0) (hD : evalIntPoint D m₀ l₀ = 0)
    (hT : evalIntPoint T m₀ l₀ ≠ 0)
    (hGL : evalIntPoint (derivative G) m₀ l₀ ≠ 0)
    (hDL : evalIntPoint (derivative D) m₀ l₀ ≠ 0)
    (hcoll : NodeCollisionFree G D T m₀ l₀)
    (hGR : toComparison G ∣ toComparison R₀) (hDS : toComparison D ∣ toComparison S₀)
    {a b : ℕ} {βs : ℂ[X]} {Ss Rs : ℂ[X][X]}
    (hR : R₀.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) = C ((X - C m₀) ^ a) * Rs)
    (hS : S₀.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) = C ((X - C m₀) ^ b) * Ss)
    (hβs : βs.eval m₀ ≠ 0)
    (hfac : C βs * P₀.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) = Ss * Rs) :
    ∃ Rc : ℂ[X], Rs.map (Polynomial.evalRingHom m₀) = (X - C l₀) * Rc ∧
      (Ss.map (Polynomial.evalRingHom m₀)).eval l₀ = 0 ∧
      IsCoprime Rc (Ss.map (Polynomial.evalRingHom m₀)) ∧
      (κ₁.map (Int.castRingHom ℂ)).eval m₀ *
          ((derivative (Rs.map (Polynomial.evalRingHom m₀))).eval l₀ *
              ((innerDerivative Ss).map (Polynomial.evalRingHom m₀)).eval l₀ -
            (derivative (Ss.map (Polynomial.evalRingHom m₀))).eval l₀ *
              ((innerDerivative Rs).map (Polynomial.evalRingHom m₀)).eval l₀) =
        βs.eval m₀ * (κ₂.map (Int.castRingHom ℂ)).eval m₀ * evalIntPoint T m₀ l₀ *
          (evalIntPoint (derivative G) m₀ l₀ * evalIntPoint (coeffDerivative D) m₀ l₀ -
            evalIntPoint (coeffDerivative G) m₀ l₀ * evalIntPoint (derivative D) m₀ l₀) := by
  obtain ⟨hgd, htc⟩ := hcoll
  obtain ⟨lR, hR0, hRL, hRM⟩ := exists_tangent_of_toComparison_dvd hl₀ hG hGL hGR hR
  obtain ⟨lS, hS0, hSL, hSM⟩ := exists_tangent_of_toComparison_dvd hl₀ hD hDL hDS hS
  have hfacfib : C (βs.eval m₀) *
      (P₀.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map (Polynomial.evalRingHom m₀) =
        Ss.map (Polynomial.evalRingHom m₀) * Rs.map (Polynomial.evalRingHom m₀) := by
    have hmap := congrArg (Polynomial.map (Polynomial.evalRingHom m₀)) hfac
    rwa [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, coe_evalRingHom] at hmap
  have hsymfib := congrArg (fun p : ℤ[X][X] ↦
    (p.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map (Polynomial.evalRingHom m₀)) hsym
  simp only [Polynomial.map_mul, Polynomial.map_C, coe_mapRingHom, coe_evalRingHom] at hsymfib
  have hmain : C ((κ₁.map (Int.castRingHom ℂ)).eval m₀) *
        (Ss.map (Polynomial.evalRingHom m₀) * Rs.map (Polynomial.evalRingHom m₀)) =
      C (βs.eval m₀ * (κ₂.map (Int.castRingHom ℂ)).eval m₀) *
        ((G.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map (Polynomial.evalRingHom m₀) *
          (D.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map (Polynomial.evalRingHom m₀) *
          (T.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map
            (Polynomial.evalRingHom m₀)) := by
    rw [← hfacfib, C_mul]
    linear_combination C (βs.eval m₀) * hsymfib
  have hc1 : C ((κ₁.map (Int.castRingHom ℂ)).eval m₀)⁻¹ *
      C ((κ₁.map (Int.castRingHom ℂ)).eval m₀) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hκ₁, C_1]
  have hC : C (((κ₁.map (Int.castRingHom ℂ)).eval m₀)⁻¹ *
      (βs.eval m₀ * (κ₂.map (Int.castRingHom ℂ)).eval m₀)) *
      ((G.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map (Polynomial.evalRingHom m₀) *
        (D.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map (Polynomial.evalRingHom m₀) *
        (T.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map (Polynomial.evalRingHom m₀)) =
      Ss.map (Polynomial.evalRingHom m₀) * Rs.map (Polynomial.evalRingHom m₀) := by
    rw [C_mul (a := ((κ₁.map (Int.castRingHom ℂ)).eval m₀)⁻¹)]
    linear_combination C ((κ₁.map (Int.castRingHom ℂ)).eval m₀)⁻¹ * hmain.symm +
      (Ss.map (Polynomial.evalRingHom m₀) * Rs.map (Polynomial.evalRingHom m₀)) * hc1
  have h0 : ((G.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map (Polynomial.evalRingHom m₀) *
      (D.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map (Polynomial.evalRingHom m₀) *
      (T.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map (Polynomial.evalRingHom m₀)).eval 0
        ≠ 0 := by
    intro hz
    have hev := congrArg (eval 0) hsymfib
    simp only [eval_mul, eval_C] at hev hz
    rw [hz, mul_zero, ← evalIntPoint_eq_eval] at hev
    exact mul_ne_zero hκ₁ hP0 hev
  have hGne : (G.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map
      (Polynomial.evalRingHom m₀) ≠ 0 := fun h ↦ hGL (by
    rw [evalIntPoint_derivative_fibre_sepCollision, h, derivative_zero, eval_zero])
  have hDne : (D.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map
      (Polynomial.evalRingHom m₀) ≠ 0 := fun h ↦ hDL (by
    rw [evalIntPoint_derivative_fibre_sepCollision, h, derivative_zero, eval_zero])
  have hc : ((κ₁.map (Int.castRingHom ℂ)).eval m₀)⁻¹ *
      (βs.eval m₀ * (κ₂.map (Int.castRingHom ℂ)).eval m₀) ≠ 0 :=
    mul_ne_zero (inv_ne_zero hκ₁) (mul_ne_zero hβs hκ₂)
  have hG' := hG
  have hD' := hD
  have hT' := hT
  have hGL' := hGL
  have hDL' := hDL
  simp only [evalIntPoint_derivative_fibre_sepCollision] at hGL' hDL' htc
  simp only [evalIntPoint_eq_eval] at hG' hD' hT' hgd htc
  obtain ⟨Rc, hRc, hcop⟩ := exists_eq_mul_isCoprime_of_collision hc hC h0
    (exists_fibre_dvd_X_pow_mul_sepCollision hGR hGne hR)
    (exists_fibre_dvd_X_pow_mul_sepCollision hDS hDne hS) hG' hD' hGL' hDL' hT' hgd htc
  have hprod := eval_derivative_mul_eq_of_mul_eq hmain hR0 hS0 hG' hD'
  rw [← evalIntPoint_derivative_fibre_sepCollision, ← evalIntPoint_derivative_fibre_sepCollision,
    ← evalIntPoint_eq_eval, hSL, hRL] at hprod
  have hkey : (κ₁.map (Int.castRingHom ℂ)).eval m₀ * (lR * lS) =
      βs.eval m₀ * (κ₂.map (Int.castRingHom ℂ)).eval m₀ * evalIntPoint T m₀ l₀ := by
    apply mul_right_cancel₀ (mul_ne_zero hGL hDL)
    linear_combination hprod
  refine ⟨Rc, hRc, hS0, hcop, ?_⟩
  rw [hRL, hSM, hSL, hRM]
  linear_combination (evalIntPoint (derivative G) m₀ l₀ * evalIntPoint (coeffDerivative D) m₀ l₀ -
    evalIntPoint (coeffDerivative G) m₀ l₀ * evalIntPoint (derivative D) m₀ l₀) * hkey

end AJConjecture
