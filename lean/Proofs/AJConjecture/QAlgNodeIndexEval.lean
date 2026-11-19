import Mathlib
import AJConjecture.QAlgInnerDerivativeBasic
import AJConjecture.QAlgNodeIndexEuler
import AJConjecture.QAlgNodeSyzygy

/-!
# The right-hand side of the divided first-jet equation at the node (fibre fact 5)

Let `β* P₀ = S* R*` over `ℂ[M][L]` with `β*(m₀) ≠ 0`, `R*(m₀, l₀) = S*(m₀, l₀) = 0`, and
`β* p = s* r*` for the coefficient `p` of `P₀` in degree `deg P`. Put
`N* = β*² jetNumer P + 2 s* (L ∂_L S*)(r* M ∂_M R* - M r*' R*)`. Then at the node
`N*(m₀, l₀) = s* r* (β* P^W - l₀ m₀ J*)`, `J* = ∂_L R* ∂_M S* - ∂_L S* ∂_M R*`,
`P^W = weylSymbol P`.

Proof. `jetNumer P = p P₁ - p₁ P₀` and `P₁ = P^W - (L ∂_L)(M ∂_M) P₀` (definitions of
`jetNumer`, `weylSymbol`). At the node `β* P₀ = S* R* = 0`, so the `p₁` term vanishes and
`β*² p P₁ = s* r* β* P₁`; the term `M r*' R*` vanishes; `β* ∂_L P₀ = ∂_L (S* R*) = 0`, so
`∂_L P₀ = 0` (here `β*(m₀) ≠ 0` is used). Apply `∂_L ∂_M` (`Polynomial.derivative`,
`innerDerivative_mul`, `innerDerivative_C`) to `β* P₀ = S* R*` and evaluate:
`β* ∂_L ∂_M P₀ = ∂_L S* ∂_M R* + ∂_M S* ∂_L R*`. With `evalIntPoint_eulerEuler`:
`β* P₁ = β* P^W - l₀ m₀ (∂_L S* ∂_M R* + ∂_M S* ∂_L R*)`, and adding
`2 l₀ m₀ ∂_L S* ∂_M R*` gives the claim. Conversions as in `QAlgNodeFibreTangent`
(`Polynomial.derivative_map`, `coeffDerivative_eq_innerDerivative`, `innerDerivative_map`).
-/

open Polynomial

namespace AJConjecture

/-- The value at a complex point as an iterated evaluation. -/
private theorem evalIntPoint_eq_eval_map_indexEval (p : ℤ[X][X]) (m l : ℂ) :
    evalIntPoint p m l =
      ((p.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map
        (Polynomial.evalRingHom m)).eval l := by
  rw [eval_map]
  rfl

/-- Values at a common zero of the fibres of `S` and `R` of `P` and of `∂_L ∂_M P`, when
`β P = S R` and `β(m₀) ≠ 0`. -/
private theorem eval_derivatives_of_C_mul_eq_indexEval {k : Type*} [Field k] {m₀ l₀ : k}
    {β : k[X]} {P S R : k[X][X]} (hβ : β.eval m₀ ≠ 0) (hfac : C β * P = S * R)
    (hR : (R.map (Polynomial.evalRingHom m₀)).eval l₀ = 0)
    (hS : (S.map (Polynomial.evalRingHom m₀)).eval l₀ = 0) :
    (P.map (Polynomial.evalRingHom m₀)).eval l₀ = 0 ∧
      β.eval m₀ *
          ((derivative (innerDerivative P)).map (Polynomial.evalRingHom m₀)).eval l₀ =
        ((innerDerivative S).map (Polynomial.evalRingHom m₀)).eval l₀ *
            ((derivative R).map (Polynomial.evalRingHom m₀)).eval l₀ +
          ((derivative S).map (Polynomial.evalRingHom m₀)).eval l₀ *
            ((innerDerivative R).map (Polynomial.evalRingHom m₀)).eval l₀ := by
  have h0 := congrArg (fun q ↦ (q.map (Polynomial.evalRingHom m₀)).eval l₀) hfac
  simp only [Polynomial.map_mul, eval_mul, Polynomial.map_C, eval_C, coe_evalRingHom, hR,
    mul_zero] at h0
  have hP : (P.map (Polynomial.evalRingHom m₀)).eval l₀ = 0 :=
    (mul_eq_zero.mp h0).resolve_left hβ
  have h1 := congrArg (fun q ↦ ((derivative q).map (Polynomial.evalRingHom m₀)).eval l₀) hfac
  simp only [derivative_C, derivative_mul, Polynomial.map_add, Polynomial.map_mul, eval_add,
    eval_mul, Polynomial.map_C, eval_C, coe_evalRingHom, hR, hS, mul_zero, zero_mul,
    add_zero, zero_add] at h1
  have hdP : ((derivative P).map (Polynomial.evalRingHom m₀)).eval l₀ = 0 :=
    (mul_eq_zero.mp h1).resolve_left hβ
  have h2 := congrArg
    (fun q ↦ ((derivative (innerDerivative q)).map (Polynomial.evalRingHom m₀)).eval l₀) hfac
  simp only [innerDerivative_mul, innerDerivative_C, derivative_add, derivative_C,
    derivative_mul, Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, Polynomial.map_C,
    eval_C, coe_evalRingHom, hR, hS, hdP, mul_zero, zero_mul, add_zero, zero_add] at h2
  exact ⟨hP, by linear_combination h2⟩

/-- The value at a point of `jetNumer P = p P₁ - p₁ P₀`. -/
private theorem eval_map_jetNumer_indexEval (P : RecOp) (m l : ℂ) :
    (((jetNumer P).map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map
        (Polynomial.evalRingHom m)).eval l =
      (((specialize P).coeff P.natDegree).map (Int.castRingHom ℂ)).eval m *
          evalIntPoint (specializeJet P) m l -
        (((specializeJet P).coeff P.natDegree).map (Int.castRingHom ℂ)).eval m *
          evalIntPoint (specialize P) m l := by
  simp only [evalIntPoint_eq_eval_map_indexEval, jetNumer, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C, coe_mapRingHom, coe_evalRingHom, eval_sub, eval_mul,
    eval_C]

/-- The value at a point of the Weyl symbol: `P^W = P₁ + l m ∂_L ∂_M P₀`. -/
private theorem evalIntPoint_weylSymbol_indexEval (P : RecOp) (m l : ℂ) :
    evalIntPoint (weylSymbol P) m l =
      evalIntPoint (specializeJet P) m l +
        l * m *
          ((derivative (innerDerivative
            ((specialize P).map (Polynomial.mapRingHom (Int.castRingHom ℂ))))).map
              (Polynomial.evalRingHom m)).eval l := by
  have hadd : evalIntPoint (specializeJet P + eulerEuler (specialize P)) m l =
      evalIntPoint (specializeJet P) m l + evalIntPoint (eulerEuler (specialize P)) m l := by
    simp only [evalIntPoint_eq_eval_map_indexEval, Polynomial.map_add, eval_add]
  rw [weylSymbol, hadd, evalIntPoint_eulerEuler,
    evalIntPoint_eq_eval_map_indexEval (derivative (coeffDerivative (specialize P))),
    coeffDerivative_eq_innerDerivative, innerDerivative_map, derivative_map]

/-- The value at the node of the right-hand side `N*` of the divided first-jet equation is
`s* r* (β* P^W - l₀ m₀ J*)`. -/
theorem eval_nodeRemainder_of_content {P : RecOp} {m₀ l₀ : ℂ} {βs ss rs : ℂ[X]}
    {Ss Rs : ℂ[X][X]} (hβs : βs.eval m₀ ≠ 0)
    (hfac : C βs * (specialize P).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) = Ss * Rs)
    (hlc : βs * ((specialize P).coeff P.natDegree).map (Int.castRingHom ℂ) = ss * rs)
    (hR : (Rs.map (Polynomial.evalRingHom m₀)).eval l₀ = 0)
    (hS : (Ss.map (Polynomial.evalRingHom m₀)).eval l₀ = 0) :
    ((C (βs ^ 2) * (jetNumer P).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) +
          C (2 * ss) * (X * derivative Ss) *
            (C rs * (C X * innerDerivative Rs) - C (X * derivative rs) * Rs)).map
        (Polynomial.evalRingHom m₀)).eval l₀ =
      ss.eval m₀ * rs.eval m₀ *
        (βs.eval m₀ * evalIntPoint (weylSymbol P) m₀ l₀ -
          l₀ * m₀ *
            ((derivative (Rs.map (Polynomial.evalRingHom m₀))).eval l₀ *
                ((innerDerivative Ss).map (Polynomial.evalRingHom m₀)).eval l₀ -
              (derivative (Ss.map (Polynomial.evalRingHom m₀))).eval l₀ *
                ((innerDerivative Rs).map (Polynomial.evalRingHom m₀)).eval l₀)) := by
  obtain ⟨hP0, hD⟩ := eval_derivatives_of_C_mul_eq_indexEval hβs hfac hR hS
  have hV0 : evalIntPoint (specialize P) m₀ l₀ = 0 := by
    rw [evalIntPoint_eq_eval_map_indexEval]
    exact hP0
  have hW := evalIntPoint_weylSymbol_indexEval P m₀ l₀
  have hJ := eval_map_jetNumer_indexEval P m₀ l₀
  have hlcm := congrArg (eval m₀) hlc
  rw [eval_mul, eval_mul] at hlcm
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
    Polynomial.map_X, eval_add, eval_mul, eval_sub, eval_C, eval_X, coe_evalRingHom, eval_pow,
    eval_ofNat, hR, hJ, hV0, derivative_map, mul_zero, sub_zero]
  linear_combination (βs.eval m₀ * evalIntPoint (specializeJet P) m₀ l₀) * hlcm -
    (ss.eval m₀ * rs.eval m₀ * βs.eval m₀) * hW - (ss.eval m₀ * rs.eval m₀ * l₀ * m₀) * hD

end AJConjecture
