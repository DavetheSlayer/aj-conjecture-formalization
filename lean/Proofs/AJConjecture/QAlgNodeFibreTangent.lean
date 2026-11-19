import Mathlib
import AJConjecture.QAlgNodeFibreGradient
import AJConjecture.QAlgNodeFibreLocalDvd

/-!
# The primitive part of a multiple of `G` is tangent to `G` at a point of `G` (fibre facts 2, 4)

Let `toComparison G ∣ toComparison F`, `G(m₀, l₀) = 0`, `∂_L G(m₀, l₀) ≠ 0`, `l₀ ≠ 0`, and
`F = μ^a F*` over `ℂ[M][L]`, `μ = M - m₀`. Then `F*(m₀, l₀) = 0` and
`∇F*(m₀, l₀) = λ ∇G(m₀, l₀)` for some `λ ∈ ℂ`.

Proof. The fibre of `G` at `m₀` is not zero since its derivative does not vanish at `l₀`.
`exists_local_dvd_of_toComparison_dvd` gives `u L^n F* = G Q` over `ℂ` with `u(m₀) ≠ 0`, and
`exists_gradient_eq_mul_of_local_dvd` the proportionality. Conversions:
`evalIntPoint p m l = ((p.map (mapRingHom (Int.castRingHom ℂ))).map (evalRingHom m)).eval l`
(unfold `evalIntPoint`, `evalPoint`; `Polynomial.eval_map`), `Polynomial.derivative_map`,
`coeffDerivative_eq_innerDerivative` and `innerDerivative_map`.
-/

open Polynomial

namespace AJConjecture

/-- The value at a complex point is the value of the fibre of the base change. -/
theorem evalIntPoint_eq_eval (p : ℤ[X][X]) (m l : ℂ) :
    evalIntPoint p m l =
      ((p.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map
        (Polynomial.evalRingHom m)).eval l := by
  unfold evalIntPoint evalPoint
  rw [eval_map]

/-- If `G` divides `F` in the comparison ring and `(m₀, l₀)` is a point of `G` with
`∂_L G ≠ 0`, then the primitive part `F*` of `F` at `m₀` vanishes at `(m₀, l₀)` and its
gradient there is proportional to the gradient of `G`. -/
theorem exists_tangent_of_toComparison_dvd {G F : ℤ[X][X]} {m₀ l₀ : ℂ} (hl₀ : l₀ ≠ 0)
    (hG : evalIntPoint G m₀ l₀ = 0) (hGL : evalIntPoint (derivative G) m₀ l₀ ≠ 0)
    (hdvd : toComparison G ∣ toComparison F) {a : ℕ} {Fs : ℂ[X][X]}
    (hF : F.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) = C ((X - C m₀) ^ a) * Fs) :
    ∃ lam : ℂ, (Fs.map (Polynomial.evalRingHom m₀)).eval l₀ = 0 ∧
      (derivative (Fs.map (Polynomial.evalRingHom m₀))).eval l₀ =
        lam * evalIntPoint (derivative G) m₀ l₀ ∧
      ((innerDerivative Fs).map (Polynomial.evalRingHom m₀)).eval l₀ =
        lam * evalIntPoint (coeffDerivative G) m₀ l₀ := by
  rw [evalIntPoint_eq_eval] at hG
  rw [evalIntPoint_eq_eval, ← derivative_map, ← derivative_map] at hGL
  rw [evalIntPoint_eq_eval, evalIntPoint_eq_eval,
    ← derivative_map, ← derivative_map, coeffDerivative_eq_innerDerivative, ← innerDerivative_map]
  have hGfib : (G.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map
      (Polynomial.evalRingHom m₀) ≠ 0 := fun h0 ↦ by
    rw [h0, derivative_zero, eval_zero] at hGL
    exact hGL rfl
  obtain ⟨u, n, Q, hu, h⟩ := exists_local_dvd_of_toComparison_dvd hdvd hGfib hF
  exact exists_gradient_eq_mul_of_local_dvd hu hl₀ h hG

end AJConjecture
