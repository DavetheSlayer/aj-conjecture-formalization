import Mathlib
import AJConjecture.APolynomial
import AJFamily.Classical.HomCheb

/-!
# Evaluating the family polynomials

Closed forms for the values at `(M, L) ∈ ℂ²` of the polynomials `k`, `τ`, `A` and `B_m` of
`FamilyPolynomials`; the value of `B_m` is expressed through `homCheb` of the values of `τ`
and `k`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Evaluation at `(M, L)` of an integer bivariate polynomial, as a ring homomorphism. -/
private def famEvalHom (M L : ℂ) : ℤ[X][X] →+* ℂ :=
  (eval₂RingHom (evalRingHom M) L).comp (mapRingHom (mapRingHom (Int.castRingHom ℂ)))

/-- `evalPoint ∘ mapC` is the ring homomorphism `famEvalHom`. -/
private theorem evalPoint_mapC_eq_famEvalHom (P : ℤ[X][X]) (M L : ℂ) :
    evalPoint (mapC P) (M, L) = famEvalHom M L P := rfl

/-- `x = M²` evaluates to `M²`. -/
private theorem famEvalHom_famX (M L : ℂ) : famEvalHom M L famX = M ^ 2 := by
  simp [famEvalHom, famX, eval₂_pow, eval₂_C]

/-- The outer variable evaluates to `L`. -/
private theorem famEvalHom_X (M L : ℂ) : famEvalHom M L X = L := by
  simp [famEvalHom]

/-- `P` evaluates to `(M² - 1)(1 - L)`. -/
private theorem famEvalHom_famP (M L : ℂ) :
    famEvalHom M L famP = (M ^ 2 - 1) * (1 - L) := by
  simp only [famP, map_mul, map_sub, map_one, famEvalHom_famX, famEvalHom_X]

/-- `Q` evaluates to `M² + L`. -/
private theorem famEvalHom_famQ (M L : ℂ) : famEvalHom M L famQ = M ^ 2 + L := by
  simp only [famQ, map_add, famEvalHom_famX, famEvalHom_X]

/-- Evaluation of `k`. -/
theorem evalPoint_famK (M L : ℂ) : evalPoint (mapC famK) (M, L) = M ^ 2 * (M ^ 2 + L) ^ 2 := by
  simp only [evalPoint_mapC_eq_famEvalHom, famK, map_mul, map_pow, famEvalHom_famX,
    famEvalHom_famQ]

/-- Evaluation of `τ`. -/
theorem evalPoint_famTau (M L : ℂ) :
    evalPoint (mapC famTau) (M, L) =
      let P := (M ^ 2 - 1) * (1 - L)
      let Q := M ^ 2 + L
      M ^ 4 * P * Q + M ^ 2 * P ^ 2 - 2 * M ^ 2 * P * Q + 2 * M ^ 2 * Q ^ 2 + P * Q := by
  simp only [evalPoint_mapC_eq_famEvalHom, famTau, map_add, map_sub, map_mul, map_pow,
    map_ofNat, famEvalHom_famX, famEvalHom_famP, famEvalHom_famQ]
  ring

/-- Evaluation of `A`. -/
theorem evalPoint_famA (M L : ℂ) :
    evalPoint (mapC famA) (M, L) =
      let P := (M ^ 2 - 1) * (1 - L)
      let Q := M ^ 2 + L
      M ^ 4 * P * Q - M ^ 4 * Q ^ 2 + M ^ 2 * P ^ 2 - 3 * M ^ 2 * P * Q + 3 * M ^ 2 * Q ^ 2 +
        P * Q - Q ^ 2 := by
  simp only [evalPoint_mapC_eq_famEvalHom, famA, map_add, map_sub, map_mul, map_pow,
    map_ofNat, famEvalHom_famX, famEvalHom_famP, famEvalHom_famQ]
  ring

/-- Evaluation of `B_m` through the homogenised Chebyshev sequence. -/
theorem evalPoint_famB (m : ℕ) (M L : ℂ) :
    evalPoint (mapC (famB m)) (M, L) =
      evalPoint (mapC famA) (M, L) *
          homCheb (evalPoint (mapC famTau) (M, L)) (evalPoint (mapC famK) (M, L)) m -
        evalPoint (mapC famK) (M, L) ^ 2 *
          homCheb (evalPoint (mapC famTau) (M, L)) (evalPoint (mapC famK) (M, L)) (m - 1) := by
  simp only [evalPoint_mapC_eq_famEvalHom, famB, map_sub, map_mul, map_pow, map_homCheb]

end AJConjecture
