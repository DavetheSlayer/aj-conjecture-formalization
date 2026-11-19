import Mathlib
import AJConjecture.QAlgNodeContentEnds
import AJConjecture.QAlgNodeIndexDivide
import AJConjecture.QAlgNodeSyzygy

/-!
# The first-jet equation of a pseudo-factorisation, divided by the contents (step 3)

Let `β P = S ⋆ R`, `deg P = deg S + deg R`, `e = deg S`, `d = deg R`, and over `ℂ[M][L]`
`R₀ = μ^a R*`, `S₀ = μ^b S*`, `β₀ = μ^(a+b) β*` (`μ = M - m₀`). With `s*`, `r*` the
coefficients of `S*`, `R*` in degrees `e`, `d`, there is `U` with
`S* · (μ^(2b) s* · jetNumer R) + R* · U = μ^(2a+2b) N*`,
`N* = β*² jetNumer P + 2 s* (L ∂_L S*)(r* M ∂_M R* - M r*' R*)`.

Proof. Base-change `specialize_mul_jetNumer_add` to `ℂ` (`Polynomial.map_mul`,
`Polynomial.map_add`, `Polynomial.map_sub`, `Polynomial.map_C`, `Polynomial.map_X`,
`Polynomial.derivative_map`, `coeffDerivative_eq_innerDerivative`, `innerDerivative_map`,
`Polynomial.coeff_map`). The coefficients of `S₀`, `R₀` in degrees `e`, `d` become `μ^b s*`,
`μ^a r*` (`Polynomial.coeff_C_mul`). Substitute `hR`, `hS`, `hβ`; the bracket is
`content_mul_jetBracket` with `A = μ^a`, `B = μ^b`. Take `U = C (μ^a) * U₀` where `U₀` is the
base change of the second factor of `specialize R` in `specialize_mul_jetNumer_add`; the rest
is `ring`/`linear_combination`.
-/

open Polynomial

namespace AJConjecture

/-- The first-jet equation of `β P = S ⋆ R`, base-changed to `ℂ`. -/
private theorem exists_map_jetNumer_add_indexEquation {P S R : RecOp} {β : Coeff}
    (h : C β * P = oreMul coeffShift S R) (hn : P.natDegree = S.natDegree + R.natDegree) :
    ∃ U₀ : ℂ[X][X],
      (specialize S).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) *
          (C (((specialize S).coeff S.natDegree).map (Int.castRingHom ℂ)) *
            (jetNumer R).map (Polynomial.mapRingHom (Int.castRingHom ℂ))) +
        (specialize R).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) * U₀ =
      C ((β.map (Polynomial.evalRingHom (-1))).map (Int.castRingHom ℂ) ^ 2) *
          (jetNumer P).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) +
        C (2 * ((specialize S).coeff S.natDegree).map (Int.castRingHom ℂ)) *
          (X * derivative ((specialize S).map (Polynomial.mapRingHom (Int.castRingHom ℂ)))) *
          (C (((specialize R).coeff R.natDegree).map (Int.castRingHom ℂ)) *
              (C X * innerDerivative
                ((specialize R).map (Polynomial.mapRingHom (Int.castRingHom ℂ)))) -
            C (X * derivative (((specialize R).coeff R.natDegree).map (Int.castRingHom ℂ))) *
              (specialize R).map (Polynomial.mapRingHom (Int.castRingHom ℂ))) := by
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : ℤ[X][X],
      specialize S * (C ((specialize S).coeff S.natDegree) * jetNumer R) + specialize R * U₀ =
        C (β.map (Polynomial.evalRingHom (-1)) ^ 2) * jetNumer P +
          C (2 * (specialize S).coeff S.natDegree) * (X * derivative (specialize S)) *
            (C ((specialize R).coeff R.natDegree) * (C X * coeffDerivative (specialize R)) -
              C (X * derivative ((specialize R).coeff R.natDegree)) * specialize R) :=
    ⟨_, specialize_mul_jetNumer_add h hn⟩
  refine ⟨U₀.map (Polynomial.mapRingHom (Int.castRingHom ℂ)), ?_⟩
  have hmap := congrArg (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) hU₀
  simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_pow, Polynomial.map_ofNat, ← derivative_map,
    coe_mapRingHom, coeffDerivative_eq_innerDerivative, ← innerDerivative_map] using hmap

/-- The first-jet equation of `β P = S ⋆ R` for the primitive parts `S*`, `R*` at `m₀`:
`S* · (μ^(2b) s* jetNumer R) + R* · U = μ^(2a+2b) N*`. -/
theorem exists_nodeSyzygy_of_content {P S R : RecOp} {β : Coeff}
    (h : C β * P = oreMul coeffShift S R) (hn : P.natDegree = S.natDegree + R.natDegree)
    {m₀ : ℂ} {a b : ℕ} {βs : ℂ[X]} {Ss Rs : ℂ[X][X]}
    (hR : (specialize R).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
      C ((X - C m₀) ^ a) * Rs)
    (hS : (specialize S).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
      C ((X - C m₀) ^ b) * Ss)
    (hβ : (β.map (Polynomial.evalRingHom (-1))).map (Int.castRingHom ℂ) =
      (X - C m₀) ^ (a + b) * βs) :
    ∃ U : ℂ[X][X],
      Ss * (C ((X - C m₀) ^ (2 * b) * Ss.coeff S.natDegree) *
            (jetNumer R).map (Polynomial.mapRingHom (Int.castRingHom ℂ))) + Rs * U =
        C ((X - C m₀) ^ (2 * a + 2 * b)) *
          (C (βs ^ 2) * (jetNumer P).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) +
            C (2 * Ss.coeff S.natDegree) * (X * derivative Ss) *
              (C (Rs.coeff R.natDegree) * (C X * innerDerivative Rs) -
                C (X * derivative (Rs.coeff R.natDegree)) * Rs)) := by
  obtain ⟨U₀, key⟩ := exists_map_jetNumer_add_indexEquation h hn
  rw [coeff_map_specialize_eq hS, coeff_map_specialize_eq hR, hS, hR,
    hβ, content_mul_jetBracket] at key
  refine ⟨C ((X - C m₀) ^ a) * U₀, ?_⟩
  simp only [C_mul, C_pow] at key ⊢
  linear_combination key

end AJConjecture
