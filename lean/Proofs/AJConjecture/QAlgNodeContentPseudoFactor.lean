import Mathlib
import AJConjecture.QAlgNodeContentFactor
import AJConjecture.QAlgSpecializeOreMul

/-!
# The contents at `M = m₀` of the symbols of a pseudo-factorisation (fibre fact 1)

Let `β P = S ⋆ R` with `β₀ = β(-1, M) ≠ 0` and the leading coefficient of `P₀ = specialize P`
not vanishing at `m₀`. Over `ℂ[M][L]`, with `μ = M - m₀`: `R₀ = μ^a R*`, `S₀ = μ^b S*`,
`β₀ = μ^(a+b) β*`, `β*(m₀) ≠ 0`, `β* P₀ = S* R*`.

Proof. `β₀ P₀ = S₀ R₀` over `ℤ` (`specialize_oreMul`; `specialize (C β * P) = C β₀ * P₀` by
`Polynomial.map_mul`, `Polynomial.map_C`), base-changed to `ℂ` (`Polynomial.map_mul`). The base
change of `β₀` is not zero (`Polynomial.map_injective`, `Int.cast_injective`); the fibre of
`P₀` is not zero because its coefficient of degree `deg P₀` is `hlead`. Apply
`exists_content_of_mul_eq`.
-/

open Polynomial

namespace AJConjecture

/-- The symbols of the two factors of `β P = S ⋆ R` are powers of `M - m₀` times polynomials
`S*`, `R*` with `β* P₀ = S* R*` and `β*(m₀) ≠ 0`. -/
theorem exists_nodeContent_of_pseudoFactor {P S R : RecOp} {β : Coeff} {m₀ : ℂ}
    (hβ : β.map (Polynomial.evalRingHom (-1)) ≠ 0) (h : C β * P = oreMul coeffShift S R)
    (hlead : ((specialize P).leadingCoeff.map (Int.castRingHom ℂ)).eval m₀ ≠ 0) :
    ∃ (a b : ℕ) (βs : ℂ[X]) (Ss Rs : ℂ[X][X]),
      (specialize R).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
        C ((X - C m₀) ^ a) * Rs ∧
      (specialize S).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
        C ((X - C m₀) ^ b) * Ss ∧
      (β.map (Polynomial.evalRingHom (-1))).map (Int.castRingHom ℂ) =
        (X - C m₀) ^ (a + b) * βs ∧
      βs.eval m₀ ≠ 0 ∧
      C βs * (specialize P).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) = Ss * Rs := by
  have hspecC : specialize (C β) = C (β.map (Polynomial.evalRingHom (-1))) := by
    rw [specialize, coe_mapRingHom, Polynomial.map_C, coe_mapRingHom]
  have I1 : C (β.map (Polynomial.evalRingHom (-1))) * specialize P =
      specialize S * specialize R := by
    rw [← specialize_oreMul, ← h, map_mul, hspecC]
  have I1c := congrArg (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) I1
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, coe_mapRingHom] at I1c
  have hβc : (β.map (Polynomial.evalRingHom (-1))).map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective_int (Int.castRingHom ℂ))).mpr hβ
  have hfib : ((specialize P).map (Polynomial.mapRingHom (Int.castRingHom ℂ))).map
      (Polynomial.evalRingHom m₀) ≠ 0 := by
    intro h0
    apply hlead
    have hc := congrArg (fun q ↦ q.coeff (specialize P).natDegree) h0
    simpa only [coeff_map, coe_mapRingHom, coe_evalRingHom, coeff_zero,
      coeff_natDegree] using hc
  exact exists_content_of_mul_eq hβc hfib I1c

end AJConjecture
