import Mathlib
import AJConjecture.QAlgLogDerivResidue
import AJConjecture.QAlgNodeCoboundary
import AJConjecture.QAlgNodeCoboundaryJet
import AJConjecture.QAlgNodeCoboundarySpec

/-!
# The index of a right pseudo-factor is a non-negative integer (Theorems A and B)

Let `β P = S ⋆ R` with the leading and constant coefficients of `P` not vanishing at
`(t, M) = (-1, m₀)`. Then the logarithmic first jet `nodeNumer R / nodeDenom R` of
`r_0 / r_d` has at most a simple pole at `M = m₀`, with residue `-2 m₀ j`, `j ∈ ℕ`:
with `μ = X - m₀` and `k` the multiplicity of `m₀` in `nodeDenom R`,
`μ^(k+1) ∣ μ · nodeNumer R + 2 j m₀ · nodeDenom R`.

Proof: `exists_complex_coboundary_of_pseudoFactor` (Theorem A),
`exists_coboundary_complexSpec_ne_zero`, `coboundary_jet_identity` (Theorem B) and
`exists_nat_pow_dvd_of_logDeriv_identity`.
-/

open Polynomial

namespace AJConjecture

/-- The residue at `m₀` of the logarithmic first jet of `r_0 / r_d`, for a right pseudo-factor
`R` of an operator with end coefficients nonzero at `(-1, m₀)`, is `-2 m₀ j` with `j ∈ ℕ`. -/
theorem exists_nat_pow_dvd_nodeNumer_of_pseudoFactor {m₀ : ℂ} {P S R : RecOp} {β : Coeff}
    (hβ : β ≠ 0) (h : C β * P = oreMul coeffShift S R)
    (hlead : (complexSpec (coeffToComplex P.leadingCoeff)).eval m₀ ≠ 0)
    (hconst : (complexSpec (coeffToComplex (P.coeff 0))).eval m₀ ≠ 0) :
    ∃ j : ℕ, (X - C m₀) ^ (((nodeDenom R).map (Int.castRingHom ℂ)).rootMultiplicity m₀ + 1) ∣
      (X - C m₀) * (nodeNumer R).map (Int.castRingHom ℂ) +
        C (2 * j * m₀) * (nodeDenom R).map (Int.castRingHom ℂ) := by
  obtain ⟨γ₁, γ₂, v₁, v₂, hγ₁, hγ₂, hv₁, hv₂, hc⟩ :=
    exists_complex_coboundary_of_pseudoFactor hβ h hlead hconst
  obtain ⟨γ₁', hγ₁', hc'⟩ := exists_coboundary_complexSpec_ne_zero hγ₁ hc
  have hγ₂' : complexSpec γ₂ ≠ 0 := fun h0 ↦ hγ₂ (by rw [h0, eval_zero])
  have hid := coboundary_jet_identity hγ₁' hγ₂' hc'
  have hN : (nodeNumer R).map (Int.castRingHom ℂ) =
      complexJet (coeffToComplex (R.coeff 0)) * complexSpec (coeffToComplex R.leadingCoeff) -
        complexSpec (coeffToComplex (R.coeff 0)) * complexJet (coeffToComplex R.leadingCoeff) := by
    simp only [nodeNumer, Polynomial.map_sub, Polynomial.map_mul, complexSpec_coeffToComplex,
      complexJet_coeffToComplex, coeff_specializeJet, coeff_specialize, Polynomial.leadingCoeff]
  have hD : (nodeDenom R).map (Int.castRingHom ℂ) =
      complexSpec (coeffToComplex (R.coeff 0)) * complexSpec (coeffToComplex R.leadingCoeff) := by
    simp only [nodeDenom, Polynomial.map_mul, complexSpec_coeffToComplex, coeff_specialize,
      Polynomial.leadingCoeff]
  rw [hN, hD]
  refine exists_nat_pow_dvd_of_logDeriv_identity (g₁ := complexSpec γ₁') (g₂ := complexSpec γ₂)
    (u := complexSpec v₁ * complexSpec v₂)
    (A := complexSpec v₂ * complexJet v₁ - complexSpec v₁ * complexJet v₂) hγ₁' hγ₂
    (by rw [eval_mul]; exact mul_ne_zero hv₁ hv₂) ?_
  linear_combination hid

end AJConjecture
