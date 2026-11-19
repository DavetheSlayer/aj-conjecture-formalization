import Mathlib
import AJConjecture.QAlgNodeJetBasic

/-!
# The first jet of the coboundary identity (Theorem B)

Write `f⁰ = complexSpec f`, `f¹ = complexJet f`. From
`r_0 γ₁ σ(γ₂) v₂ = r_d v₁ σ(γ₁) γ₂` with `γ₁⁰ ≠ 0`, `γ₂⁰ ≠ 0`:

* value at `t = -1`: `r_0⁰ v₂⁰ = r_d⁰ v₁⁰` (cancel `γ₁⁰ γ₂⁰`);
* first jet, by `complexJet_mul` and `complexJet_complexShift`: the terms with `γ₁¹`, `γ₂¹`
  cancel by the previous line and
  `γ₁⁰ γ₂⁰ (r_0¹ v₂⁰ + r_0⁰ v₂¹ - r_d¹ v₁⁰ - r_d⁰ v₁¹) = 2 M r_0⁰ v₂⁰ (γ₁⁰ γ₂⁰' - γ₁⁰' γ₂⁰)`.

Multiplying by `r_d⁰ v₁⁰` and using the first line again gives the statement, which says
`(r_0¹ r_d⁰ - r_0⁰ r_d¹)/(r_0⁰ r_d⁰) = v₁¹/v₁⁰ - v₂¹/v₂⁰ + 2M (γ₂⁰'/γ₂⁰ - γ₁⁰'/γ₁⁰)`.
-/

open Polynomial

namespace AJConjecture

/-- The first jet of the coboundary identity: the logarithmic first jet of `r_0 / r_d` is a
regular term plus `2M` times a difference of logarithmic derivatives. -/
theorem coboundary_jet_identity {r₀ r₁ γ₁ γ₂ v₁ v₂ : ℂ[X][X]} (hγ₁ : complexSpec γ₁ ≠ 0)
    (hγ₂ : complexSpec γ₂ ≠ 0)
    (h : r₀ * γ₁ * complexShift γ₂ * v₂ = r₁ * v₁ * complexShift γ₁ * γ₂) :
    (complexJet r₀ * complexSpec r₁ - complexSpec r₀ * complexJet r₁) *
        (complexSpec v₁ * complexSpec v₂ * complexSpec γ₁ * complexSpec γ₂) =
      complexSpec r₀ * complexSpec r₁ *
        (complexSpec γ₁ * complexSpec γ₂ *
            (complexSpec v₂ * complexJet v₁ - complexSpec v₁ * complexJet v₂) +
          2 * X * (complexSpec v₁ * complexSpec v₂) *
            (complexSpec γ₁ * derivative (complexSpec γ₂) -
              derivative (complexSpec γ₁) * complexSpec γ₂)) := by
  have hs := congrArg complexSpec h
  simp only [map_mul, complexSpec_complexShift] at hs
  have hj := congrArg complexJet h
  simp only [complexJet_mul, map_mul, complexSpec_complexShift, complexJet_complexShift] at hj
  have he : complexSpec r₀ * complexSpec v₂ = complexSpec r₁ * complexSpec v₁ := by
    apply mul_right_cancel₀ (mul_ne_zero hγ₁ hγ₂)
    linear_combination hs
  linear_combination (complexSpec r₁ * complexSpec v₁) * hj +
    (-(complexJet r₁ * complexSpec v₁ * complexSpec γ₁ * complexSpec γ₂) -
      complexSpec r₁ * complexJet v₁ * complexSpec γ₁ * complexSpec γ₂ +
      2 * X * complexSpec r₁ * complexSpec v₁ * derivative (complexSpec γ₁) * complexSpec γ₂ -
      complexSpec r₁ * complexSpec v₁ * complexJet γ₁ * complexSpec γ₂ -
      complexSpec r₁ * complexSpec v₁ * complexSpec γ₁ * complexJet γ₂) * he

end AJConjecture
