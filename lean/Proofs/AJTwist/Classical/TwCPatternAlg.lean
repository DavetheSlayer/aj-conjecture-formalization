import Mathlib
import AJTwist.Classical.TwCSatelliteDefs

/-!
# From the orbit split to the pattern relations: pure group theory

The last step of Unit C2. From the splitting of the longitude at the two Hopf loops, the edge
relations, the loops of the Hopf letters and the two gap relations `C R_0 = 1`, `H₂ H₁ = 1`, the
pattern relations `IsWhPattern` follow by a computation in an arbitrary group:

* `twcPattern_neg` (negative clasp): the clasp is `R_0 = α β⁻¹ α⁻¹ β`, and
  `IsWhPattern μ t z_0 l`. This is `pairWh_clasp` and `pairWh_algebra` of
  `AJHandoff.TorusKnot.PairKPeripheral` (private there) with `Λ` renamed `t`.
* `twcPattern_pos` (positive clasp): the Hopf relations give `H₁ = β⁻¹ α`, the clasp
  `R_0 = α⁻¹ β⁻¹ α β` and `α = β (U μ U⁻¹) β⁻¹`; then `z_0 = t⁻¹ c t` with
  `c = compMer μ (t μ t⁻¹)`, which is `c` because `t` commutes with `z_0`, and
  `l = μ⁻¹ t μ t⁻¹ μ⁻¹ t⁻¹ μ t`, whose inverse is the pattern word for `t⁻¹` up to conjugation by
  `μ²`, which is trivial because `l` commutes with `μ`. So `IsWhPattern μ t⁻¹ z_0 l⁻¹`.
-/

namespace AJConjecture

/-- Negative clasp: the orbit split, the Hopf loops and the gap relations give the pattern
relations with axis meridian `t`. -/
theorem twcPattern_neg {G : Type*} [Group G] (μ α β h h₂ R C Gg M U z₀ t l : G)
    (hl : l = Gg * h⁻¹ * M * h * U) (hcomm : l * μ = μ * l) (hμ : μ = Gg * β * Gg⁻¹)
    (hα : α = U * μ * U⁻¹) (hC : C * R = 1) (htop : h₂ * h = 1) (hH1 : h = R * β⁻¹ * α)
    (hH2 : h₂ = C * h * α⁻¹ * h⁻¹ * β * R⁻¹) (hz : U⁻¹ * R * U = z₀) (hGU : Gg * U = t)
    (hM : Gg * R⁻¹ * M * R * Gg⁻¹ = t⁻¹) : IsWhPattern μ t z₀ l := by
  have hR : R = α * β⁻¹ * α⁻¹ * β := by
    have hC' : C = R⁻¹ := eq_inv_of_mul_eq_one_left hC
    subst hC' hH1 hH2
    have h1 : R⁻¹ * (R * β⁻¹ * α) * α⁻¹ * (R * β⁻¹ * α)⁻¹ * β * R⁻¹ * (R * β⁻¹ * α) =
        β⁻¹ * α⁻¹ * β * R⁻¹ * β * β⁻¹ * α := by group
    rw [h1] at htop
    have h2 : R⁻¹ = (β⁻¹ * α⁻¹ * β)⁻¹ * (β⁻¹ * α⁻¹ * β * R⁻¹ * β * β⁻¹ * α) * α⁻¹ := by group
    rw [htop, mul_one] at h2
    rw [← inv_inv R, h2]
    group
  have hβ : β = Gg⁻¹ * μ * Gg := by rw [hμ]; group
  have hGg : Gg = t * U⁻¹ := by rw [← hGU]; group
  have hM' : M = R * Gg⁻¹ * t⁻¹ * Gg * R⁻¹ := by
    calc M = R * Gg⁻¹ * (Gg * R⁻¹ * M * R * Gg⁻¹) * Gg * R⁻¹ := by group
      _ = _ := by rw [hM]
  have hc : Commute l μ := hcomm
  clear hμ hM hcomm hC htop hH2
  subst hz hH1 hM' hR hα hβ hGg
  refine ⟨by rw [compMer]; group, ?_⟩
  have hE : l = t * μ⁻¹ * t⁻¹ * μ * t⁻¹ * μ⁻¹ * t * μ := by rw [hl]; group
  calc l = μ ^ 2 * l * (μ ^ 2)⁻¹ := by rw [← (hc.pow_right 2).eq]; group
    _ = μ ^ 2 * (t * μ⁻¹ * t⁻¹ * μ * t⁻¹ * μ⁻¹ * t * μ) * (μ ^ 2)⁻¹ := by rw [← hE]
    _ = _ := by group

/-- Positive clasp: the orbit split, the Hopf loops and the gap relations give the pattern
relations with axis meridian `t⁻¹` and the inverse longitude. -/
theorem twcPattern_pos {G : Type*} [Group G] (μ α β h h₂ R C Gg M U z₀ t l : G)
    (hl : l = Gg * h * M * h⁻¹ * U) (hcomm : l * μ = μ * l) (hμ : μ = Gg * β * Gg⁻¹)
    (hα : α = h⁻¹ * U * μ * U⁻¹ * h) (hC : C * R = 1) (htop : h₂ * h = 1)
    (hH1 : h = α * R * β⁻¹) (hH2 : h₂ = α * h⁻¹ * C * R * β⁻¹ * h⁻¹) (hz : U⁻¹ * R * U = z₀)
    (hGU : Gg * U = t) (hM : Gg * R⁻¹ * M * R * Gg⁻¹ = t⁻¹) (htz : t * z₀ = z₀ * t) :
    IsWhPattern μ t⁻¹ z₀ l⁻¹ := by
  have hC' : C = R⁻¹ := eq_inv_of_mul_eq_one_left hC
  have hh₂ : h₂ = h⁻¹ := eq_inv_of_mul_eq_one_left htop
  have hh : h = β⁻¹ * α := by
    rw [hh₂, hC'] at hH2
    have h1 : α * h⁻¹ * β⁻¹ = 1 := by
      calc α * h⁻¹ * β⁻¹ = (α * h⁻¹ * R⁻¹ * R * β⁻¹ * h⁻¹) * h := by group
        _ = h⁻¹ * h := by rw [← hH2]
        _ = 1 := by group
    calc h = β⁻¹ * (α * h⁻¹ * β⁻¹)⁻¹ * α := by group
      _ = β⁻¹ * α := by rw [h1]; group
  have hR : R = α⁻¹ * β⁻¹ * α * β := by
    calc R = α⁻¹ * (α * R * β⁻¹) * β := by group
      _ = α⁻¹ * h * β := by rw [← hH1]
      _ = _ := by rw [hh]; group
  have hα' : α = β * (U * μ * U⁻¹) * β⁻¹ := by
    have h2 : α = (β⁻¹ * α)⁻¹ * U * μ * U⁻¹ * (β⁻¹ * α) := by rw [← hh]; exact hα
    calc α = α * ((β⁻¹ * α)⁻¹ * U * μ * U⁻¹ * (β⁻¹ * α)) * α⁻¹ := by rw [← h2]; group
      _ = β * (U * μ * U⁻¹) * β⁻¹ := by group
  have hβ : β = Gg⁻¹ * μ * Gg := by rw [hμ]; group
  have hU : U = Gg⁻¹ * t := by rw [← hGU]; group
  have hM' : M = R * Gg⁻¹ * t⁻¹ * Gg * R⁻¹ := by
    calc M = R * Gg⁻¹ * (Gg * R⁻¹ * M * R * Gg⁻¹) * Gg * R⁻¹ := by group
      _ = _ := by rw [hM]
  have hc : Commute l μ := hcomm
  have hz' : z₀ = t⁻¹ * compMer μ (t * μ * t⁻¹) * t := by
    rw [← hz, hR, hα', hβ, hU, compMer]
    group
  have hE : l = μ⁻¹ * t * μ * t⁻¹ * μ⁻¹ * t⁻¹ * μ * t := by
    rw [hl, hM', hh, hR, hα', hβ, hU]
    group
  refine ⟨?_, ?_⟩
  · have h3 : z₀ = t * z₀ * t⁻¹ := by rw [htz]; group
    rw [h3, hz', inv_inv]
    group
  · have hc' : Commute l⁻¹ μ := hc.inv_left
    calc l⁻¹ = μ ^ 2 * l⁻¹ * (μ ^ 2)⁻¹ := by rw [← (hc'.pow_right 2).eq]; group
      _ = μ ^ 2 * (μ⁻¹ * t * μ * t⁻¹ * μ⁻¹ * t⁻¹ * μ * t)⁻¹ * (μ ^ 2)⁻¹ := by rw [← hE]
      _ = _ := by group

end AJConjecture
