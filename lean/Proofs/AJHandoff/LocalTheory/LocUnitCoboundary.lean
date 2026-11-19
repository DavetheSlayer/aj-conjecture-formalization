import Mathlib
import AJConjecture.QAlgCoboundaryOfSpan

/-!
# A semi-invariant fractional ideal is a unit times a coboundary

Let `O` be a unique factorisation domain with fraction field `F`, `σ` an automorphism of `O` and
`τ` its extension to `F`. If a finite family `x` of `F`, not all zero, satisfies
`span_O(c τ(x_s)) = span_O(x_s)`, then `c = v τ(γ)/γ` with `v ∈ O^×` and `γ ∈ F^×`.

This is `exists_unit_mul_coboundary_of_span_eq` of the library without its hypothesis
`1 ∈ span_O(x)`, at the price of `γ ∈ F` instead of `γ ∈ O`. Proof: rescale by a nonzero member
`x_{s₀}` of the family. The new family `x / x_{s₀}` has `1` in its span and satisfies the
hypothesis with `c τ(x_{s₀})/x_{s₀}` in place of `c`.

This is the step of Lemma 1 of the source where the finite-support divisor calculation over the
meridian valuation rings is replaced by unique factorisation in the two-dimensional regular local
ring `R₀`: no Puiseux extension is needed.
-/

namespace AJConjecture

/-- The span of a rescaled family is the image of the span under multiplication. -/
private theorem span_range_mul_eq_map_unitCoboundary {O F : Type*} [CommRing O] [CommRing F]
    [Algebra O F] {ι : Type*} (g : ι → F) (a : F) :
    Submodule.span O (Set.range fun s ↦ a * g s) =
      (Submodule.span O (Set.range g)).map (LinearMap.mulLeft O a) := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem exists_unit_mul_coboundary_of_span_eq_of_ne_zero {O F : Type*} [CommRing O] [IsDomain O]
    [UniqueFactorizationMonoid O] [Field F] [Algebra O F] [IsFractionRing O F] (σ : O ≃+* O)
    (τ : F →+* F) (hτ : ∀ a : O, τ (algebraMap O F a) = algebraMap O F (σ a)) {ι : Type*}
    [Finite ι] (x : ι → F) (hx : ∃ s, x s ≠ 0) (c : F)
    (hspan : Submodule.span O (Set.range fun s ↦ c * τ (x s)) =
      Submodule.span O (Set.range x)) :
    ∃ (v : Oˣ) (γ : F), γ ≠ 0 ∧ c * γ = algebraMap O F v * τ γ := by
  obtain ⟨s₀, hs₀⟩ := hx
  have hτs₀ : τ (x s₀) ≠ 0 := (map_ne_zero_iff τ τ.injective).2 hs₀
  set y : ι → F := fun s ↦ (x s₀)⁻¹ * x s with hy
  have h1 : (1 : F) ∈ Submodule.span O (Set.range y) := by
    have hmem : y s₀ ∈ Submodule.span O (Set.range y) := Submodule.subset_span ⟨s₀, rfl⟩
    have hy1 : y s₀ = 1 := inv_mul_cancel₀ hs₀
    rwa [hy1] at hmem
  have hfun : (fun s ↦ c * τ (x s₀) / x s₀ * τ (y s)) = fun s ↦ (x s₀)⁻¹ * (c * τ (x s)) := by
    funext s
    rw [hy, map_mul, map_inv₀]
    field_simp
  have hspan' : Submodule.span O (Set.range fun s ↦ c * τ (x s₀) / x s₀ * τ (y s)) =
      Submodule.span O (Set.range y) := by
    rw [hfun, span_range_mul_eq_map_unitCoboundary, hspan, hy,
      span_range_mul_eq_map_unitCoboundary]
  obtain ⟨v, γ, hγ, hvγ⟩ :=
    exists_unit_mul_coboundary_of_span_eq σ τ hτ y _ h1 hspan'
  have hγ' : algebraMap O F γ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O F)).2 hγ
  refine ⟨v, algebraMap O F γ / x s₀, div_ne_zero hγ' hs₀, ?_⟩
  rw [map_mul] at hvγ
  rw [map_div₀, hτ]
  field_simp at hvγ ⊢
  linear_combination hvγ

end AJConjecture
