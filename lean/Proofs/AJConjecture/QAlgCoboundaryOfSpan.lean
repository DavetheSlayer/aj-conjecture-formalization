import Mathlib
import AJConjecture.QAlgPrimitiveScaling
import AJConjecture.QAlgUnitOfSpan

/-!
# A semi-invariant fractional ideal gives a coboundary

Let `O` be a unique factorisation domain with fraction field `F`, `σ` an automorphism of `O`
and `τ` its extension to `F`. If a finite family `x` of `F` whose span `𝔟` contains `1`
satisfies `span(c τ(x_s)) = 𝔟`, then `c γ = v σ(γ)` with `v ∈ O^×` and `γ ∈ O` nonzero.

Proof. By `exists_primitive_scaling`, `δ x_s = y_s` with `y` primitive; `σ ∘ y` is primitive
too (`σ` is an automorphism). Put `w = c δ / σ(δ)`. Then `w σ(y_s) = δ · c τ(x_s) ∈ δ 𝔟 = (y)`
and `y_s = δ x_s ∈ δ · span(c τ(x)) = span(w σ(y))`, so `w = v` is a unit by
`exists_unit_eq_of_mul_mem_span`, and `c δ = v σ(δ)`.
-/

namespace AJConjecture

/-- Multiplication by `a` maps the span of a family into the span of the multiplied family. -/
private theorem mul_mem_span_range_mul_of_mem {O F : Type*} [CommRing O] [CommRing F]
    [Algebra O F] {ι : Type*} (x : ι → F) (a z : F) (hz : z ∈ Submodule.span O (Set.range x)) :
    a * z ∈ Submodule.span O (Set.range fun s ↦ a * x s) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, rfl⟩ := hz
    exact Submodule.subset_span ⟨s, rfl⟩
  | zero =>
    rw [mul_zero]
    exact Submodule.zero_mem _
  | add z z' _ _ hz hz' =>
    rw [mul_add]
    exact Submodule.add_mem _ hz hz'
  | smul r z _ hz =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ r hz

/-- A finite family `x` of the fraction field whose span contains `1` and is equal to the span
of the family `c τ(x)` gives `c γ = v σ(γ)` with `v` a unit and `γ ≠ 0` in `O`. -/
theorem exists_unit_mul_coboundary_of_span_eq {O F : Type*} [CommRing O] [IsDomain O]
    [UniqueFactorizationMonoid O] [Field F] [Algebra O F] [IsFractionRing O F] (σ : O ≃+* O)
    (τ : F →+* F) (hτ : ∀ a : O, τ (algebraMap O F a) = algebraMap O F (σ a)) {ι : Type*}
    [Finite ι] (x : ι → F) (c : F) (h1 : (1 : F) ∈ Submodule.span O (Set.range x))
    (hspan : Submodule.span O (Set.range fun s ↦ c * τ (x s)) =
      Submodule.span O (Set.range x)) :
    ∃ (v : Oˣ) (γ : O), γ ≠ 0 ∧ c * algebraMap O F γ = algebraMap O F (v * σ γ) := by
  obtain ⟨δ, y, hδ, hδy, hprim⟩ := exists_primitive_scaling x h1
  have hinj : Function.Injective (algebraMap O F) := IsFractionRing.injective O F
  have hσδ : algebraMap O F (σ δ) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ((map_ne_zero_iff σ σ.injective).mpr hδ)
  have hprim' : ∀ p : O, (∀ s, p ∣ σ (y s)) → IsUnit p := by
    intro p hp
    have hu : IsUnit (σ.symm p) := hprim _ fun s ↦ by
      have hdvd := map_dvd σ.symm (hp s)
      rwa [RingEquiv.symm_apply_apply] at hdvd
    have hu' := hu.map σ
    rwa [RingEquiv.apply_symm_apply] at hu'
  obtain ⟨w, hw⟩ : ∃ w : F, w = c * algebraMap O F δ / algebraMap O F (σ δ) := ⟨_, rfl⟩
  have hkey : ∀ s, w * algebraMap O F (σ (y s)) = algebraMap O F δ * (c * τ (x s)) := by
    intro s
    rw [← hτ (y s), ← hδy s, map_mul, hτ δ, hw]
    field_simp
  have h₁ : ∀ s, w * algebraMap O F (σ (y s)) ∈
      Submodule.span O (Set.range fun s ↦ algebraMap O F (y s)) := by
    intro s
    rw [hkey s]
    have hmem : c * τ (x s) ∈ Submodule.span O (Set.range x) := by
      rw [← hspan]
      exact Submodule.subset_span ⟨s, rfl⟩
    simpa only [hδy] using mul_mem_span_range_mul_of_mem x (algebraMap O F δ) _ hmem
  have h₂ : ∀ s, algebraMap O F (y s) ∈
      Submodule.span O (Set.range fun s ↦ w * algebraMap O F (σ (y s))) := by
    intro s
    rw [← hδy s]
    have hmem : x s ∈ Submodule.span O (Set.range fun s ↦ c * τ (x s)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨s, rfl⟩
    simpa only [hkey] using
      mul_mem_span_range_mul_of_mem (fun s ↦ c * τ (x s)) (algebraMap O F δ) _ hmem
  obtain ⟨v, hv⟩ := exists_unit_eq_of_mul_mem_span y (fun s ↦ σ (y s)) hprim hprim' w h₁ h₂
  refine ⟨v, δ, hδ, ?_⟩
  rw [map_mul, ← hv, hw, div_mul_cancel₀ _ hσδ]

end AJConjecture
