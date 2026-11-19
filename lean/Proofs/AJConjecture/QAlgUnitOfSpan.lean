import Mathlib

/-!
# A scalar exchanging two primitive ideals is a unit

Let `O` be a unique factorisation domain with fraction field `F`, and `y`, `y'` two families of
`O` each without common non-unit divisor. If `w ∈ F` satisfies `w · (y') ⊆ (y)` and
`(y) ⊆ w · (y')` (as `O`-submodules of `F`), then `w` is a unit of `O`.

Proof. Write `w = a / b` with `a`, `b` relatively prime
(`IsFractionRing.exists_reduced_fraction`). From `w y'_s ∈ O`: `b ∣ a y'_s`, so `b ∣ y'_s` for
all `s` and `b` is a unit; hence `w = a' ∈ O`. From `y_s ∈ a' · (y')`: `a' ∣ y_s` for all `s`,
so `a'` is a unit.
-/

namespace AJConjecture

/-- An element of the span of the images of the multiples `a t_s` is the image of a multiple
of `a`. -/
private theorem exists_eq_algebraMap_mul_of_mem_span {O F : Type*} [CommRing O] [CommRing F]
    [Algebra O F] {ι : Type*} (a : O) (t : ι → O) (z : F)
    (hz : z ∈ Submodule.span O (Set.range fun s ↦ algebraMap O F (a * t s))) :
    ∃ r : O, z = algebraMap O F (a * r) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, rfl⟩ := hz
    exact ⟨t s, rfl⟩
  | zero => exact ⟨0, by rw [mul_zero, map_zero]⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨r, rfl⟩ := hz
    obtain ⟨r', rfl⟩ := hz'
    exact ⟨r + r', by rw [mul_add, map_add]⟩
  | smul c z _ hz =>
    obtain ⟨r, rfl⟩ := hz
    exact ⟨c * r, by rw [Algebra.smul_def, ← map_mul, mul_left_comm]⟩

/-- If `w · (y') ⊆ (y)` and `(y) ⊆ w · (y')` for two families of a UFD without common non-unit
divisors, then `w` is a unit of the UFD. -/
theorem exists_unit_eq_of_mul_mem_span {O F : Type*} [CommRing O] [IsDomain O]
    [UniqueFactorizationMonoid O] [Field F] [Algebra O F] [IsFractionRing O F] {ι ι' : Type*}
    (y : ι → O) (y' : ι' → O) (hy : ∀ p : O, (∀ s, p ∣ y s) → IsUnit p)
    (hy' : ∀ p : O, (∀ s, p ∣ y' s) → IsUnit p) (w : F)
    (h₁ : ∀ s, w * algebraMap O F (y' s) ∈
      Submodule.span O (Set.range fun s ↦ algebraMap O F (y s)))
    (h₂ : ∀ s, algebraMap O F (y s) ∈
      Submodule.span O (Set.range fun s ↦ w * algebraMap O F (y' s))) :
    ∃ v : Oˣ, w = algebraMap O F v := by
  have hinj : Function.Injective (algebraMap O F) := IsFractionRing.injective O F
  obtain ⟨a, b, hab, hw⟩ := IsFractionRing.exists_reduced_fraction (A := O) w
  have hbF : algebraMap O F b ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.coe_ne_zero b)
  have hwb : w * algebraMap O F b = algebraMap O F a := by
    rw [← hw, IsLocalization.mk'_spec]
  have hbu : IsUnit (b : O) := by
    refine hy' _ fun s ↦ ?_
    obtain ⟨r, hr⟩ := exists_eq_algebraMap_mul_of_mem_span 1 y _
      (by simpa only [one_mul] using h₁ s)
    rw [one_mul] at hr
    have hab' : (b : O) * r = a * y' s := by
      apply hinj
      rw [map_mul, map_mul, ← hwb, ← hr]
      ring
    exact hab.symm.dvd_of_dvd_mul_left (Dvd.intro r hab')
  obtain ⟨bu, hbu'⟩ := hbu
  have hwa : w = algebraMap O F (a * ↑bu⁻¹) := by
    apply mul_right_cancel₀ hbF
    rw [hwb, ← map_mul, ← hbu', mul_assoc, Units.inv_mul, mul_one]
  have hau : IsUnit (a * ↑bu⁻¹) := by
    refine hy _ fun s ↦ ?_
    obtain ⟨r, hr⟩ := exists_eq_algebraMap_mul_of_mem_span (a * ↑bu⁻¹) y' _
      (by simpa only [hwa, ← map_mul] using h₂ s)
    exact ⟨r, hinj hr⟩
  obtain ⟨v, hv⟩ := hau
  exact ⟨v, by rw [hwa, hv]⟩

end AJConjecture
