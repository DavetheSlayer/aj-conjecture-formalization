import Mathlib

/-!
# A finitely generated fractional ideal containing `1` is `δ⁻¹` times a primitive ideal

Let `O` be a unique factorisation domain with fraction field `F` and `x` a finite family of `F`
whose `O`-span contains `1`. Then there are `δ ∈ O`, `δ ≠ 0`, and a family `y` of `O` with
`δ x_s = y_s` and such that every common divisor of the `y_s` is a unit.

Proof. Take a common denominator `γ₀` (`IsLocalization.exist_integer_multiples_of_finite`),
`γ₀ x_s = z_s ∈ O`, and `g = gcd(z_s) ≠ 0` (a `NormalizedGCDMonoid` structure exists on a UFD);
`z_s = g y_s`. From `1 = ∑ c_s x_s`: `γ₀ = g ∑ c_s y_s`, so `δ = ∑ c_s y_s` satisfies
`δ g = γ₀` and `δ x_s = y_s`. A common divisor `p` of the `y_s` gives `p g ∣ gcd(z_s) = g`.
-/

namespace AJConjecture

/-- A finite family of the fraction field of a UFD whose span contains `1` becomes, after
multiplication by a nonzero `δ ∈ O`, a family of `O` without common non-unit divisor. -/
theorem exists_primitive_scaling {O F : Type*} [CommRing O] [IsDomain O]
    [UniqueFactorizationMonoid O] [Field F] [Algebra O F] [IsFractionRing O F] {ι : Type*}
    [Finite ι] (x : ι → F) (h1 : (1 : F) ∈ Submodule.span O (Set.range x)) :
    ∃ (δ : O) (y : ι → O), δ ≠ 0 ∧ (∀ s, algebraMap O F δ * x s = algebraMap O F (y s)) ∧
      ∀ p : O, (∀ s, p ∣ y s) → IsUnit p := by
  classical
  cases nonempty_fintype ι
  obtain ⟨_⟩ := (inferInstance : Nonempty (NormalizedGCDMonoid O))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp h1
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
  choose z hz using hb
  have hinj : Function.Injective (algebraMap O F) := IsFractionRing.injective O F
  have hb0 : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨g, hg⟩ : ∃ g : O, g = Finset.univ.gcd z := ⟨_, rfl⟩
  have hgz : ∀ s, g ∣ z s := fun s ↦ hg ▸ Finset.gcd_dvd (Finset.mem_univ s)
  choose y hy using hgz
  have hγ : (b : O) = g * ∑ s, c s * y s := by
    apply hinj
    calc algebraMap O F b = (b : O) • (1 : F) := by rw [Algebra.smul_def, mul_one]
      _ = ∑ s, c s • algebraMap O F (z s) := by
          rw [← hc, Finset.smul_sum]
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          rw [smul_comm, hz]
      _ = algebraMap O F (g * ∑ s, c s * y s) := by
          rw [Finset.mul_sum, map_sum]
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          rw [Algebra.smul_def, hy s, ← map_mul, mul_left_comm]
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hγ
    exact hb0 hγ
  refine ⟨∑ s, c s * y s, y, ?_, fun s ↦ ?_, fun p hp ↦ ?_⟩
  · intro h
    rw [h, mul_zero] at hγ
    exact hb0 hγ
  · have hgF : algebraMap O F g ≠ 0 := (map_ne_zero_iff _ hinj).mpr hg0
    apply mul_left_cancel₀ hgF
    rw [← mul_assoc, ← map_mul, ← hγ, ← map_mul, ← hy, hz, Algebra.smul_def]
  · have hdvd : g * p ∣ g * 1 := by
      rw [mul_one]
      conv_rhs => rw [hg]
      refine Finset.dvd_gcd fun s _ ↦ ?_
      rw [hy s]
      exact mul_dvd_mul_left g (hp s)
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_left hg0).mp hdvd)

end AJConjecture
