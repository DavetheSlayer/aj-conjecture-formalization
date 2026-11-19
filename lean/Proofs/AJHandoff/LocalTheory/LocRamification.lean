import Mathlib
import AJHandoff.LocalTheory.LocResidue

/-!
# I-GAUGE: ramified meridians multiply the residue

Pulling back a one-form `f(z) dz` along the ramified chart `z = z₀ + w^e` (`e ≥ 1`) gives
`f(z₀ + w^e) e w^(e-1) dw`, whose residue at `w = 0` is `e` times the residue of `f` at `z₀`. In
the normalized index the lifted vector field is `c z/(e w^(e-1)) d/dw`, which has a pole at
`w = 0` for `e > 1`: the joint-ring hypothesis is not preserved, and no ramified-pullback
invariance or factor exclusion is asserted. In particular a half-integral index becomes integral
under a degree-two ramification (see `LocWeakControl`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The substitution `z ↦ z₀ + w^e`, `e ≥ 1`, maps nonzero polynomials to nonzero polynomials. -/
private theorem nonZeroDivisors_le_comap_compRingHom_ramify (z₀ : ℂ) {e : ℕ} (he : 0 < e) :
    nonZeroDivisors ℂ[X] ≤
      (nonZeroDivisors ℂ[X]).comap (Polynomial.compRingHom (C z₀ + X ^ e : ℂ[X])) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  intro h
  rcases comp_eq_zero_iff.1 h with h | ⟨-, h⟩
  · exact nonZeroDivisors.ne_zero hp h
  · have := congrArg natDegree h
    rw [natDegree_C, natDegree_C_add, natDegree_X_pow] at this
    omega

/-- The substitution `z ↦ z₀ + w^e` on `ℂ(z)`. -/
def ratRamify (z₀ : ℂ) (e : ℕ) (he : 0 < e) : RatFunc ℂ →+* RatFunc ℂ :=
  RatFunc.mapRingHom (Polynomial.compRingHom (C z₀ + X ^ e : ℂ[X]))
    (nonZeroDivisors_le_comap_compRingHom_ramify z₀ he)

/-- The substitution `z ↦ z₀ + w^e` on polynomials. -/
private theorem ratRamify_algebraMap (z₀ : ℂ) (e : ℕ) (he : 0 < e) (p : ℂ[X]) :
    ratRamify z₀ e he (algebraMap ℂ[X] (RatFunc ℂ) p) =
      algebraMap ℂ[X] (RatFunc ℂ) (p.comp (C z₀ + X ^ e)) := by
  have h := RatFunc.map_apply_div (Polynomial.compRingHom (C z₀ + X ^ e : ℂ[X]))
    (nonZeroDivisors_le_comap_compRingHom_ramify z₀ he) p 1
  simp only [map_one, div_one] at h
  exact h

/-- A ramified pullback of degree `e` multiplies the residue by `e`. -/
theorem hasSimpleResidue_ramify {f : RatFunc ℂ} {z₀ ι : ℂ} (hf : HasSimpleResidue f z₀ ι)
    {e : ℕ} (he : 0 < e) :
    HasSimpleResidue (ratRamify z₀ e he f * (e : RatFunc ℂ) * RatFunc.X ^ (e - 1)) 0 (e * ι) := by
  obtain ⟨a, b, hb, hab⟩ := hf
  have hab' := congrArg (ratRamify z₀ e he) hab
  have hX : ratRamify z₀ e he (RatFunc.X - RatFunc.C z₀) = RatFunc.X ^ e := by
    rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub, ratRamify_algebraMap,
      sub_comp, X_comp, C_comp, add_sub_cancel_left, map_pow, RatFunc.algebraMap_X]
  have hC : ratRamify z₀ e he (RatFunc.C ι) = RatFunc.C ι := by
    rw [← RatFunc.algebraMap_C, ratRamify_algebraMap, C_comp]
  rw [map_mul, map_sub, map_div₀, hX, hC, ratRamify_algebraMap, ratRamify_algebraMap] at hab'
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  refine ⟨C ((n + 1 : ℕ) : ℂ) * X ^ n * a.comp (C z₀ + X ^ (n + 1)),
    b.comp (C z₀ + X ^ (n + 1)), ?_, ?_⟩
  · simpa [eval_comp] using hb
  · have hX0 : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
    rw [Nat.add_sub_cancel, map_zero, sub_zero, map_mul (algebraMap ℂ[X] (RatFunc ℂ)), ← hab']
    simp only [map_mul, map_pow, map_natCast, RatFunc.algebraMap_X]
    field_simp
    ring

end AJConjecture
