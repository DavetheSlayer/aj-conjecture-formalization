import Mathlib
import AJConjecture.QAlgNodeJet

/-!
# The coboundary can be chosen nonzero at `t = -1`

In `r_0 γ₁ σ(γ₂) v₂ = r_d v₁ σ(γ₁) γ₂` the element `γ₁ ≠ 0` may be divided by the largest power
of `t + 1` that divides it: `σ(t + 1) = t + 1`, so the power cancels from both sides, and the
quotient has nonzero value at `t = -1` (`complexSpec f = 0` iff `C (X + 1) ∣ f`).
-/

open Polynomial

namespace AJConjecture

/-- A polynomial of `ℂ[t][M]` whose value at `t = -1` is zero is divisible by `t + 1`. -/
private theorem C_X_sub_C_dvd_of_complexSpec_eq_zero {f : ℂ[X][X]} (hf : complexSpec f = 0) :
    C (X - C (-1 : ℂ)) ∣ f := by
  rw [C_dvd_iff_dvd_coeff]
  intro i
  rw [dvd_iff_isRoot, IsRoot.def]
  have h := congrArg (fun q : ℂ[X] ↦ q.coeff i) hf
  simpa only [complexSpec, coe_mapRingHom, coeff_map, coe_evalRingHom, coeff_zero] using h

/-- In the coboundary identity `γ₁` can be replaced by an element whose value at `t = -1` is
not zero. -/
theorem exists_coboundary_complexSpec_ne_zero {r₀ r₁ γ₁ γ₂ v₁ v₂ : ℂ[X][X]} (hγ₁ : γ₁ ≠ 0)
    (h : r₀ * γ₁ * complexShift γ₂ * v₂ = r₁ * v₁ * complexShift γ₁ * γ₂) :
    ∃ γ₁' : ℂ[X][X], complexSpec γ₁' ≠ 0 ∧
      r₀ * γ₁' * complexShift γ₂ * v₂ = r₁ * v₁ * complexShift γ₁' * γ₂ := by
  have hq : ¬IsUnit (C (X - C (-1 : ℂ)) : ℂ[X][X]) := by
    rw [isUnit_C]
    exact not_isUnit_X_sub_C _
  obtain ⟨n, g, hg, rfl⟩ := WfDvdMonoid.max_power_factor' hγ₁ hq
  refine ⟨g, fun h0 ↦ hg (C_X_sub_C_dvd_of_complexSpec_eq_zero h0), ?_⟩
  have hshift : complexShift (C (X - C (-1 : ℂ))) = C (X - C (-1 : ℂ)) := by
    have hcomp : complexShift (C (X - C (-1 : ℂ))) =
        (C (X - C (-1 : ℂ)) : ℂ[X][X]).comp (C (X ^ 2) * X) := rfl
    rw [hcomp, C_comp]
  have hpow : (C (X - C (-1 : ℂ)) : ℂ[X][X]) ^ n ≠ 0 :=
    left_ne_zero_of_mul hγ₁
  rw [map_mul, map_pow, hshift] at h
  apply mul_left_cancel₀ hpow
  linear_combination h

end AJConjecture
