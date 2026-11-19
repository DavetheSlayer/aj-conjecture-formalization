import Mathlib

/-!
# The residue of `A/u + κ z (g₁'/g₁ - g₂'/g₂)`

If `N/Δ = A/u + κ z (g₁'/g₁ - g₂'/g₂)` with `u(z₀) ≠ 0`, then `N/Δ` has at most a simple pole at
`z₀`, with residue `κ z₀ (ord_{z₀} g₁ - ord_{z₀} g₂)`. In polynomial form, with `μ = z - z₀` and
`k = ord_{z₀} Δ`: `μ^(k+1) ∣ μ N - κ z₀ (ord g₁ - ord g₂) Δ`.

This generalizes the library's `exists_nat_pow_dvd_of_logDeriv_identity` (where `κ = -2`,
`g₂(z₀) ≠ 0`): here both `g₁` and `g₂` may vanish at `z₀`, so the integer may have either sign.
Proof: write `g_i = μ^(j_i) h_i` and argue as in the library.
-/

open Polynomial

namespace AJConjecture

/-- `μ (μ^j q)' = μ^j (j q + μ q')` for `μ = X - z₀`. -/
private theorem X_sub_C_mul_derivative_pow_mul_logDerivInt (z₀ : ℂ) (j : ℕ) (q : ℂ[X]) :
    (X - C z₀) * derivative ((X - C z₀) ^ j * q) =
      (X - C z₀) ^ j * (C (j : ℂ) * q + (X - C z₀) * derivative q) := by
  rw [derivative_mul, derivative_X_sub_C_pow]
  cases j with
  | zero =>
    rw [Nat.cast_zero, C_0, zero_mul, zero_mul]
    ring
  | succ j =>
    rw [Nat.add_sub_cancel, pow_succ]
    ring

/-- The identity of the statement after `g_i = μ^(j_i) q_i` has been substituted and
`μ^(j₁ + j₂)` cancelled. -/
private theorem logDeriv_identity_cancel_pow_logDerivInt {z₀ κ : ℂ} {N Δ q₁ q₂ u A : ℂ[X]}
    (j₁ j₂ : ℕ)
    (h : N * (u * ((X - C z₀) ^ j₁ * q₁) * ((X - C z₀) ^ j₂ * q₂)) =
      Δ * ((X - C z₀) ^ j₁ * q₁ * ((X - C z₀) ^ j₂ * q₂) * A + C κ * X * u *
        (derivative ((X - C z₀) ^ j₁ * q₁) * ((X - C z₀) ^ j₂ * q₂) -
          (X - C z₀) ^ j₁ * q₁ * derivative ((X - C z₀) ^ j₂ * q₂)))) :
    (X - C z₀) * N * (u * q₁ * q₂) =
      Δ * ((X - C z₀) * q₁ * q₂ * A + C κ * X * u *
        ((C (j₁ : ℂ) - C (j₂ : ℂ)) * q₁ * q₂ +
          (X - C z₀) * (derivative q₁ * q₂ - q₁ * derivative q₂))) := by
  have h₁ := X_sub_C_mul_derivative_pow_mul_logDerivInt z₀ j₁ q₁
  have h₂ := X_sub_C_mul_derivative_pow_mul_logDerivInt z₀ j₂ q₂
  have hpow : (X - C z₀ : ℂ[X]) ^ (j₁ + j₂) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero z₀)
  apply mul_left_cancel₀ hpow
  rw [pow_add]
  linear_combination (X - C z₀) * h +
    (Δ * C κ * X * u * ((X - C z₀) ^ j₂ * q₂)) * h₁ -
    (Δ * C κ * X * u * ((X - C z₀) ^ j₁ * q₁)) * h₂

theorem pow_dvd_of_logDeriv_identity_int {z₀ κ : ℂ} {N Δ g₁ g₂ u A : ℂ[X]} (hg₁ : g₁ ≠ 0)
    (hg₂ : g₂ ≠ 0) (hu : u.eval z₀ ≠ 0)
    (h : N * (u * g₁ * g₂) =
      Δ * (g₁ * g₂ * A + C κ * X * u * (derivative g₁ * g₂ - g₁ * derivative g₂))) :
    (X - C z₀) ^ (Δ.rootMultiplicity z₀ + 1) ∣
      (X - C z₀) * N -
        C (κ * z₀ * ((g₁.rootMultiplicity z₀ : ℂ) - (g₂.rootMultiplicity z₀ : ℂ))) * Δ := by
  obtain ⟨q₁, hq₁, hq₁dvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd g₁ hg₁ z₀
  obtain ⟨q₂, hq₂, hq₂dvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd g₂ hg₂ z₀
  generalize g₁.rootMultiplicity z₀ = j₁ at hq₁ ⊢
  generalize g₂.rootMultiplicity z₀ = j₂ at hq₂ ⊢
  subst hq₁ hq₂
  have hc := logDeriv_identity_cancel_pow_logDerivInt j₁ j₂ h
  have hw : ¬(X - C z₀) ∣ u * q₁ * q₂ := by
    intro hdvd
    rcases (prime_X_sub_C z₀).dvd_or_dvd hdvd with h1 | h1
    · rcases (prime_X_sub_C z₀).dvd_or_dvd h1 with h2 | h2
      · exact hu (dvd_iff_isRoot.mp h2)
      · exact hq₁dvd h2
    · exact hq₂dvd h1
  have hC : (C (κ * z₀ * ((j₁ : ℂ) - (j₂ : ℂ))) : ℂ[X]) =
      C κ * C z₀ * (C (j₁ : ℂ) - C (j₂ : ℂ)) := by
    rw [C_mul, C_mul, C_sub]
  obtain ⟨D', hD'⟩ := pow_rootMultiplicity_dvd Δ z₀
  generalize Δ.rootMultiplicity z₀ = k at hD' ⊢
  apply (prime_X_sub_C z₀).pow_dvd_of_dvd_mul_right _ hw
  refine ⟨D' * (q₁ * q₂ * A + C κ * X * u * (derivative q₁ * q₂ - q₁ * derivative q₂) +
    C κ * (C (j₁ : ℂ) - C (j₂ : ℂ)) * (u * q₁ * q₂)), ?_⟩
  rw [hC]
  linear_combination hc + (X - C z₀) * (q₁ * q₂ * A +
    C κ * X * u * (derivative q₁ * q₂ - q₁ * derivative q₂) +
    C κ * (C (j₁ : ℂ) - C (j₂ : ℂ)) * (u * q₁ * q₂)) * hD' 

end AJConjecture
