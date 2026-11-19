import Mathlib

/-!
# The residue of a logarithmic derivative is an integer

If `N/D = A/u + 2X (g₂'/g₂ - g₁'/g₁)` with `u`, `g₂` not vanishing at `m₀`, then `N/D` has at
most a simple pole at `m₀`, with residue `-2 m₀ j`, `j` the multiplicity of `m₀` as a root of
`g₁`. In polynomial form, with `μ = X - m₀` and `k` the multiplicity of `m₀` in `D`:
`μ^(k+1) ∣ μ N + 2 j m₀ D`.

Proof. Write `g₁ = μ^j h`, `h(m₀) ≠ 0`. Then
`μ (g₁ g₂' - g₁' g₂) = μ^j (μ (h g₂' - h' g₂) - j h g₂)`. Multiply the hypothesis by `μ` and
cancel `μ^j`: `μ N (u h g₂) = D (μ h g₂ A + 2X u (μ (h g₂' - h' g₂) - j h g₂))`, which is
congruent to `-2 j m₀ D (u h g₂)` modulo `μ^(k+1)` because `μ^k ∣ D` and `X ≡ m₀`. Finally
`u h g₂` is coprime to `μ`. (If `D = 0` then `N = 0` and there is nothing to prove.)
-/

open Polynomial

namespace AJConjecture

/-- `μ (μ^j q)' = μ^j (j q + μ q')` for `μ = X - m₀`. -/
private theorem X_sub_C_mul_derivative_pow_mul_logDerivResidue (m₀ : ℂ) (j : ℕ) (q : ℂ[X]) :
    (X - C m₀) * derivative ((X - C m₀) ^ j * q) =
      (X - C m₀) ^ j * (C (j : ℂ) * q + (X - C m₀) * derivative q) := by
  rw [derivative_mul, derivative_X_sub_C_pow]
  cases j with
  | zero =>
    rw [Nat.cast_zero, C_0, zero_mul, zero_mul]
    ring
  | succ j =>
    rw [Nat.add_sub_cancel, pow_succ]
    ring

/-- The identity of the statement after `g₁ = μ^j q` has been substituted and `μ^j` cancelled:
`μ N (u q g₂) = D (μ q g₂ A + 2X u (μ (q g₂' - q' g₂) - j q g₂))`. -/
private theorem logDeriv_identity_cancel_pow_logDerivResidue {m₀ : ℂ} {N D q g₂ u A : ℂ[X]}
    (j : ℕ)
    (h : N * (u * ((X - C m₀) ^ j * q) * g₂) =
      D * ((X - C m₀) ^ j * q * g₂ * A + 2 * X * u * ((X - C m₀) ^ j * q * derivative g₂ -
        derivative ((X - C m₀) ^ j * q) * g₂))) :
    (X - C m₀) * N * (u * q * g₂) =
      D * ((X - C m₀) * q * g₂ * A + 2 * X * u *
        ((X - C m₀) * (q * derivative g₂ - derivative q * g₂) - C (j : ℂ) * q * g₂)) := by
  have hder := X_sub_C_mul_derivative_pow_mul_logDerivResidue m₀ j q
  have hpow : (X - C m₀ : ℂ[X]) ^ j ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero m₀)
  apply mul_left_cancel₀ hpow
  linear_combination (X - C m₀) * h - (2 * X * u * D * g₂) * hder

/-- A rational function of the form `A/u + 2X (g₂'/g₂ - g₁'/g₁)` has residue `-2 m₀ j` at `m₀`,
`j ∈ ℕ`, when `u` and `g₂` do not vanish at `m₀`. -/
theorem exists_nat_pow_dvd_of_logDeriv_identity {m₀ : ℂ} {N D g₁ g₂ u A : ℂ[X]} (hg₁ : g₁ ≠ 0)
    (hg₂ : g₂.eval m₀ ≠ 0) (hu : u.eval m₀ ≠ 0)
    (h : N * (u * g₁ * g₂) =
      D * (g₁ * g₂ * A + 2 * X * u * (g₁ * derivative g₂ - derivative g₁ * g₂))) :
    ∃ j : ℕ, (X - C m₀) ^ (D.rootMultiplicity m₀ + 1) ∣ (X - C m₀) * N + C (2 * j * m₀) * D := by
  obtain ⟨q, hq, hqdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd g₁ hg₁ m₀
  obtain ⟨j, hj⟩ : ∃ j, j = g₁.rootMultiplicity m₀ := ⟨_, rfl⟩
  rw [← hj] at hq
  subst hq
  refine ⟨j, ?_⟩
  have hc := logDeriv_identity_cancel_pow_logDerivResidue j h
  have hC : (C (2 * (j : ℂ) * m₀) : ℂ[X]) = 2 * C (j : ℂ) * C m₀ := by
    rw [C_mul, C_mul, C_ofNat]
  have hw : ¬(X - C m₀) ∣ u * q * g₂ := by
    intro hdvd
    rcases (prime_X_sub_C m₀).dvd_or_dvd hdvd with h1 | h1
    · rcases (prime_X_sub_C m₀).dvd_or_dvd h1 with h2 | h2
      · exact hu (dvd_iff_isRoot.mp h2)
      · exact hqdvd h2
    · exact hg₂ (dvd_iff_isRoot.mp h1)
  obtain ⟨D', hD'⟩ := pow_rootMultiplicity_dvd D m₀
  generalize D.rootMultiplicity m₀ = k at hD' ⊢
  apply (prime_X_sub_C m₀).pow_dvd_of_dvd_mul_right _ hw
  refine ⟨D' * (q * g₂ * A + 2 * X * u * (q * derivative g₂ - derivative q * g₂) -
    2 * C (j : ℂ) * (u * q * g₂)), ?_⟩
  rw [hC]
  linear_combination hc + (X - C m₀) * (q * g₂ * A +
    2 * X * u * (q * derivative g₂ - derivative q * g₂) - 2 * C (j : ℂ) * (u * q * g₂)) * hD'

end AJConjecture
