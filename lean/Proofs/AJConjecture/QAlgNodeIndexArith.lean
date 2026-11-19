import Mathlib

/-!
# From the residue identity to the divisibility statement

Let `μ = X - m₀`, `Δ = μ^(2a) r₀ r` with `r₀(m₀) r(m₀) ≠ 0`, `s(m₀) ≠ 0`,
`μ s N = μ^(2a) y` and `Θ y(m₀) + (Ω - Θ m₀) r₀(m₀) r(m₀) s(m₀) = 0`. Then
`μ^(k+1) ∣ Θ (μ N - m₀ Δ) + Ω Δ` with `k` the multiplicity of `m₀` in `Δ`.

Proof. `k = 2a` (`Polynomial.rootMultiplicity_X_sub_C_pow`-type lemmas, or
`Polynomial.le_rootMultiplicity_iff` in both directions with `Polynomial.dvd_iff_isRoot`).
`s · (Θ (μ N - m₀ Δ) + Ω Δ) = μ^(2a) (Θ y + (Ω - Θ m₀) r₀ r s)` and the bracket vanishes at
`m₀`, so it is divisible by `μ`. Since `s(m₀) ≠ 0`, `s` is coprime to `μ^(2a+1)`
(`Polynomial.irreducible_X_sub_C`, `IsCoprime.pow_left`), and the factor `s` can be removed
(`IsCoprime.dvd_of_dvd_mul_left`).
-/

open Polynomial

namespace AJConjecture

/-- If `Δ = μ^(2a) r₀ r`, `μ s N = μ^(2a) y` with `r₀, r, s` units at `m₀`, and
`Θ y(m₀) + (Ω - Θ m₀) r₀(m₀) r(m₀) s(m₀) = 0`, then
`μ^(ord Δ + 1) ∣ Θ (μ N - m₀ Δ) + Ω Δ`. -/
theorem pow_dvd_of_residue_identity {k : Type*} [Field k] {m₀ Θ Ω : k} {a : ℕ}
    {N Δ ss r0s rs y : k[X]} (hΔ : Δ = (X - C m₀) ^ (2 * a) * (r0s * rs))
    (hss : ss.eval m₀ ≠ 0) (hr0 : r0s.eval m₀ ≠ 0) (hrs : rs.eval m₀ ≠ 0)
    (hy : (X - C m₀) * (ss * N) = (X - C m₀) ^ (2 * a) * y)
    (hres : Θ * y.eval m₀ + (Ω - Θ * m₀) * (r0s.eval m₀ * rs.eval m₀ * ss.eval m₀) = 0) :
    (X - C m₀) ^ (Δ.rootMultiplicity m₀ + 1) ∣
      C Θ * ((X - C m₀) * N - C m₀ * Δ) + C Ω * Δ := by
  subst hΔ
  have hne : (r0s * rs).eval m₀ ≠ 0 := by
    rw [eval_mul]
    exact mul_ne_zero hr0 hrs
  have h0 : r0s * rs ≠ 0 := fun h ↦ hne (by rw [h, eval_zero])
  have hrm : ((X - C m₀) ^ (2 * a) * (r0s * rs)).rootMultiplicity m₀ = 2 * a := by
    rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero m₀)) h0),
      rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero hne, add_zero]
  rw [hrm]
  have hbr : (X - C m₀) ∣ C Θ * y + C (Ω - Θ * m₀) * (r0s * rs * ss) := by
    rw [dvd_iff_isRoot, IsRoot.def]
    simp only [eval_add, eval_mul, eval_C]
    exact hres
  have hmul : ss * (C Θ * ((X - C m₀) * N - C m₀ * ((X - C m₀) ^ (2 * a) * (r0s * rs))) +
        C Ω * ((X - C m₀) ^ (2 * a) * (r0s * rs))) =
      (X - C m₀) ^ (2 * a) * (C Θ * y + C (Ω - Θ * m₀) * (r0s * rs * ss)) := by
    rw [C_sub, C_mul]
    linear_combination C Θ * hy
  have hdvd : (X - C m₀) ^ (2 * a + 1) ∣
      ss * (C Θ * ((X - C m₀) * N - C m₀ * ((X - C m₀) ^ (2 * a) * (r0s * rs))) +
        C Ω * ((X - C m₀) ^ (2 * a) * (r0s * rs))) := by
    rw [hmul, pow_succ]
    exact mul_dvd_mul_left _ hbr
  have hcop : IsCoprime ((X - C m₀) ^ (2 * a + 1)) ss := by
    apply IsCoprime.pow_left
    exact (irreducible_X_sub_C m₀).coprime_iff_not_dvd.mpr (by rw [dvd_iff_isRoot]; exact hss)
  exact hcop.dvd_of_dvd_mul_left hdvd

end AJConjecture
