import Mathlib
import AJConjecture.QAlgNodeContentSplit

/-!
# The contents at `M = m₀` of a factorisation `β₀ P₀ = S₀ R₀`

Let `β₀ ∈ k[M]`, `β₀ ≠ 0`, and `P₀, S₀, R₀ ∈ k[M][L]` with `β₀ P₀ = S₀ R₀` and the fibre of `P₀`
at `M = m₀` not zero. With `μ = M - m₀`: `R₀ = μ^a R*`, `S₀ = μ^b S*`, `β₀ = μ^(a+b) β*`,
`β*(m₀) ≠ 0` and `β* P₀ = S* R*`.

Proof. `S₀, R₀ ≠ 0`; split them and `β₀` (`exists_eq_C_pow_mul_fibre_ne_zero`,
`Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`): `β₀ = μ^c β*`. Then
`μ^c (β* P₀) = μ^(a+b) (S* R*)` and both `β* P₀` and `S* R*` have nonzero fibre (`k[L]` is a
domain), so `c = a + b` and `β* P₀ = S* R*` (`eq_C_pow_mul_of_C_pow_mul_eq` in both directions).
-/

open Polynomial

namespace AJConjecture

/-- The contents at `M = m₀` of the two factors of `β₀ P₀ = S₀ R₀`, when the fibre of `P₀` is
not zero, add up to the multiplicity of `m₀` in `β₀`. -/
theorem exists_content_of_mul_eq {k : Type*} [Field k] {m₀ : k} {β₀ : k[X]}
    {P₀ S₀ R₀ : k[X][X]} (hβ : β₀ ≠ 0) (hP : P₀.map (Polynomial.evalRingHom m₀) ≠ 0)
    (h : C β₀ * P₀ = S₀ * R₀) :
    ∃ (a b : ℕ) (βs : k[X]) (Ss Rs : k[X][X]),
      R₀ = C ((X - C m₀) ^ a) * Rs ∧ S₀ = C ((X - C m₀) ^ b) * Ss ∧
      β₀ = (X - C m₀) ^ (a + b) * βs ∧ βs.eval m₀ ≠ 0 ∧ C βs * P₀ = Ss * Rs := by
  have hP0 : P₀ ≠ 0 := fun h0 ↦ hP (by rw [h0, Polynomial.map_zero])
  have hSR : S₀ * R₀ ≠ 0 := h ▸ mul_ne_zero (C_ne_zero.mpr hβ) hP0
  obtain ⟨a, Rs, rfl, hRs⟩ := exists_eq_C_pow_mul_fibre_ne_zero m₀ (right_ne_zero_of_mul hSR)
  obtain ⟨b, Ss, rfl, hSs⟩ := exists_eq_C_pow_mul_fibre_ne_zero m₀ (left_ne_zero_of_mul hSR)
  obtain ⟨βs, hβs, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd β₀ hβ m₀
  have hβm : βs.eval m₀ ≠ 0 := fun h0 ↦ hdvd (dvd_iff_isRoot.mpr h0)
  have hfibβ : (C βs * P₀).map (Polynomial.evalRingHom m₀) ≠ 0 := by
    rw [Polynomial.map_mul, Polynomial.map_C, coe_evalRingHom]
    exact mul_ne_zero (C_ne_zero.mpr hβm) hP
  have hfibSR : (Ss * Rs).map (Polynomial.evalRingHom m₀) ≠ 0 := by
    rw [Polynomial.map_mul]
    exact mul_ne_zero hSs hRs
  have heq : C ((X - C m₀) ^ β₀.rootMultiplicity m₀) * (C βs * P₀) =
      C ((X - C m₀) ^ (a + b)) * (Ss * Rs) := by
    rw [← mul_assoc, ← C_mul, ← hβs, h, pow_add, C_mul]
    ring
  obtain ⟨h1, -⟩ := eq_C_pow_mul_of_C_pow_mul_eq heq hfibSR
  obtain ⟨h2, h3⟩ := eq_C_pow_mul_of_C_pow_mul_eq heq.symm hfibβ
  have hc : β₀.rootMultiplicity m₀ = a + b := le_antisymm h1 h2
  refine ⟨a, b, βs, Ss, Rs, rfl, rfl, ?_, hβm, ?_⟩
  · rw [← hc]
    exact hβs
  · rw [h3, hc, Nat.sub_self, pow_zero, C_1, one_mul]

end AJConjecture
