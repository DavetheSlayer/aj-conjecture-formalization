import Mathlib
import AJTwist.Exist.TwHXDegree

/-!
# The degree in `x` of the iterated adjoint of a polynomial in `J`

For a polynomial `ρ` in `J` alone (`ρ.map C`, of degree `0` in `x`; `swap (ρ.map C) = C ρ`,
`Polynomial.Bivariate.swap_map_C`), the `s`-th iterate of the cleared adjoint has degree at
most `2s` in `x`, and
`[x^(2s)] (twAdjoint d q)^[s] ρ = ∏_{u=1}^{s} (1 - q^u J) · ρ(q^s J)`.

Induction on `s` from `twH_natDegree_swap_twAdjoint_le` and `twH_coeff_swap_twAdjoint`
(`Function.iterate_succ_apply'`): composing the product for `s` with `J ↦ qJ` shifts the factors
`1 - q^u J` to `1 - q^(u+1) J` and `ρ(q^s J)` to `ρ(q^(s+1) J)`
(`Polynomial.prod_comp`, `Polynomial.comp_assoc`, `Finset.prod_range_succ'`).

In the manuscript's normalization: `𝒜_d^s(ρ) / x^s → q^(-ds) ∏_{u=1}^{s} (1 - q^u J) ρ(q^s J)`
as `x → ∞`. Checked in exact arithmetic for `s ≤ 4` (scratch `H/h02_sbp.py`, item (e)).
-/

open Polynomial Polynomial.Bivariate

noncomputable section

namespace AJConjecture

/-- The `s`-th iterate of the cleared adjoint of a polynomial in `J` has degree at most `2s`
in `x`. -/
theorem twH_natDegree_swap_iterate_twAdjoint_le {R : Type*} [CommRing R] (d : ℕ) (q : R)
    (s : ℕ) (ρ : R[X]) : (swap ((twAdjoint d q)^[s] (ρ.map C))).natDegree ≤ 2 * s := by
  induction s with
  | zero =>
    rw [Function.iterate_zero, id_eq, swap_map_C, natDegree_C]
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    exact (twH_natDegree_swap_twAdjoint_le d q _ ih).trans (by omega)

/-- The coefficient of `x^(2s)` of the `s`-th iterate of the cleared adjoint of a polynomial
`ρ` in `J`: `∏_{u<s} (1 - q^(u+1) J) · ρ(q^s J)`. -/
theorem twH_coeff_swap_iterate_twAdjoint {R : Type*} [CommRing R] (d : ℕ) (q : R) (s : ℕ)
    (ρ : R[X]) :
    (swap ((twAdjoint d q)^[s] (ρ.map C))).coeff (2 * s) =
      (∏ u ∈ Finset.range s, (1 - C (q ^ (u + 1)) * X)) * ρ.comp (C (q ^ s) * X) := by
  induction s with
  | zero =>
    rw [Function.iterate_zero, id_eq, swap_map_C, Nat.mul_zero, coeff_C_zero,
      Finset.prod_range_zero, one_mul, pow_zero, C_1, one_mul, comp_X]
  | succ s ih =>
    have h1 : ∀ u : ℕ, (1 - C (q ^ (u + 1)) * X : R[X]).comp (C q * X) =
        1 - C (q ^ (u + 1 + 1)) * X := by
      intro u
      rw [sub_comp, one_comp, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, ← pow_succ]
    have h2 : (C (q ^ s) * X : R[X]).comp (C q * X) = C (q ^ (s + 1)) * X := by
      rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, ← pow_succ]
    rw [Function.iterate_succ_apply', show 2 * (s + 1) = 2 * s + 2 by ring,
      twH_coeff_swap_twAdjoint d q _ (twH_natDegree_swap_iterate_twAdjoint_le d q s ρ), ih,
      mul_comp, prod_comp, comp_assoc, h2, Finset.prod_range_succ']
    simp only [h1, zero_add, pow_one]
    ring

end AJConjecture
