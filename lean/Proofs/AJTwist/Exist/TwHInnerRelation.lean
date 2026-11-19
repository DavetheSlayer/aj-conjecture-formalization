import Mathlib
import AJTwist.Exist.TwHGensStep
import AJTwist.Exist.TwHSpanRelation
import AJTwist.Exist.TwHClearDenoms

/-!
# The inner relation: a polynomial recurrence in `V` for the cyclotomic coefficients

For every chirality `η`, all natural `r`, `s` and every twist `ℓ`, the cyclotomic coefficients
`D = pairQCycloCoeff (twInput η r s ℓ)` of the twisted input satisfy a nontrivial relation
`∑_{i ≤ R} ρ_i(q^j) (V^i D)_j = 0` at **every** `j ≥ 0`, with polynomials `ρ_i` in `J = q^j`.

* `twH_exists_relation_field`: coefficients in `ℚ(t)[J]`. The `R + 1` sequences `V^i D`,
  `i ≤ R`, lie in the saturated span of the `R = |a| + 2|ℓ| + 2` generators `twHGen`
  (`twHSpan_gen_iterate`), so `twHSpan_exists_relation` applies.
* `twH_exists_inner_relation`: coefficients in `ℤ[t][J]`
  (`twH_exists_map_twTHom_eq_family`: multiply the relation by the common denominator; the
  family is extended by zero to all natural indices).

This is the statement that replaces `q`-holonomicity of the inner sum. Checked numerically
(scratch `H/h03_pipeline.py`): for 22 choices of `(η, r, s, ℓ)` (pairs `(2,3)`, `(2,5)`,
`(3,4)`, `(3,5)`, degenerate pairs with `r s = 0` or `r = s`, twists between `-6` and `13`,
including `ℓ = 0`) a relation of order `≤ |a| + 2|ℓ| + 2` and of small degree in `J` was found
by linear algebra in a prime field, from a number of values of `j` exceeding the number of
unknown coefficients by 25, and it holds at 15 further values of `j`; the value `j = 0` is
among the equations. The span machinery itself was executed literally in exact rationals on
seven small cases (scratch `H/h07_span.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The inner relation with coefficients in `ℚ(t)[J]`. -/
theorem twH_exists_relation_field (η : Bool) (r s : ℕ) (ℓ : ℤ) :
    ∃ (R : ℕ) (ρ : Fin (R + 1) → (RatFunc ℚ)[X]), ρ ≠ 0 ∧ ∀ j : ℕ,
      ∑ i, (ρ i).eval (qParam ^ j) *
        cycloStep^[(i : ℕ)] (pairQCycloCoeff (twInput η r s ℓ)) j = 0 := by
  obtain ⟨ρ, hρ, hrel⟩ := twHSpan_exists_relation (twHGen η r s ℓ)
    (fun i ↦ cycloStep^[(i : ℕ)] (pairQCycloCoeff (twInput η r s ℓ)))
    (fun i ↦ twHSpan_gen_iterate η r s ℓ i)
  exact ⟨_, ρ, hρ, hrel⟩

/-- The inner relation with coefficients in `ℤ[t][J]`: polynomials `ρ_0, …, ρ_R`, not all
zero, with `∑_{i ≤ R} ρ_i(q^j) (V^i D)_j = 0` for every `j`. -/
theorem twH_exists_inner_relation (η : Bool) (r s : ℕ) (ℓ : ℤ) :
    ∃ (R : ℕ) (ρ : ℕ → ℤ[X][X]), (∃ i, i ≤ R ∧ ρ i ≠ 0) ∧ ∀ j : ℕ,
      ∑ i ∈ Finset.range (R + 1), ((ρ i).map twTHom).eval (qParam ^ j) *
        cycloStep^[i] (pairQCycloCoeff (twInput η r s ℓ)) j = 0 := by
  obtain ⟨R, ρ, hρ, hrel⟩ := twH_exists_relation_field η r s ℓ
  obtain ⟨b, ρ', hb, hmap⟩ := twH_exists_map_twTHom_eq_family ρ
  refine ⟨R, fun i ↦ if h : i < R + 1 then ρ' ⟨i, h⟩ else 0, ?_, fun j ↦ ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hρ
    refine ⟨i, Nat.lt_succ_iff.mp i.isLt, ?_⟩
    beta_reduce
    rw [dite_eq_left i.isLt, Fin.eta]
    intro h0
    have h1 := hmap i
    rw [h0, Polynomial.map_zero] at h1
    rcases mul_eq_zero.mp h1.symm with h2 | h2
    · exact hb (C_eq_zero.mp h2)
    · exact hi h2
  · rw [← Fin.sum_univ_eq_sum_range (fun i ↦
      ((if h : i < R + 1 then ρ' ⟨i, h⟩ else 0).map twTHom).eval (qParam ^ j) *
        cycloStep^[i] (pairQCycloCoeff (twInput η r s ℓ)) j) (R + 1)]
    have hterm : ∀ i : Fin (R + 1),
        ((if h : (i : ℕ) < R + 1 then ρ' ⟨i, h⟩ else 0).map twTHom).eval (qParam ^ j) *
          cycloStep^[(i : ℕ)] (pairQCycloCoeff (twInput η r s ℓ)) j =
        twTHom b * ((ρ i).eval (qParam ^ j) *
          cycloStep^[(i : ℕ)] (pairQCycloCoeff (twInput η r s ℓ)) j) := by
      intro i
      rw [dite_eq_left i.isLt, Fin.eta, hmap, eval_mul, eval_C, mul_assoc]
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.mul_sum, hrel j, mul_zero]

end AJConjecture
