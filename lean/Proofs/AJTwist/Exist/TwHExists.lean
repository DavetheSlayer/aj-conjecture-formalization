import Mathlib
import AJConjecture.QAlgGaugeToUnreduced
import AJConjecture.QAlgKillFiniteDefect
import AJConjecture.QAlgTwoSidedAnnihilator
import AJHandoff.TorusQuantum.PairQFormulaBasic
import AJTwist.Exist.TwHInnerRelation
import AJTwist.Exist.TwHTail

/-!
# Existence of a nonzero recurrence for the twisted satellite sequences

Source: revision 5, Theorem 1.1 and Section 8.1 (`conclusion.tex`), first paragraph: "By the
`q`-holonomicity theorem for the unreduced colored Jones sequence [S02, Thm. 1], the actual
`Φ_S` has a nonzero positive-tail annihilator. … Take the original row and its reflection, form
a nonzero common left multiple, and clear its coefficient denominators. Both tails vanish. The
finitely many remaining colors are killed by the left scalar".

Here the citation is replaced by a proof, for every chirality `η`, all natural `r`, `s` and
every twist `ℓ` (no hypothesis: neither coprimality nor `r < s` nor `ℓ ≠ 0` is used).

1. *Inner finite rank* (`twH_exists_inner_relation`). The Gaussian periods
   `𝔊^(c)_j = ∑_n K_{j,n} q^(ℓ n(n+1) + c n)` satisfy a contiguity relation in `c` and
   `V 𝔊^(c) = 𝔊^(c+1) + q⁻¹ 𝔊^(c-1)`; with the inner equation `p_a D = e` of the manuscript
   (eq. (innerforcing)) the sequences `V^i D` lie in a module of rank `≤ |a| + 2|ℓ| + 2` over
   `ℚ(t)[J]`, so `∑_{i ≤ R} ρ_i(q^j) (V^i D)_j = 0` for all `j`, with `ρ ≠ 0`.
2. *Outer transfer* (`twH_exists_tail_annihilator_of_relation`). Adjunction against the kernel
   of a large pole window and the pole basis turn the relation into `P F = 0` at the colours
   `n ≥ 1`, with `P` the Cramer operator of the cleared target; `P ≠ 0` because the adjoint
   raises the degree in `x` by exactly one.
3. *Tail to all integers* (`twH_exists_annihilator_of_tail`, the library's
   `exists_annihilator_outside_finite_of_even`, `exists_C_mul_annihilator_of_outside_finite`,
   `exists_gauge_quantumInt_mul`, exactly as in `pairQ_exists_annihilator`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A nonzero operator annihilates the even reduced sequence of the twisted satellite at all
colours `n ≥ 1`. -/
theorem twH_exists_tail_annihilator (η : Bool) (r s : ℕ) (ℓ : ℤ) :
    ∃ G : RecOp, G ≠ 0 ∧ ∀ n : ℤ, 1 ≤ n → opApplyField G (twReducedEven η r s ℓ) n = 0 := by
  obtain ⟨R, ρ, hρ, hrel⟩ := twH_exists_inner_relation η r s ℓ
  exact twH_exists_tail_annihilator_of_relation (twInput η r s ℓ) R ρ hρ hrel

/-- From a tail annihilator of the even reduced sequence of an arbitrary input to an annihilator
of the unreduced formula at every integer colour. -/
theorem twH_exists_annihilator_of_tail (u : ℕ → RatFunc ℚ) {G : RecOp} (hG : G ≠ 0) {n₀ : ℤ}
    (h : ∀ n : ℤ, n₀ ≤ n → opApplyField G (pairQReducedFormulaEven u) n = 0) :
    ∃ Q : RecOp, Q ≠ 0 ∧ ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (pairQFormula u) n = 0 := by
  obtain ⟨Q₀, hQ₀, N, hN⟩ :=
    exists_annihilator_outside_finite_of_even (pairQReducedFormulaEven_neg u) hG h
  obtain ⟨c, hc, hc0⟩ := exists_C_mul_annihilator_of_outside_finite hN
  obtain ⟨Q, hQ, hQann⟩ := exists_gauge_quantumInt_mul (Polynomial.C c * Q₀)
  have hne : Polynomial.C c * Q₀ ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hQ₀
  have hfun : pairQFormula u = fun m ↦ quantumInt m * pairQReducedFormulaEven u m :=
    funext (pairQFormula_eq_quantumInt_mul u)
  refine ⟨Q, hQ hne, 1, one_ne_zero, fun n ↦ ?_⟩
  rw [Polynomial.C_1, one_mul, hfun]
  exact hQann (pairQReducedFormulaEven u) n (hc0 n)

/-- **Existence of a recurrence.** For every chirality, all natural `r`, `s` and every twist
`ℓ`, the formula of the twisted satellite has a nonzero annihilator valid at every integer
colour, up to a nonzero left coefficient. -/
theorem twH_exists_annihilator (η : Bool) (r s : ℕ) (ℓ : ℤ) :
    ∃ Q : RecOp, Q ≠ 0 ∧ ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (twFormula η r s ℓ) n = 0 := by
  obtain ⟨G, hG, hGann⟩ := twH_exists_tail_annihilator η r s ℓ
  exact twH_exists_annihilator_of_tail (twInput η r s ℓ) hG hGann

end AJConjecture
