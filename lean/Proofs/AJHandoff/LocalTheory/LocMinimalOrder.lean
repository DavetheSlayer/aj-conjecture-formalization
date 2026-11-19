import Mathlib
import AJConjecture.FieldActionBridge
import AJConjecture.RecurrencePolynomialExists
import AJHandoff.LocalTheory.LocTailOrder
import AJHandoff.LocalTheory.LocTailExtension

/-!
# The true minimal recurrence: order `d + 1`

Let `J` be a signed integer-coloured sequence (values in `ℤ[t, t⁻¹]`, as `coloredJones`) whose
image in `ℚ(t)` is `[n] F(n)` on positive colours, where `F` satisfies a transfer identity
`P F = ρ` as in `tailOrder_of_transfer` (irreducible `P` of order `d`, `F` not eventually
rational, `ρ` rational and eventually nonzero), and suppose that every tail annihilator of `J`
annihilates `J` at every integer (`TailExtends`, which holds for every sequence with a cyclotomic
expansion). Then `J` has a recurrence polynomial, and every recurrence polynomial (the primitive
generator of the rationally saturated all-integer annihilator, `IsRecurrencePolynomial`) has order
exactly `d + 1`.

Proof. Lower bound: a nonzero `c α` annihilating `J` everywhere annihilates a tail of `J`, so has
order `≥ d + 1` (`tailOrder_of_transfer`). Upper bound: the gauged homogenized transfer row of
order `d + 1` annihilates `J` on positive colours, hence everywhere by `TailExtends`, and it is
nonzero; `laurentToField` is injective, so it lies in the localized annihilator.

Hypotheses supplied by a transfer for a torus pair `(r, s)` (package TorusQuantum): the operator
`P` with its irreducibility, the reduced sequence `F` with `δ P F = β`, `P F` eventually nonzero,
non-rationality of `F`, the identification `J = [n] F` on positive colours, and a cyclotomic
expansion of `J` (or directly `TailExtends`).
-/

open Polynomial
open scoped LaurentPolynomial

noncomputable section

namespace AJConjecture

theorem natDegree_isRecurrencePolynomial_of_transfer {J : ℤ → ℤ[T;T⁻¹]}
    {F : ℤ → RatFunc ℚ} {P : RecOp} (hP : 0 < P.natDegree)
    (hirr : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree = 0 ∨ R.natDegree = P.natDegree)
    (hnr : ¬ EventuallyRational F)
    (hrhs : ∃ β δ : Coeff, δ ≠ 0 ∧ ∀ n : ℤ, 1 ≤ n →
      evalAtField n δ * opApplyField P F n = evalAtField n β)
    (hne : ∃ n₂ : ℤ, ∀ n : ℤ, n₂ ≤ n → opApplyField P F n ≠ 0)
    (hJF : ∀ n : ℤ, 1 ≤ n → laurentToField (J n) = quantumInt n * F n)
    (hext : TailExtends fun n ↦ laurentToField (J n)) :
    (∃ α : RecOp, IsRecurrencePolynomial J α) ∧
      ∀ α : RecOp, IsRecurrencePolynomial J α → α.natDegree = P.natDegree + 1 := by
  obtain ⟨-, -, ⟨G, hG0, hGdeg, hG⟩, hlow⟩ :=
    tailOrder_of_transfer hP hirr hnr hrhs hne (J := fun n ↦ laurentToField (J n)) hJF
  have hGall := hext G ⟨1, hG⟩
  have hGin : InLocalizedAnnihilator J G := ⟨1, one_ne_zero, fun n ↦ by
    apply laurentToField_injective
    rw [map_one, one_mul, laurentToField_opApply, hGall n, map_zero]⟩
  have hdeg : ∀ α : RecOp, α ≠ 0 → InLocalizedAnnihilator J α →
      P.natDegree + 1 ≤ α.natDegree := by
    rintro α hα0 ⟨c, hc, hann⟩
    rw [← natDegree_C_mul (a := c) (p := α) hc]
    refine hlow _ (mul_ne_zero (C_ne_zero.mpr hc) hα0) ⟨0, fun n _ ↦ ?_⟩
    rw [← laurentToField_opApply, hann n, map_zero]
  refine ⟨exists_isRecurrencePolynomial ⟨G, hG0, hGin⟩, fun α hα ↦ ?_⟩
  exact le_antisymm (hGdeg ▸ hα.2.2.1 G hG0 hGin) (hdeg α hα.1 hα.2.1)

end AJConjecture
