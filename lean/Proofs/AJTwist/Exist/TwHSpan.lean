import Mathlib
import AJConjecture.QAlgQParamBasic

/-!
# Saturated polynomial spans of sequences (existence of a recurrence, inner part)

Source: revision 5, Section 8.1 (`conclusion.tex`), first paragraph: for twist `ℓ ≠ 0` the
manuscript obtains a nonzero annihilator of the coloured Jones function from the
`q`-holonomicity theorem of the literature. This package (`AJTwist/Exist`) replaces the citation
by a proof; the route is described in `AJTwist.Exist.TwHExists`.

Sequences in the summation index `j` (functions `ℕ → ℚ(t)`) are acted on by polynomials in
`J = q^j`: `(f · y)_j = f(q^j) y_j`. For a finite family `g` of sequences, `TwHSpan g y` says
that `y` lies in the *saturation* of the `ℚ(t)[J]`-span of `g`: a nonzero polynomial multiple of
`y` is a polynomial combination of the `g k`, at **every** `j ≥ 0`. Multipliers are used instead
of quotients because the coefficients that have to be inverted may vanish at some `j` (the top
coefficient `q (1 - J)` of the inner operator `p_0` vanishes at `j = 0`).

This file has the definition and the four primitive closure properties; the derived ones are in
`AJTwist.Exist.TwHSpanClosure`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `y` lies in the saturated `ℚ(t)[J]`-span of the sequences `g k`: there are a nonzero
multiplier `δ` and polynomials `A k` with `δ(q^j) y_j = ∑_k A_k(q^j) g_k(j)` for every `j`. -/
def TwHSpan {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ) (y : ℕ → RatFunc ℚ) : Prop :=
  ∃ δ : (RatFunc ℚ)[X], δ ≠ 0 ∧ ∃ A : ι → (RatFunc ℚ)[X],
    ∀ j : ℕ, δ.eval (qParam ^ j) * y j = ∑ k, (A k).eval (qParam ^ j) * g k j

/-- A generator lies in the span (`δ = 1`, `A = ` the indicator of `k`). -/
theorem twHSpan_gen {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ) (k : ι) :
    TwHSpan g (g k) := by
  classical
  refine ⟨1, one_ne_zero, Pi.single k 1, fun j ↦ ?_⟩
  rw [Finset.sum_eq_single k
    (fun i _ hik ↦ by rw [Pi.single_eq_of_ne hik, eval_zero, zero_mul])
    (fun hk ↦ absurd (Finset.mem_univ k) hk), Pi.single_eq_same]

/-- The span is closed under addition (`δ = δ₁ δ₂`, `A = δ₂ A₁ + δ₁ A₂`). -/
theorem twHSpan_add {ι : Type*} [Fintype ι] {g : ι → ℕ → RatFunc ℚ} {y z : ℕ → RatFunc ℚ}
    (hy : TwHSpan g y) (hz : TwHSpan g z) : TwHSpan g (fun j ↦ y j + z j) := by
  obtain ⟨δ₁, h₁, A₁, e₁⟩ := hy
  obtain ⟨δ₂, h₂, A₂, e₂⟩ := hz
  refine ⟨δ₁ * δ₂, mul_ne_zero h₁ h₂, fun k ↦ δ₂ * A₁ k + δ₁ * A₂ k, fun j ↦ ?_⟩
  simp only [eval_mul, eval_add, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
    ← e₁, ← e₂]
  ring

/-- The span is closed under multiplication by a polynomial in `J = q^j` (same `δ`,
`A` multiplied by `f`). -/
theorem twHSpan_polyMul {ι : Type*} [Fintype ι] {g : ι → ℕ → RatFunc ℚ} {y : ℕ → RatFunc ℚ}
    (f : (RatFunc ℚ)[X]) (hy : TwHSpan g y) :
    TwHSpan g (fun j ↦ f.eval (qParam ^ j) * y j) := by
  obtain ⟨δ, h, A, e⟩ := hy
  refine ⟨δ, h, fun k ↦ f * A k, fun j ↦ ?_⟩
  simp only [eval_mul, mul_assoc, ← Finset.mul_sum, ← e]
  ring

/-- Saturation: if a nonzero polynomial multiple of `y` lies in the span, so does `y`
(`δ` multiplied by `f`, same `A`). -/
theorem twHSpan_of_polyMul {ι : Type*} [Fintype ι] {g : ι → ℕ → RatFunc ℚ}
    {y : ℕ → RatFunc ℚ} {f : (RatFunc ℚ)[X]} (hf : f ≠ 0)
    (hy : TwHSpan g (fun j ↦ f.eval (qParam ^ j) * y j)) : TwHSpan g y := by
  obtain ⟨δ, h, A, e⟩ := hy
  refine ⟨δ * f, mul_ne_zero h hf, A, fun j ↦ ?_⟩
  rw [eval_mul, mul_assoc]
  exact e j

end AJConjecture
