import Mathlib
import AJTwist.Exist.TwHSpan

/-!
# Saturated polynomial spans: derived closure properties

Consequences of the four primitive properties of `TwHSpan` (`twHSpan_gen`, `twHSpan_add`,
`twHSpan_polyMul`, `twHSpan_of_polyMul`): the zero sequence, constant multiples, differences,
finite sums, and transitivity (a sequence in the span of a family whose members lie in the span
of `g` lies in the span of `g`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The zero sequence lies in every span (`δ = 1`, `A = 0`). -/
theorem twHSpan_zero {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ) :
    TwHSpan g (fun _ ↦ 0) := by
  refine ⟨1, one_ne_zero, 0, fun j ↦ ?_⟩
  simp only [Pi.zero_apply, eval_zero, zero_mul, mul_zero, Finset.sum_const_zero]

/-- The span is closed under multiplication by a constant (`twHSpan_polyMul` with `f = C c`). -/
theorem twHSpan_constMul {ι : Type*} [Fintype ι] {g : ι → ℕ → RatFunc ℚ} {y : ℕ → RatFunc ℚ}
    (c : RatFunc ℚ) (hy : TwHSpan g y) : TwHSpan g (fun j ↦ c * y j) := by
  have h := twHSpan_polyMul (C c) hy
  simp only [eval_C] at h
  exact h

/-- The span is closed under subtraction. -/
theorem twHSpan_sub {ι : Type*} [Fintype ι] {g : ι → ℕ → RatFunc ℚ} {y z : ℕ → RatFunc ℚ}
    (hy : TwHSpan g y) (hz : TwHSpan g z) : TwHSpan g (fun j ↦ y j - z j) := by
  have h := twHSpan_add hy (twHSpan_constMul (-1) hz)
  have e : (fun j ↦ y j - z j) = fun j ↦ y j + -1 * z j := by
    funext j
    ring
  rw [e]
  exact h

/-- The span is closed under finite sums (induction on the finite set, `twHSpan_zero`,
`twHSpan_add`). -/
theorem twHSpan_sum {ι κ : Type*} [Fintype ι] {g : ι → ℕ → RatFunc ℚ} (S : Finset κ)
    (y : κ → ℕ → RatFunc ℚ) (hy : ∀ a ∈ S, TwHSpan g (y a)) :
    TwHSpan g (fun j ↦ ∑ a ∈ S, y a j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact twHSpan_zero g
  | insert a S ha ih =>
    have h := twHSpan_add (hy a (Finset.mem_insert_self a S))
      (ih fun b hb ↦ hy b (Finset.mem_insert_of_mem hb))
    have e : (fun j ↦ ∑ b ∈ insert a S, y b j) = fun j ↦ y a j + ∑ b ∈ S, y b j := by
      funext j
      rw [Finset.sum_insert ha]
    rw [e]
    exact h

/-- Transitivity: if every member of a second family `g'` lies in the span of `g`, then the span
of `g'` is contained in the span of `g`. With `δ' y = ∑_k A'_k g'_k`: the right-hand side lies in
the span of `g` (`twHSpan_sum`, `twHSpan_polyMul`), hence so does `y` (`twHSpan_of_polyMul`). -/
theorem twHSpan_trans {ι κ : Type*} [Fintype ι] [Fintype κ] {g : ι → ℕ → RatFunc ℚ}
    {g' : κ → ℕ → RatFunc ℚ} {y : ℕ → RatFunc ℚ} (hg : ∀ k, TwHSpan g (g' k))
    (hy : TwHSpan g' y) : TwHSpan g y := by
  obtain ⟨δ, hδ, A, e⟩ := hy
  refine twHSpan_of_polyMul hδ ?_
  have h := twHSpan_sum (g := g) Finset.univ (fun k j ↦ (A k).eval (qParam ^ j) * g' k j)
    fun k _ ↦ twHSpan_polyMul (A k) (hg k)
  have e' : (fun j ↦ δ.eval (qParam ^ j) * y j) =
      fun j ↦ ∑ k, (A k).eval (qParam ^ j) * g' k j := funext e
  rw [e']
  exact h

end AJConjecture
