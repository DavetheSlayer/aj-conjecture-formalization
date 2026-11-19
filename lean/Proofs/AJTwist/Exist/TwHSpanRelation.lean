import Mathlib
import AJTwist.Exist.TwHSpan

/-!
# Finite rank: more sequences than generators satisfy a polynomial relation

`twHSpan_exists_relation`: if `r + 1` sequences lie in the saturated span of `r` generators, then
there are polynomials `ρ_0, …, ρ_r` in `J`, not all zero, with `∑_s ρ_s(q^j) y_s(j) = 0` at
**every** `j ≥ 0`.

Proof. Write `δ_s y_s = ∑_k A_(s,k) g_k`. The `r + 1` rows `A_s` of the free module
`ℚ(t)[J]^r` over the domain `ℚ(t)[J]` are linearly dependent (`twH_exists_vecMul_eq_zero`):
`∑_s π_s A_s = 0` with `π ≠ 0`. Put `ρ_s = π_s δ_s`; it is nonzero where `π_s` is, and
`∑_s ρ_s(J) y_s = ∑_k (∑_s π_s A_(s,k))(J) g_k = 0`. No quotient is formed, so the relation
holds also at the values of `j` where some multiplier vanishes.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Over a commutative domain, `r + 1` vectors with `r` coordinates are linearly dependent. -/
theorem twH_exists_vecMul_eq_zero {ι : Type*} [Fintype ι] {R : Type*} [CommRing R] [IsDomain R]
    (M : Fin (Fintype.card ι + 1) → ι → R) :
    ∃ π : Fin (Fintype.card ι + 1) → R, π ≠ 0 ∧ ∀ k, ∑ s, π s * M s k = 0 := by
  by_contra hcon
  have hli : LinearIndependent R M := by
    rw [Fintype.linearIndependent_iff]
    intro π hπ
    by_contra h
    refine hcon ⟨π, fun h0 ↦ h fun i ↦ congrFun h0 i, fun k ↦ ?_⟩
    have := congrFun hπ k
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  have h := hli.fintype_card_le_finrank
  simp at h

/-- `r + 1` sequences in the saturated span of `r` generators satisfy a nontrivial polynomial
relation, valid at every `j`. -/
theorem twHSpan_exists_relation {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ)
    (y : Fin (Fintype.card ι + 1) → ℕ → RatFunc ℚ) (hy : ∀ s, TwHSpan g (y s)) :
    ∃ ρ : Fin (Fintype.card ι + 1) → (RatFunc ℚ)[X], ρ ≠ 0 ∧
      ∀ j : ℕ, ∑ s, (ρ s).eval (qParam ^ j) * y s j = 0 := by
  choose δ hδ A e using hy
  obtain ⟨π, hπ, hrel⟩ := twH_exists_vecMul_eq_zero fun s k ↦ A s k
  refine ⟨fun s ↦ π s * δ s, fun h0 ↦ hπ (funext fun s ↦ ?_), fun j ↦ ?_⟩
  · rcases mul_eq_zero.mp (congrFun h0 s) with h | h
    · exact h
    · exact absurd h (hδ s)
  · have h1 : ∀ s, (π s * δ s).eval (qParam ^ j) * y s j =
        ∑ k, (π s * A s k).eval (qParam ^ j) * g k j := fun s ↦ by
      rw [eval_mul, mul_assoc, e s j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [eval_mul, mul_assoc]
    rw [Finset.sum_congr rfl fun s _ ↦ h1 s, Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [← Finset.sum_mul, ← eval_finsetSum, hrel k, eval_zero, zero_mul]

end AJConjecture
