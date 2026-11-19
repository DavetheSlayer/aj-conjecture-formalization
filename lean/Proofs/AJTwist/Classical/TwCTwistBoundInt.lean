import Mathlib
import AJFamily.Classical.TwistBoundGen
import AJTwist.Classical.TwCTwistBoundNeg

/-!
# The bound for the twist relation of an arbitrary signed index

Source: revision 5, Section 7.2 (`classical.tex`): a signed filling `μ_A λ_A^k` of the marked
Whitehead pattern gives `T_k = 0`, that is `𝒫_k = 0` off the abelian line.

`twist_bound_int`: for `a, a₁ ∈ SL₂(ℂ)`, `c = compMer a a₁ = a a₁⁻¹ a⁻¹ a₁` and `n ∈ ℤ`, if
`a₁ c^n = c^n a` and `a` and the longitude `a² c^(-n) a⁻¹ c^n a a₁⁻¹ a⁻¹` are upper triangular,
then `(L - 1) 𝒫_n` vanishes at their diagonal entries `(M, L)`.

Route: `n > 0`: `twist_bound_gen n.toNat` and `famB_eq_twistPoly`; `n = 0`: `a₁ = a` and the
longitude is `1`; `n < 0`: `twist_bound_neg (-n).toNat`, after rewriting the relation as
`c^b a₁ = a c^b`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value of `(L - 1) P` at a point. -/
private theorem evalPoint_sub_one_mul_twCTwistBoundInt (P : ℤ[X][X]) (M L : ℂ) :
    evalPoint (mapC ((X - 1) * P)) (M, L) = (L - 1) * evalPoint (mapC P) (M, L) := by
  simp only [evalPoint, mapC, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_one, eval₂_mul, eval₂_sub, eval₂_X, eval₂_one]

/-- The index `0`: the relation is `a₁ = a` and the longitude is trivial. -/
private theorem twist_bound_zero_twCTwistBoundInt (a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (hrel : a₁ * compMer a a₁ ^ (0 : ℤ) = compMer a a₁ ^ (0 : ℤ) * a) :
    evalPoint (mapC ((X - 1) * twP 0))
      (a.1 0 0, (a ^ 2 * (compMer a a₁ ^ (0 : ℤ))⁻¹ * a⁻¹ * compMer a a₁ ^ (0 : ℤ) * a * a₁⁻¹ *
        a⁻¹).1 0 0) = 0 := by
  rw [zpow_zero, mul_one, one_mul] at hrel
  subst hrel
  have h : a₁ ^ 2 * (compMer a₁ a₁ ^ (0 : ℤ))⁻¹ * a₁⁻¹ * compMer a₁ a₁ ^ (0 : ℤ) * a₁ * a₁⁻¹ *
      a₁⁻¹ = 1 := by
    rw [zpow_zero]
    group
  rw [h, evalPoint_sub_one_mul_twCTwistBoundInt, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_apply_eq, sub_self, zero_mul]

/-- The bound `(L - 1) 𝒫_n` for the twist relation `a₁ c^n = c^n a` of signed index `n`. -/
theorem twist_bound_int (n : ℤ) (a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ) (ha : a.1 1 0 = 0)
    (hrel : a₁ * compMer a a₁ ^ n = compMer a a₁ ^ n * a)
    (hl : (a ^ 2 * (compMer a a₁ ^ n)⁻¹ * a⁻¹ * compMer a a₁ ^ n * a * a₁⁻¹ * a⁻¹).1 1 0 = 0) :
    evalPoint (mapC ((X - 1) * twP n))
      (a.1 0 0, (a ^ 2 * (compMer a a₁ ^ n)⁻¹ * a⁻¹ * compMer a a₁ ^ n * a * a₁⁻¹ *
        a⁻¹).1 0 0) = 0 := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · obtain _ | m := m
    · exact twist_bound_zero_twCTwistBoundInt a a₁ hrel
    · rw [zpow_natCast] at hrel hl ⊢
      rw [twP_natCast, ← famB_eq_twistPoly (m + 1) (by omega)]
      exact twist_bound_gen (m + 1) a a₁ ha hrel hl
  · obtain _ | m := m
    · exact twist_bound_zero_twCTwistBoundInt a a₁ hrel
    · rw [zpow_neg, zpow_natCast] at hrel hl ⊢
      rw [inv_inv] at hl ⊢
      rw [twP_neg_natCast (m + 1) (by omega)]
      refine twist_bound_neg (m + 1) (by omega) a a₁ ha ?_ hl
      have h := congrArg (fun y ↦ compMer a a₁ ^ (m + 1) * y * compMer a a₁ ^ (m + 1)) hrel
      simpa only [mul_assoc, inv_mul_cancel, mul_one, mul_inv_cancel_left] using h

end AJConjecture
