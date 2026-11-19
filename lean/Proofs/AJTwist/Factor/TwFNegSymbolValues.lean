import Mathlib
import AJConjecture.QAlgWeylSymbol
import AJFamily.Quantum.DoubleRootRecurrence
import AJFamily.Quantum.TwistPolyNodeValues
import AJTwist.Quantum.TwQTwistPolyNeg

/-!
# `T̂_(-b)` at a double point of its recursion, in the coordinates `(x, J)` (TwF, unit F2)

Source: revision 5, Section 5.4 (`operators.tex`, "Negative effective index"): at the crossing
`(L - 1)/C_b` (`Z = 2`) one has `p_Z = 4b`, `p_{ZJ} = -(2b² - 2b + 1)`, `p_{ZZ} = (4b³ + 2b)/3`;
at the crossing `E/C_b` (`Z = -2`) `p_Z = 0`, `p_{ZJ} = s_b h_b`, `p_{ZZ} = -2 s_b b(2b+1)/3`.

Both nodes of `P_(-b)` lie on the locus `ζ² = 4x²` where the recursion
`T̂_(-(k+2)) = ζ T̂_(-(k+1)) - x² T̂_(-k)` of `symbolTwistNeg` has a double characteristic root
`w = ζ/2 = ± x` (`w = x` at the abelian node `J = 1`, `w = -x` on the curve `Z = -2`). There
`T̂_(-k) = w^k + k w^(k-1) δ`, `δ = x² + 1 - xJ - w`, and the derivatives `∂_J`, `∂_x` are the
closed forms `dblRootDeriv` of the library, with `∂_J ζ = 2xJ - (x² + 1)`,
`∂_x ζ = J² - 2xJ + 2x + 1`, `∂_J T̂_(-1) = -x`, `∂_x T̂_(-1) = 2x - J`, `∂_x (x²) = 2x`.

Here `evalIntPoint f x₀ J₀` evaluates `f ∈ ℤ[x][J]` at `x = x₀`, `J = J₀`; `derivative` is `∂_J`
and `coeffDerivative` is `∂_x`.
Route: `dblRoot_closed` (three times, as in `twistPoly_node_values`,
`AJFamily/Quantum/TwistPolyNodeValues.lean`), with `evalIntPoint_eq` and
`coeffDerivative_eq_innerDerivative`, `innerDerivative_mul`.
Checked for `b ≤ 8` through the node identities (scratch `check_paper5.py`, `node_closed_neg.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value of `ζ = x J² - (x² + 1) J + x² + x + 1` at a point. -/
theorem evalIntPoint_symbolZeta (x₀ J₀ : ℂ) :
    evalIntPoint symbolZeta x₀ J₀ = x₀ * J₀ ^ 2 - (x₀ ^ 2 + 1) * J₀ + (x₀ ^ 2 + x₀ + 1) := by
  rw [evalIntPoint_eq, symbolZeta]
  simp only [evalIntHomTwistNode, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_one, coe_eval₂RingHom, eval₂_mul, eval₂_pow, eval₂_add,
    eval₂_sub, eval₂_C, eval₂_X, coe_evalRingHom, eval_pow, eval_X, eval_add, eval_one]

/-- The inner derivative of `1` vanishes. -/
private theorem innerDerivative_one_twfNegSymbolValues :
    innerDerivative (1 : ℤ[X][X]) = 0 := by
  rw [← C_1, innerDerivative_C, derivative_one, C_0]

/-- The inner derivative of the outer variable vanishes. -/
private theorem innerDerivative_X_twfNegSymbolValues : innerDerivative (X : ℤ[X][X]) = 0 := by
  rw [innerDerivative, sum_X_index] <;> simp

/-- The derivatives of the seeds and coefficients of the recursion of `T̂_(-k)`. -/
private theorem derivative_seeds_twfNegSymbolValues :
    derivative (symbolTwistNeg 1) = -(C X : ℤ[X][X]) ∧
      derivative symbolZeta = C (2 * X) * X - C (X ^ 2 + 1) ∧
      innerDerivative (symbolTwistNeg 1) = C (2 * X) - X ∧
      innerDerivative symbolZeta = X ^ 2 - C (2 * X) * X + C (2 * X + 1) ∧
      innerDerivative (C (X ^ 2) : ℤ[X][X]) = C (2 * X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [symbolTwistNeg, derivative_sub, derivative_mul, derivative_C, derivative_X]
    ring
  · simp only [symbolZeta, sq (X : ℤ[X][X]), derivative_add, derivative_sub, derivative_mul,
      derivative_C, derivative_X]
    simp only [C_mul, C_add, C_pow, C_1, C_ofNat]
    ring
  · simp only [symbolTwistNeg, innerDerivative_sub, innerDerivative_mul, innerDerivative_C,
      innerDerivative_X_twfNegSymbolValues, sq (X : ℤ[X]), derivative_add, derivative_mul,
      derivative_X, derivative_one]
    simp only [C_mul, C_add, C_1, C_0, C_ofNat]
    ring
  · simp only [symbolZeta, sq (X : ℤ[X][X]), innerDerivative_sub, innerDerivative_add,
      innerDerivative_mul, innerDerivative_C, innerDerivative_X_twfNegSymbolValues,
      sq (X : ℤ[X]), derivative_add, derivative_mul, derivative_X, derivative_one]
    simp only [C_mul, C_add, C_1, C_0, C_ofNat]
    ring
  · simp only [innerDerivative_C, sq (X : ℤ[X]), derivative_mul, derivative_X]
    simp only [C_mul, C_add, C_1, C_ofNat]
    ring

/-- The values of the seeds and coefficients of the recursion of `T̂_(-k)` and of their
derivatives at a point. -/
private theorem evalIntPoint_seeds_twfNegSymbolValues (x₀ J₀ : ℂ) :
    evalIntPoint (C (X ^ 2) : ℤ[X][X]) x₀ J₀ = x₀ ^ 2 ∧
      evalIntPoint (symbolTwistNeg 1) x₀ J₀ = x₀ ^ 2 + 1 - x₀ * J₀ ∧
      evalIntPoint (derivative (symbolTwistNeg 1)) x₀ J₀ = -x₀ ∧
      evalIntPoint (derivative symbolZeta) x₀ J₀ = 2 * x₀ * J₀ - (x₀ ^ 2 + 1) ∧
      evalIntPoint (derivative (C (X ^ 2) : ℤ[X][X])) x₀ J₀ = 0 ∧
      evalIntPoint (coeffDerivative (symbolTwistNeg 1)) x₀ J₀ = 2 * x₀ - J₀ ∧
      evalIntPoint (coeffDerivative symbolZeta) x₀ J₀ = J₀ ^ 2 - 2 * x₀ * J₀ + 2 * x₀ + 1 ∧
      evalIntPoint (coeffDerivative (C (X ^ 2) : ℤ[X][X])) x₀ J₀ = 2 * x₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := derivative_seeds_twfNegSymbolValues
  simp only [evalIntPoint_eq, coeffDerivative_eq_innerDerivative, h1, h2, h3, h4, h5,
    derivative_C, map_zero]
  refine ⟨?_, ?_, ?_, ?_, trivial, ?_, ?_, ?_⟩
  all_goals
    simp only [symbolTwistNeg, evalIntHomTwistNode, RingHom.comp_apply, coe_mapRingHom,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_neg, Polynomial.map_C, Polynomial.map_X, Polynomial.map_one,
      Polynomial.map_ofNat, coe_eval₂RingHom, eval₂_mul, eval₂_pow, eval₂_add,
      eval₂_sub, eval₂_neg, eval₂_C, eval₂_X, coe_evalRingHom, eval_pow, eval_X, eval_add,
      eval_one, eval_mul, eval_ofNat]
  ring

/-- Values and first derivatives of `T̂_(-k)` at a double point `ζ = 2w`, `w² = x²` of its
recursion. -/
theorem symbolTwistNeg_node_values {x₀ J₀ w : ℂ} (hw : evalIntPoint symbolZeta x₀ J₀ = 2 * w)
    (hw2 : w ^ 2 = x₀ ^ 2) (hw0 : w ≠ 0) (k : ℕ) :
    evalIntPoint (symbolTwistNeg k) x₀ J₀ =
        w ^ k + k * w ^ (k - 1) * (x₀ ^ 2 + 1 - x₀ * J₀ - w) ∧
      evalIntPoint (derivative (symbolTwistNeg k)) x₀ J₀ =
        dblRootDeriv w (x₀ ^ 2 + 1 - x₀ * J₀ - w) (-x₀) (2 * x₀ * J₀ - (x₀ ^ 2 + 1)) 0 k ∧
      evalIntPoint (coeffDerivative (symbolTwistNeg k)) x₀ J₀ =
        dblRootDeriv w (x₀ ^ 2 + 1 - x₀ * J₀ - w) (2 * x₀ - J₀)
          (J₀ ^ 2 - 2 * x₀ * J₀ + 2 * x₀ + 1) (2 * x₀) k := by
  obtain ⟨hQ, hT1, hT1J, hζJ, hQJ, hT1x, hζx, hQx⟩ :=
    evalIntPoint_seeds_twfNegSymbolValues x₀ J₀
  have hQw : evalIntPoint (C (X ^ 2) : ℤ[X][X]) x₀ J₀ = w ^ 2 := by rw [hQ, hw2]
  have hrec : ∀ k, symbolTwistNeg (k + 2) =
      symbolZeta * symbolTwistNeg (k + 1) - C (X ^ 2) * symbolTwistNeg k := fun k ↦ rfl
  have hy : ∀ k, evalIntPoint (symbolTwistNeg (k + 2)) x₀ J₀ =
      2 * w * evalIntPoint (symbolTwistNeg (k + 1)) x₀ J₀ -
        w ^ 2 * evalIntPoint (symbolTwistNeg k) x₀ J₀ := by
    intro k
    rw [hrec, ← hw, ← hQw]
    simp only [evalIntPoint_eq, map_sub, map_mul]
  have hy0 : evalIntPoint (symbolTwistNeg 0) x₀ J₀ = 1 := by
    rw [evalIntPoint_eq, symbolTwistNeg, map_one]
  have hy1 : evalIntPoint (symbolTwistNeg 1) x₀ J₀ = w + (x₀ ^ 2 + 1 - x₀ * J₀ - w) := by
    rw [hT1]
    ring
  have key := fun (z₁ α β : ℂ) (z : ℕ → ℂ) ↦
    dblRoot_closed (z₁ := z₁) (α := α) (β := β)
      (y := fun k ↦ evalIntPoint (symbolTwistNeg k) x₀ J₀) (z := z) hw0 hy0 hy1 hy
  have hE := hw
  have hF := hQw
  simp only [evalIntPoint_eq] at hE hF hζJ hQJ hζx hQx
  refine ⟨(key 0 0 0 (fun _ ↦ 0) rfl rfl (fun _ ↦ by ring) k).1,
    (key _ _ _ (fun k ↦ evalIntPoint (derivative (symbolTwistNeg k)) x₀ J₀) ?_ hT1J ?_ k).2,
    (key _ _ _ (fun k ↦ evalIntPoint (coeffDerivative (symbolTwistNeg k)) x₀ J₀) ?_ hT1x ?_ k).2⟩
  · simp only [symbolTwistNeg, derivative_one, evalIntPoint_eq, map_zero]
  · intro k
    simp only [hrec, derivative_mul, evalIntPoint_eq, map_sub, map_add, map_mul,
      hE, hF, hζJ, hQJ]
    ring
  · simp only [symbolTwistNeg, coeffDerivative_eq_innerDerivative,
      innerDerivative_one_twfNegSymbolValues, evalIntPoint_eq, map_zero]
  · intro k
    simp only [hrec, coeffDerivative_eq_innerDerivative, innerDerivative_sub,
      innerDerivative_mul, evalIntPoint_eq, map_sub, map_add, map_mul, hE, hF]
    simp only [← coeffDerivative_eq_innerDerivative, hζx, hQx]
    ring

/-- The double-root closed form at a zero `w + k δ = 0`, for every `k ≥ 1` (the library's
`dblRootDeriv_eq_of_crit` is stated for `k ≥ 2`), with the denominators cleared. -/
theorem dblRootDeriv_mul_of_crit {w δ z₁ α β : ℂ} {k : ℕ} (hk : 1 ≤ k) (hw : w ≠ 0)
    (hδ : w + k * δ = 0) :
    6 * w * dblRootDeriv w δ z₁ α β k = w ^ (k - 1) *
      (6 * k * w * z₁ + (k - 1) * (2 * k - 1) * α * w - 2 * (k - 1) * (k + 1) * β) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hk0 : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hδ' : δ = -w / ((j + 1 : ℕ) : ℂ) := by
    field_simp
    linear_combination hδ
  rw [dblRootDeriv, Nat.add_sub_cancel, pow_succ, hδ']
  push_cast at hk0 ⊢
  field_simp
  ring

end AJConjecture
