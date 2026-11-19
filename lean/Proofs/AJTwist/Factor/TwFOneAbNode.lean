import Mathlib
import AJFamily.Quantum.AbNodeNoSeparation
import AJFamily.Quantum.FamSymbolFacts
import AJFamily.Quantum.AbNodeCertificateIdentity
import AJTwist.Factor.TwFOneWeyl

/-!
# The degenerate crossing `K = 3` of `P_1` (TwF, unit F3)

Source: revision 5, Section 5.5 (`operators.tex`, "The rank-one split at `a = 1`"): "At `K = 3`
the block `T_1 = (J - 1)²` has a double shift root. … At `u = 1`,
`H_raw(x, 1) = 4 (1 - x)^(-5) ((x - 1)/(x + 1)) (3 - K)`. It has a simple `x`-zero at each
solution `x₀` of `K = 3`."

`famOne_abNode_data`: at `(m₀, 1)` with `(m₀²)² - 3 m₀² + 1 = 0`: `m₀ ≠ 0`, `m₀² ≠ ± 1`, both end
coefficients of the symbol of `famTransferOp 1` are nonzero, and
`H(M) = (∂_L P₀)(M, 1)` has a simple zero at `m₀` (`H(m₀) = 0`, `H'(m₀) ≠ 0`).

Route: `specialize_famTransferOp_mul_eq 1`: `κ₁ P₀ = κ₂ (L - 1) E B_1`; differentiating in `L` at
`L = 1`: `κ₁ H = κ₂ E(M, 1) B_1(M, 1)` with `E(M, 1) = 4M²` and
`B_1(M, 1) = -(M⁴ - 3M² + 1)(M² + 1)²` (`twistPoly_one_eq_explicit`); `κ₁, κ₂` do not vanish at
`m₀` (`eval_symbolLeft_ne_zero`, `eval_symbolRight_ne_zero`), and `M⁴ - 3M² + 1` has simple roots
(`4 m₀³ - 6 m₀ = 2 m₀ (2 m₀² - 3) ≠ 0` on the node quartic). The end coefficients are
`eval_coeff_specialize_famTransferOp_ne_zero 1`. In the paper's normalization this is the simple
zero of `H_raw(x, 1)` at `K = 3`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A simple zero of a factor of the right-hand side of `κ₁ H = κ₂ Q A` gives a zero of `H`
and the value of its derivative. -/
private theorem eval_derivative_of_mul_eq_twfOneAbNode {κ₁ κ₂ H Q A : ℂ[X]} {m₀ : ℂ}
    (hI : κ₁ * H = κ₂ * (Q * A)) (hκ₁ : κ₁.eval m₀ ≠ 0) (hQ : Q.eval m₀ = 0) :
    H.eval m₀ = 0 ∧ κ₁.eval m₀ * (derivative H).eval m₀ =
      κ₂.eval m₀ * ((derivative Q).eval m₀ * A.eval m₀) := by
  have e0 := congrArg (eval m₀) hI
  simp only [eval_mul, hQ, zero_mul, mul_zero] at e0
  have hH : H.eval m₀ = 0 := (mul_eq_zero.mp e0).resolve_left hκ₁
  refine ⟨hH, ?_⟩
  have e1 := congrArg (fun p ↦ (derivative p).eval m₀) hI
  simp only [derivative_mul, eval_add, eval_mul, hQ, hH, zero_mul, mul_zero, zero_add,
    add_zero] at e1
  exact e1

/-- From the symbol `κ₁ P₀ = κ₂ (L - 1) E B_1`: `H(M) = (∂_L P₀)(M, 1)` has a simple zero at the
degenerate abelian node. -/
private theorem simple_zero_of_symbol_twfOneAbNode {P₀ : ℤ[X][X]} {κ₁ κ₂ : ℤ[X]}
    (hsym : C κ₁ * P₀ = C κ₂ * ((X - 1) * extraFactor * twistPoly 1)) {m₀ : ℂ}
    (hab : (m₀ ^ 2) ^ 2 - 3 * m₀ ^ 2 + 1 = 0)
    (hκ₁ : (κ₁.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hκ₂ : (κ₂.map (Int.castRingHom ℂ)).eval m₀ ≠ 0) :
    evalIntPoint (derivative P₀) m₀ 1 = 0 ∧
      evalIntPoint (coeffDerivative (derivative P₀)) m₀ 1 ≠ 0 := by
  have hE1 : extraFactor.eval 1 = 4 * X ^ 2 := by
    rw [extraFactor]
    simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
    ring
  have hB1 : (twistPoly 1).eval 1 = -((X ^ 4 - 3 * X ^ 2 + 1) * (X ^ 2 + 1) ^ 2) := by
    rw [twistPoly_one_eq_explicit]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
    ring
  have hI := congrArg (fun p : ℤ[X][X] ↦ (derivative p).eval 1) hsym
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C, eval_add,
    derivative_sub, derivative_X, derivative_one, sub_zero, eval_sub, eval_X, eval_one,
    sub_self, one_mul, add_zero, hE1, hB1] at hI
  have hI' := congrArg (Polynomial.map (Int.castRingHom ℂ)) hI
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_neg, Polynomial.map_one, Polynomial.map_X, Polynomial.map_ofNat] at hI'
  have hI'' : κ₁.map (Int.castRingHom ℂ) *
      ((derivative P₀).eval 1).map (Int.castRingHom ℂ) =
      κ₂.map (Int.castRingHom ℂ) * ((X ^ 4 - 3 * X ^ 2 + 1) *
        (-(4 * X ^ 2 * (X ^ 2 + 1) ^ 2))) := by
    rw [hI']
    ring
  obtain ⟨hH, hH'⟩ := eval_derivative_of_mul_eq_twfOneAbNode hI'' hκ₁ (by
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one]
    linear_combination hab)
  rw [evalIntPoint_at_one, evalIntPoint_at_one, eval_one_coeffDerivative, ← derivative_map]
  refine ⟨hH, fun h0 ↦ ?_⟩
  rw [h0, mul_zero] at hH'
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_X_pow, derivative_one,
    derivative_ofNat, eval_add, eval_sub, eval_mul, eval_neg, eval_pow, eval_X, eval_ofNat,
    eval_one, eval_C, zero_mul, zero_add, add_zero] at hH'
  have hm0 : m₀ ≠ 0 := by
    rintro rfl
    norm_num at hab
  have h23 : 2 * m₀ ^ 2 - 3 ≠ 0 := by
    intro h
    have h' : (-5 / 4 : ℂ) = 0 := by linear_combination hab - (m₀ ^ 2 / 2 - 3 / 4) * h
    norm_num at h'
  have h21 : m₀ ^ 2 + 1 ≠ 0 := by
    intro h
    have h' : (5 : ℂ) = 0 := by linear_combination hab - (m₀ ^ 2 - 4) * h
    norm_num at h'
  have hprod : (κ₂.map (Int.castRingHom ℂ)).eval m₀ *
      (m₀ ^ 3 * (2 * m₀ ^ 2 - 3) * (m₀ ^ 2 + 1) ^ 2) = 0 := by
    linear_combination (1 / 8 : ℂ) * hH'
  exact mul_ne_zero hκ₂ (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hm0) h23)
    (pow_ne_zero 2 h21)) hprod

/-- The data of the degenerate abelian node `K = 3` of `P_1` used by the rank-one tests. -/
theorem famOne_abNode_data {m₀ : ℂ} (hab : (m₀ ^ 2) ^ 2 - 3 * m₀ ^ 2 + 1 = 0) :
    m₀ ≠ 0 ∧
      ((specialize (famTransferOp 1)).leadingCoeff.map (Int.castRingHom ℂ)).eval m₀ ≠ 0 ∧
      (((specialize (famTransferOp 1)).coeff 0).map (Int.castRingHom ℂ)).eval m₀ ≠ 0 ∧
      evalIntPoint (derivative (specialize (famTransferOp 1))) m₀ 1 = 0 ∧
      evalIntPoint (coeffDerivative (derivative (specialize (famTransferOp 1)))) m₀ 1 ≠ 0 := by
  have hm0 : m₀ ≠ 0 := by
    rintro rfl
    norm_num at hab
  have h1 : m₀ ^ 2 ≠ 1 := by
    intro h
    rw [h] at hab
    norm_num at hab
  have h2 : m₀ ^ 2 ≠ -1 := by
    intro h
    rw [h] at hab
    norm_num at hab
  obtain ⟨hlead, hconst⟩ := eval_coeff_specialize_famTransferOp_ne_zero 1 le_rfl hm0 h1 h2
  obtain ⟨hH0, hH1⟩ := simple_zero_of_symbol_twfOneAbNode
    (specialize_famTransferOp_mul_eq 1 le_rfl) hab (eval_symbolLeft_ne_zero 1 h1 h2)
    (eval_symbolRight_ne_zero 1 h1 h2)
  exact ⟨hm0, hlead, hconst, hH0, hH1⟩

end AJConjecture
