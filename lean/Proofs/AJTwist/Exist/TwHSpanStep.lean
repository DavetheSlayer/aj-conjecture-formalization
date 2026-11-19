import Mathlib
import AJConjecture.QAlgCycloStep
import AJTwist.Exist.TwHSpanClosure

/-!
# Saturated polynomial spans are stable under the step operator `V`

`V = cycloStep` (the manuscript's `𝒵` on sequences in `j`,
`(V y)_j = (1/(qJ) + J) y_j - ((1 - J)/J) y_(j-1)`, `J = q^j`) is a first-order `q`-difference
operator, so it commutes with multiplication by a polynomial `f(J)` up to a twist:
`V (f · y) = f(J/q) · V y + (1/(qJ) + J)(f(J) - f(J/q)) · y`, and
`(1/(qJ) + J)(f(J) - f(J/q))` is the value at `J` of the polynomial
`twHTwist f = (q⁻¹ + J²) · (f(J) - f(J/q))/J`. The identity holds at every `j ≥ 0`: at `j = 0`
the coefficient `(1 - J)/J` of `y_(j-1)` vanishes on both sides.

Consequently a span whose generators are mapped into it by `V` is stable under `V`
(`twHSpan_cycloStep`): from `δ y = ∑_k A_k g_k`, applying `V` and using the commutation rule,
`δ(J/q) · V y = ∑_k (A_k(J/q) · V g_k + twHTwist A_k · g_k) - twHTwist δ · y`; the right-hand
side lies in the span and `δ(J/q) ≠ 0`.

Checked in exact arithmetic (scratch `H/h01_basic.py`, item (d): random `f` of degree `≤ 5`,
random sequences, `j ≤ 7`, three values of `t²`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The polynomial `(q⁻¹ + J²) (f(J) - f(J/q))/J`, whose value at `J = q^j` is
`(1/(qJ) + J)(f(J) - f(J/q))`. -/
def twHTwist (f : (RatFunc ℚ)[X]) : (RatFunc ℚ)[X] :=
  (C qParam⁻¹ + X ^ 2) * divX (f - f.comp (C qParam⁻¹ * X))

/-- The value of the divided difference `(f(J) - f(J/q))/J` at a nonzero point. -/
private theorem eval_divX_sub_comp_twHSpanStep (f : (RatFunc ℚ)[X]) {x : RatFunc ℚ}
    (hx : x ≠ 0) :
    (divX (f - f.comp (C qParam⁻¹ * X))).eval x = (f.eval x - f.eval (qParam⁻¹ * x)) / x := by
  have h0 : (f - f.comp (C qParam⁻¹ * X)).coeff 0 = 0 := by
    simp only [coeff_zero_eq_eval_zero, eval_sub, eval_comp, eval_mul, eval_C, eval_X, mul_zero,
      sub_self]
  have h := divX_mul_X_add (f - f.comp (C qParam⁻¹ * X))
  rw [h0, C_0, add_zero] at h
  have e := congrArg (eval x) h
  simp only [eval_mul, eval_X, eval_sub, eval_comp, eval_C] at e
  rw [eq_div_iff hx]
  exact e

/-- The substitution `J ↦ J/q` does not kill a nonzero polynomial. -/
private theorem comp_scale_ne_zero_twHSpanStep {f : (RatFunc ℚ)[X]} (hf : f ≠ 0) :
    f.comp (C qParam⁻¹ * X) ≠ 0 := by
  intro h
  rcases comp_eq_zero_iff.mp h with h | ⟨-, h⟩
  · exact hf h
  · have h1 := congrArg (fun p : (RatFunc ℚ)[X] ↦ p.coeff 1) h
    simp only [coeff_C_mul, coeff_X_one, mul_one, coeff_C_succ, coeff_X_zero, mul_zero] at h1
    exact inv_ne_zero qParam_ne_zero h1

/-- The commutation of `V` with multiplication by a polynomial in `J = q^j`, at every `j`. -/
theorem twH_cycloStep_polyMul (f : (RatFunc ℚ)[X]) (y : ℕ → RatFunc ℚ) (j : ℕ) :
    cycloStep (fun i ↦ f.eval (qParam ^ i) * y i) j =
      (f.comp (C qParam⁻¹ * X)).eval (qParam ^ j) * cycloStep y j +
        (twHTwist f).eval (qParam ^ j) * y j := by
  have hq : qParam ≠ 0 := qParam_ne_zero
  have hJ : qParam ^ j ≠ 0 := pow_ne_zero j hq
  rw [twHTwist, eval_mul, eval_divX_sub_comp_twHSpanStep f hJ]
  simp only [cycloStep, eval_comp, eval_mul, eval_C, eval_X, eval_add, eval_pow]
  rcases j with _ | j
  · simp only [pow_zero, sub_self, zero_div, zero_mul, sub_zero, mul_one]
    field_simp
    ring
  · have hpow : qParam ^ (j + 1 - 1) = qParam⁻¹ * qParam ^ (j + 1) := by
      rw [Nat.add_sub_cancel, pow_succ]
      field_simp
    rw [hpow]
    field_simp
    ring

/-- `V` is additive, for finite sums. -/
theorem twH_cycloStep_finsetSum {κ : Type*} (S : Finset κ) (y : κ → ℕ → RatFunc ℚ) (j : ℕ) :
    cycloStep (fun i ↦ ∑ a ∈ S, y a i) j = ∑ a ∈ S, cycloStep (y a) j := by
  simp only [cycloStep, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- A span whose generators are mapped into it by `V` is stable under `V`. -/
theorem twHSpan_cycloStep {ι : Type*} [Fintype ι] {g : ι → ℕ → RatFunc ℚ}
    {y : ℕ → RatFunc ℚ} (hg : ∀ k, TwHSpan g (cycloStep (g k))) (hy : TwHSpan g y) :
    TwHSpan g (cycloStep y) := by
  obtain ⟨δ, hδ, A, e⟩ := hy
  have hy' : TwHSpan g y := ⟨δ, hδ, A, e⟩
  refine twHSpan_of_polyMul (comp_scale_ne_zero_twHSpanStep hδ) ?_
  have hk : ∀ k, TwHSpan g (cycloStep fun i ↦ (A k).eval (qParam ^ i) * g k i) := fun k ↦ by
    have e1 : (cycloStep fun i ↦ (A k).eval (qParam ^ i) * g k i) = fun j ↦
        ((A k).comp (C qParam⁻¹ * X)).eval (qParam ^ j) * cycloStep (g k) j +
          (twHTwist (A k)).eval (qParam ^ j) * g k j :=
      funext fun j ↦ twH_cycloStep_polyMul (A k) (g k) j
    rw [e1]
    exact twHSpan_add (twHSpan_polyMul _ (hg k)) (twHSpan_polyMul _ (twHSpan_gen g k))
  have h1 : TwHSpan g (cycloStep fun i ↦ δ.eval (qParam ^ i) * y i) := by
    have e1 : (fun i ↦ δ.eval (qParam ^ i) * y i) =
        fun i ↦ ∑ k, (A k).eval (qParam ^ i) * g k i := funext e
    have e2 : (cycloStep fun i ↦ ∑ k, (A k).eval (qParam ^ i) * g k i) = fun j ↦
        ∑ k, cycloStep (fun i ↦ (A k).eval (qParam ^ i) * g k i) j :=
      funext fun j ↦ twH_cycloStep_finsetSum Finset.univ _ j
    rw [e1, e2]
    exact twHSpan_sum Finset.univ _ fun k _ ↦ hk k
  have e3 : (fun j ↦ (δ.comp (C qParam⁻¹ * X)).eval (qParam ^ j) * cycloStep y j) = fun j ↦
      cycloStep (fun i ↦ δ.eval (qParam ^ i) * y i) j - (twHTwist δ).eval (qParam ^ j) * y j :=
    funext fun j ↦ by rw [twH_cycloStep_polyMul, add_sub_cancel_right]
  rw [e3]
  exact twHSpan_sub h1 (twHSpan_polyMul _ hy')

/-- A span whose generators are mapped into it by `V` contains all `V^s y`, `y` in the span. -/
theorem twHSpan_iterate_cycloStep {ι : Type*} [Fintype ι] {g : ι → ℕ → RatFunc ℚ}
    {y : ℕ → RatFunc ℚ} (hg : ∀ k, TwHSpan g (cycloStep (g k))) (hy : TwHSpan g y) (s : ℕ) :
    TwHSpan g (cycloStep^[s] y) := by
  induction s with
  | zero => exact hy
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    exact twHSpan_cycloStep hg ih

end AJConjecture
