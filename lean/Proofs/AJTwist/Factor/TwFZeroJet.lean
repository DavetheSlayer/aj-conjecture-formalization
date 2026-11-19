import Mathlib
import AJTwist.Quantum.TwQZeroCoeff
import AJTwist.Factor.TwFRankOneJet
import AJConjecture.QAlgOreMulAssoc

/-!
# The first jet of a right factor of order one of `P_0` (TwF, unit F4)

Source: revision 5, Section 5.6 (`operators.tex`): "Now set `q = e^ε` and
`r_0 = 1 + ε f(x) + ⋯`. The monic residue gives coefficient `4/x` for `f` in the first-order
Riccati equation. The derivative of `∑ b_i/b_3` at `q = 1` is `-2(x + 1)/(x(x - 1))` by
eq. (zero-coeff). Thus `f(x) = (x + 1)/(2(x - 1))`."

For the explicit operator `twZeroExplicitOp = ∑_k b_(3-k)(t⁴, t¹² M²) L^k` (forward convention):
* `eval_one_derivative_specialize_twZeroExplicitOp`: `(∂_L P₀)(M, 1) = 4 M² (M² - 1)²`;
* `eval_one_specializeJet_twZeroExplicitOp`: `P₁(M, 1) = -8 M² (M² - 1)(M² + 1)`
  (the first jet at `t = -1`, `q = t⁴`, of `∑_k b_(3-k)(q, q³ M²)`);
* `nodeNumer_mul_of_rightFactor_twZeroExplicitOp`: for a right pseudo-factor `R` of degree one
  with `R₀(M, 1) = 0`: `N_R (M² - 1) = Δ_R · 2 (M² + 1)`, i.e. the logarithmic first jet of
  `r₀/r₁` is `2 (M² + 1)/(M² - 1)`. With `x = M²` and `d/dt = -4 d/dε` at `t = -1`, and
  `u = L⁻¹`, this is the paper's `f = (x + 1)/(2(x - 1))`.
* `exists_pseudoFactor_twZeroExplicitOp`: a right pseudo-factor of `twTransferOp 0` is one of
  `twZeroExplicitOp` (`twZeroExplicitOp_mul_eq`, `twZero_scalars_ne_zero`).

Route: the first two are computations with the explicit `twZeroB` (`specialize`, `specializeJet`
of a sum of four monomials; `Polynomial.comp`, `derivative`, `eval`); the third is
`nodeNumer_mul_of_rankOne_right` with these values, cancelling `4 M² (M² - 1)`.
Checked by computer algebra (scratch `check_zero.py`, `check_zero2.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Base change `ℤ[M] → ℂ[M]` is injective. -/
private theorem map_intCast_injective_twfZeroJet :
    Function.Injective (Polynomial.map (Int.castRingHom ℂ)) :=
  Polynomial.map_injective (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int

/-- The first jet of coefficients is additive. -/
private theorem coeffJet_add_twfZeroJet (a b : Coeff) :
    coeffJet (a + b) = coeffJet a + coeffJet b := by
  apply map_intCast_injective_twfZeroJet
  rw [← complexJet_coeffToComplex, map_add, complexJet_add, Polynomial.map_add,
    complexJet_coeffToComplex, complexJet_coeffToComplex]

/-- The Leibniz rule for the first jet of coefficients. -/
private theorem coeffJet_mul_twfZeroJet (a b : Coeff) :
    coeffJet (a * b) = coeffJet a * b.map (Polynomial.evalRingHom (-1)) +
      a.map (Polynomial.evalRingHom (-1)) * coeffJet b := by
  apply map_intCast_injective_twfZeroJet
  rw [← complexJet_coeffToComplex, map_mul, complexJet_mul, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_mul, complexJet_coeffToComplex,
    complexJet_coeffToComplex, complexSpec_coeffToComplex, complexSpec_coeffToComplex]

/-- The first jet of a polynomial in `t` alone. -/
private theorem coeffJet_C_twfZeroJet (a : ℤ[X]) :
    coeffJet (C a) = C ((derivative a).eval (-1)) := by
  rw [coeffJet, sum_C_index, monomial_zero_left]
  rw [derivative_zero, eval_zero, monomial_zero_right]

/-- The first jet of a power of `M`. -/
private theorem coeffJet_X_pow_twfZeroJet (n : ℕ) : coeffJet (X ^ n : Coeff) = 0 := by
  rw [coeffJet, X_pow_eq_monomial, sum_monomial_index]
  · simp
  · simp

/-- The first jet of an opposite. -/
private theorem coeffJet_neg_twfZeroJet (a : Coeff) : coeffJet (-a) = -coeffJet a := by
  have h := coeffJet_add_twfZeroJet a (-a)
  rw [add_neg_cancel, coeffJet_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The first jet of a difference. -/
private theorem coeffJet_sub_twfZeroJet (a b : Coeff) :
    coeffJet (a - b) = coeffJet a - coeffJet b := by
  rw [sub_eq_add_neg, coeffJet_add_twfZeroJet, coeffJet_neg_twfZeroJet, sub_eq_add_neg]

/-- The first jet of a square. -/
private theorem coeffJet_sq_twfZeroJet (a : Coeff) :
    coeffJet (a ^ 2) = 2 * a.map (Polynomial.evalRingHom (-1)) * coeffJet a := by
  rw [sq, coeffJet_mul_twfZeroJet]
  ring

/-- The first jet of a numeral. -/
private theorem coeffJet_ofNat_twfZeroJet (n : ℕ) [n.AtLeastTwo] :
    coeffJet (OfNat.ofNat n : Coeff) = 0 := by
  rw [← C_ofNat, coeffJet_C_twfZeroJet, ← C_ofNat, derivative_C, eval_zero, C_0]

/-- The first jet of `1`. -/
private theorem coeffJet_one_twfZeroJet : coeffJet (1 : Coeff) = 0 := by
  rw [← C_1, coeffJet_C_twfZeroJet, derivative_one, eval_zero, C_0]

/-- The four coefficients of the explicit operator. -/
private theorem coeff_twZeroExplicitOp_twfZeroJet (k : Fin 4) :
    twZeroExplicitOp.coeff (k : ℕ) =
      (twZeroB (X ^ 4 : ℤ[X]) (Fin.rev k)).comp (C (X ^ 12) * X ^ 2) := by
  rw [twZeroExplicitOp, finsetSum_coeff, Finset.sum_eq_single k]
  · rw [coeff_C_mul, coeff_X_pow, ite_eq_left rfl, mul_one]
  · intro j _ hj
    rw [coeff_C_mul, coeff_X_pow, ite_eq_right (fun h ↦ hj (Fin.ext h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- The four coefficients of the explicit operator, expanded. -/
private theorem coeff_twZeroExplicitOp_explicit_twfZeroJet :
    twZeroExplicitOp.coeff 0 = -(C (X ^ 4) * (C (X ^ 12) * X ^ 2) ^ 2 *
        (C (X ^ 12) * X ^ 2 - C ((X ^ 4) ^ 3)) * (C (X ^ 12) * X ^ 2 - C (X ^ 4))) ∧
      twZeroExplicitOp.coeff 1 = C ((X ^ 4) ^ 2) * (C (X ^ 12) * X ^ 2 - C ((X ^ 4) ^ 2)) ^ 2 *
        (C ((X ^ 4) ^ 3) - C ((X ^ 4) ^ 2) * (C (X ^ 12) * X ^ 2) -
          3 * C (X ^ 4) * (C (X ^ 12) * X ^ 2) + 2 * (C (X ^ 12) * X ^ 2) ^ 2) ∧
      twZeroExplicitOp.coeff 2 = -(C ((X ^ 4) ^ 3) * (C (X ^ 12) * X ^ 2 - C (X ^ 4)) ^ 2 *
        (2 * C ((X ^ 4) ^ 3) - C ((X ^ 4) ^ 2) * (C (X ^ 12) * X ^ 2) -
          3 * C (X ^ 4) * (C (X ^ 12) * X ^ 2) + (C (X ^ 12) * X ^ 2) ^ 2)) ∧
      twZeroExplicitOp.coeff 3 = C ((X ^ 4) ^ 5) * (C (X ^ 12) * X ^ 2 - C ((X ^ 4) ^ 2)) *
        (C (X ^ 12) * X ^ 2 - 1) := by
  have h0 := coeff_twZeroExplicitOp_twfZeroJet 0
  have h1 := coeff_twZeroExplicitOp_twfZeroJet 1
  have h2 := coeff_twZeroExplicitOp_twfZeroJet 2
  have h3 := coeff_twZeroExplicitOp_twfZeroJet 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl]
    at h0 h1 h2 h3
  rw [h0, h1, h2, h3]
  simp only [twZeroB, show Fin.rev (0 : Fin 4) = 3 from rfl,
    show Fin.rev (1 : Fin 4) = 2 from rfl, show Fin.rev (2 : Fin 4) = 1 from rfl,
    show Fin.rev (3 : Fin 4) = 0 from rfl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, mul_comp,
    sub_comp, add_comp, neg_comp, pow_comp, C_comp, X_comp, one_comp, ofNat_comp,
    Nat.cast_ofNat, and_self]

/-- The explicit operator has order at most three. -/
private theorem natDegree_twZeroExplicitOp_le_twfZeroJet : twZeroExplicitOp.natDegree ≤ 3 := by
  unfold twZeroExplicitOp
  refine natDegree_sum_le_of_forall_le _ _ fun k _ ↦ ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- `(∂_L P₀)(M, 1) = 4 M² (M² - 1)²` for the explicit operator of `a = 0`. -/
theorem eval_one_derivative_specialize_twZeroExplicitOp :
    (derivative (specialize twZeroExplicitOp)).eval 1 = 4 * X ^ 2 * (X ^ 2 - 1) ^ 2 := by
  have hdeg : (specialize twZeroExplicitOp).natDegree < 4 := by
    have h : (specialize twZeroExplicitOp).natDegree ≤ twZeroExplicitOp.natDegree := by
      rw [specialize, coe_mapRingHom]
      exact natDegree_map_le
    exact Nat.lt_succ_of_le (h.trans natDegree_twZeroExplicitOp_le_twfZeroJet)
  obtain ⟨-, h1, h2, h3⟩ := coeff_twZeroExplicitOp_explicit_twfZeroJet
  have hsum : (derivative (specialize twZeroExplicitOp)).eval 1 =
      (specialize twZeroExplicitOp).coeff 1 + 2 * (specialize twZeroExplicitOp).coeff 2 +
        3 * (specialize twZeroExplicitOp).coeff 3 := by
    conv_lhs => rw [(specialize twZeroExplicitOp).as_sum_range' 4 hdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, derivative_add,
      derivative_monomial, eval_add, eval_monomial, one_pow, mul_one, Nat.cast_zero, mul_zero,
      zero_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [hsum, coeff_specialize, coeff_specialize, coeff_specialize, h1, h2, h3]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_neg, Polynomial.map_one, Polynomial.map_ofNat, map_C, map_X,
    coe_evalRingHom, eval_pow, eval_X]
  norm_num
  ring

/-- `P₁(M, 1) = -8 M² (M² - 1)(M² + 1)` for the explicit operator of `a = 0`. -/
theorem eval_one_specializeJet_twZeroExplicitOp :
    (specializeJet twZeroExplicitOp).eval 1 = -(8 * X ^ 2 * (X ^ 2 - 1) * (X ^ 2 + 1)) := by
  have hdeg : (specializeJet twZeroExplicitOp).natDegree < 4 := by
    refine Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_)
    rw [coeff_specializeJet, coeff_eq_zero_of_natDegree_lt
      (natDegree_twZeroExplicitOp_le_twfZeroJet.trans_lt hk), coeffJet_zero]
  obtain ⟨h0, h1, h2, h3⟩ := coeff_twZeroExplicitOp_explicit_twfZeroJet
  have hj2 : coeffJet (2 : Coeff) = 0 := coeffJet_ofNat_twfZeroJet 2
  have hj3 : coeffJet (3 : Coeff) = 0 := coeffJet_ofNat_twfZeroJet 3
  have hjX : coeffJet (X : Coeff) = 0 := by
    have := coeffJet_X_pow_twfZeroJet 1
    rwa [pow_one] at this
  rw [eval_eq_sum_range' hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_specializeJet, one_pow,
    mul_one, zero_add]
  rw [h0, h1, h2, h3]
  simp only [coeffJet_neg_twfZeroJet, coeffJet_add_twfZeroJet, coeffJet_sub_twfZeroJet,
    coeffJet_mul_twfZeroJet, coeffJet_sq_twfZeroJet, coeffJet_C_twfZeroJet, hjX, hj2, hj3,
    coeffJet_one_twfZeroJet]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_ofNat, map_C, map_X, coe_evalRingHom, eval_pow, eval_X,
    derivative_pow, derivative_X, eval_mul, eval_C]
  norm_num
  ring

/-- The logarithmic first jet of a right pseudo-factor of degree one of the explicit operator of
`a = 0` is `2 (M² + 1)/(M² - 1)`. -/
theorem nodeNumer_mul_of_rightFactor_twZeroExplicitOp {β : Coeff}
    (hβ : β.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0) {S R : RecOp}
    (h : C β * twZeroExplicitOp = oreMul coeffShift S R) (hR : R.natDegree = 1)
    (hR1 : (specialize R).eval 1 = 0) :
    nodeNumer R * (X ^ 2 - 1) = nodeDenom R * (2 * (X ^ 2 + 1)) := by
  have hkey := nodeNumer_mul_of_rankOne_right hβ h hR hR1
  rw [eval_one_derivative_specialize_twZeroExplicitOp,
    eval_one_specializeJet_twZeroExplicitOp] at hkey
  have h2 : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
    have := (monic_X_pow_sub_C (1 : ℤ) (two_ne_zero)).ne_zero
    rwa [map_one] at this
  have h4 : (4 : ℤ[X]) ≠ 0 := by
    rw [← C_ofNat]
    exact C_ne_zero.mpr (by norm_num)
  have hc : (4 * X ^ 2 * (X ^ 2 - 1) : ℤ[X]) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 X_ne_zero)) h2
  refine mul_left_cancel₀ hc ?_
  linear_combination hkey

/-- A right pseudo-factor of `P_0` is a right pseudo-factor of the explicit operator; the
scalar keeps a nonzero value at `t = -1`. -/
theorem exists_pseudoFactor_twZeroExplicitOp {β : Coeff} {S R : RecOp}
    (h : C β * twTransferOp 0 = oreMul coeffShift S R) :
    ∃ S' : RecOp, C (β * (twDet 3 (X ^ 4 : ℤ[X])).comp (C (X ^ 12) * X ^ 2)) * twZeroExplicitOp =
      oreMul coeffShift S' R := by
  refine ⟨C ((twZeroBeta (X ^ 4 : ℤ[X])).comp (C (X ^ 12) * X ^ 2)) * S, ?_⟩
  rw [C_mul, mul_assoc, twZeroExplicitOp_mul_eq, mul_left_comm (C β), h,
    ← oreMul_C_left coeffShift _ (oreMul coeffShift S R), ← oreMul_assoc, oreMul_C_left]

end AJConjecture
