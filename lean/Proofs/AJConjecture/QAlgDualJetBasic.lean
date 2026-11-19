import Mathlib
import AJConjecture.QAlgDualJet
import AJConjecture.QAlgWeylSymbol

/-!
# The dual evaluation is the symbol plus `ε` times the first jet

`dualJetHom a = a(-1) + a'(-1) ε` (Taylor expansion, `ε² = 0`: check on `X^n`, where
`(-1 + ε)^n = (-1)^n + n (-1)^(n-1) ε`). Hence for an operator the two components of
`evalDualPoint P m l` are the values at `(m, l)` of `specialize P` and `specializeJet P`.
Proofs: additivity reduces to monomials `a(t) M^e L^k`.
-/

open Polynomial

namespace AJConjecture

/-- The dual evaluation of a monomial of `ℤ[t]`. -/
private theorem dualJetHom_monomial_dualJetBasic (n : ℕ) (c : ℤ) :
    dualJetHom (monomial n c) = (c : DualNumber ℂ) * (-1 + DualNumber.eps) ^ n := by
  rw [dualJetHom, coe_eval₂RingHom, eval₂_monomial, eq_intCast]

/-- The dual evaluation of an operator is additive. -/
private theorem evalDualPoint_add_dualJetBasic (P Q : RecOp) (m l : ℂ) :
    evalDualPoint (P + Q) m l = evalDualPoint P m l + evalDualPoint Q m l := by
  rw [evalDualPoint, Polynomial.map_add, evalEval_add]
  rfl

/-- The dual evaluation of a monomial operator. -/
private theorem evalDualPoint_monomial_dualJetBasic (k e : ℕ) (a : ℤ[X]) (m l : ℂ) :
    evalDualPoint (monomial k (monomial e a)) m l =
      dualJetHom a * TrivSqZeroExt.inl (m ^ e * l ^ k) := by
  rw [evalDualPoint, map_monomial, coe_mapRingHom, map_monomial, evalEval, eval_monomial,
    eval_mul, eval_pow, eval_C, eval_monomial, TrivSqZeroExt.inl_mul, TrivSqZeroExt.inl_pow,
    TrivSqZeroExt.inl_pow, mul_assoc]

/-- The value at a complex point is additive. -/
theorem evalIntPoint_add (p q : ℤ[X][X]) (m l : ℂ) :
    evalIntPoint (p + q) m l = evalIntPoint p m l + evalIntPoint q m l := by
  rw [evalIntPoint, Polynomial.map_add, evalPoint, eval₂_add]
  rfl

/-- The value at a complex point of a monomial. -/
private theorem evalIntPoint_monomial_dualJetBasic (k e : ℕ) (n : ℤ) (m l : ℂ) :
    evalIntPoint (monomial k (monomial e n)) m l = (n : ℂ) * (m ^ e * l ^ k) := by
  rw [evalIntPoint, map_monomial, coe_mapRingHom, map_monomial, evalPoint, eval₂_monomial,
    coe_evalRingHom, eval_monomial, eq_intCast, mul_assoc]

/-- The first jet of an operator is additive. -/
theorem specializeJet_add (P Q : RecOp) :
    specializeJet (P + Q) = specializeJet P + specializeJet Q := by
  refine sum_add_index P Q _ (fun i ↦ ?_) (fun i c d ↦ ?_)
  · rw [sum_zero_index, monomial_zero_right]
  · rw [← map_add]
    congr 1
    refine sum_add_index c d _ (fun e ↦ ?_) (fun e a b ↦ ?_)
    · rw [derivative_zero, eval_zero, monomial_zero_right]
    · rw [derivative_add, eval_add, map_add]

/-- The first jet of a monomial operator. -/
private theorem specializeJet_monomial_dualJetBasic (k e : ℕ) (a : ℤ[X]) :
    specializeJet (monomial k (monomial e a)) =
      monomial k (monomial e ((derivative a).eval (-1))) := by
  rw [specializeJet, sum_monomial_index _ _ (by rw [sum_zero_index, monomial_zero_right]),
    sum_monomial_index _ _ (by rw [derivative_zero, eval_zero, monomial_zero_right])]

/-- The second component of the dual evaluation of a coefficient is its derivative at
`t = -1`. -/
theorem snd_dualJetHom (a : ℤ[X]) : (dualJetHom a).snd = (((derivative a).eval (-1) : ℤ) : ℂ) := by
  induction a using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, TrivSqZeroExt.snd_add, hp, hq, derivative_add, eval_add, Int.cast_add]
  | monomial n c =>
    rw [dualJetHom_monomial_dualJetBasic, derivative_monomial, eval_monomial]
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_intCast, TrivSqZeroExt.snd_pow,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_neg, TrivSqZeroExt.fst_one, DualNumber.fst_eps,
      add_zero, Nat.pred_eq_sub_one, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_neg,
      TrivSqZeroExt.snd_one, neg_zero, DualNumber.snd_eps, zero_add, smul_eq_mul, mul_one,
      nsmul_eq_mul, TrivSqZeroExt.fst_pow, MulOpposite.op_pow, MulOpposite.op_neg,
      MulOpposite.op_one, TrivSqZeroExt.snd_intCast, smul_zero, Int.reduceNeg, Int.cast_mul,
      Int.cast_natCast, Int.cast_pow, Int.cast_neg, Int.cast_one]
    ring

/-- The second component of the dual evaluation of an operator is the value of its first
jet. -/
theorem snd_evalDualPoint (P : RecOp) (m l : ℂ) :
    (evalDualPoint P m l).snd = evalIntPoint (specializeJet P) m l := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [evalDualPoint_add_dualJetBasic, TrivSqZeroExt.snd_add, hp, hq,
      specializeJet_add, evalIntPoint_add]
  | monomial k c =>
    induction c using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add, evalDualPoint_add_dualJetBasic, TrivSqZeroExt.snd_add, hp, hq,
        specializeJet_add, evalIntPoint_add]
    | monomial e a =>
      rw [evalDualPoint_monomial_dualJetBasic, specializeJet_monomial_dualJetBasic,
        evalIntPoint_monomial_dualJetBasic, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.snd_inl, snd_dualJetHom]
      simp

end AJConjecture
