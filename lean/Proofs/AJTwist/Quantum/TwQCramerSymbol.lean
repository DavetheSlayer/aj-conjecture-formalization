import Mathlib
import AJConjecture.QAlgDualJet
import AJConjecture.QAlgSymbolPoly
import AJTwist.Quantum.TwQCramerOp
import AJTwist.Quantum.TwQWindowDetOne

/-!
# The operator of a target at `t = -1` and at `t = -1 + ε` (Unit Q3)

Source: revision 5, Section 3.4 (`transfer.tex`, "The characteristic factor": with the shift
basis `R_i|_{q=1} = ((J - x)/(1 - x J))^i` the symbol of the row is `(1 - x J)^(-d) Π`) and
Section 5.2 (the first jet is read from the solve over the joint local ring).

* `specialize_twCramerOp_eq_sum`: at `t = -1` the coefficients of `twCramerOp d T` are the Cramer
  numerators at `q = 1`, `x = M²`.
* `specialize_twCramerOp_mul_eq`: the symbol is the stationary pullback of the target at
  `q = 1`:
  `(-1)^d (M² - 1)^d (M⁴ - 1)^d · specialize P = det|_{q=1}(M²) · (L + x)^d T|_{q=1}(J(L))`,
  `J = (x L + 1)/(L + x)`, `x = M²`.
* `evalDualPoint_twCramerOp`: at `t = -1 + ε`, `M = m₀`, the coefficients are the Cramer
  numerators at `q = 1 - 4ε`, `x = twDualX d m₀ = (1 - 4dε) m₀²`.

These generalize `specialize_famTransferOp_eq_sum` and `evalDualPoint_famTransferOp`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The dual number `(1 - 4dε) m₀²`, the value of `x = t^(4d) M²` at `t = -1 + ε`, `M = m₀`. -/
def twDualX (d : ℕ) (m₀ : ℂ) : DualNumber ℂ :=
  (1 - ((4 * d : ℕ) : DualNumber ℂ) * DualNumber.eps) * TrivSqZeroExt.inl (m₀ ^ 2)

/-- The specialization at `t = -1` of the operator of a target. -/
theorem specialize_twCramerOp_eq_sum (d : ℕ) (T : ℤ[X][X][X]) :
    specialize (twCramerOp d T) =
      ∑ k : Fin (d + 1),
        C ((twCoeff d (1 : ℤ) (T.map (Polynomial.mapRingHom (Polynomial.evalRingHom (-1 : ℤ))))
          (Fin.rev k)).comp (X ^ 2)) * X ^ (k : ℕ) := by
  have hq : (Polynomial.evalRingHom (-1 : ℤ)) (X ^ 4) = 1 := by
    rw [coe_evalRingHom, eval_pow, eval_X]
    norm_num
  have hx : (C (X ^ (4 * d)) * X ^ 2 : ℤ[X][X]).map
      (Polynomial.evalRingHom (-1 : ℤ)) = X ^ 2 := by
    rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, coe_evalRingHom, eval_pow, eval_X,
      pow_mul]
    norm_num
  rw [twCramerOp, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [specialize, coe_mapRingHom, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C,
    coe_mapRingHom, Polynomial.map_comp, map_twCoeff, hq, hx]

/-- The stationary substitution of the left-hand side of the Cramer identity at `q = 1`. -/
private theorem moebiusSubst_twCramerSum_one_cramerSymbol (d : ℕ) (T : ℤ[X][X]) :
    moebiusSubst d (∑ i : Fin (d + 1), C (twCoeff d (1 : ℤ) T i) * twBasisPoly d (1 : ℤ) i) =
      C ((-1) ^ d * ((X - 1) ^ d * (X ^ 2 - 1) ^ d)) *
        ∑ i : Fin (d + 1), C (twCoeff d (1 : ℤ) T i) * X ^ (d - (i : ℕ)) := by
  rw [moebiusSubst_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [moebiusSubst_C_mul, moebiusSubst_twBasisPoly_one d (by omega)]
  ring

/-- The specialization of the operator of a target, with the sum reversed. -/
private theorem sum_rev_twCoeff_one_cramerSymbol (d : ℕ) (T : ℤ[X][X][X]) :
    ∑ i : Fin (d + 1),
        C ((twCoeff d (1 : ℤ) (T.map (Polynomial.mapRingHom (Polynomial.evalRingHom (-1 : ℤ))))
          i).comp (X ^ 2)) * (X : ℤ[X][X]) ^ (d - (i : ℕ)) =
      specialize (twCramerOp d T) := by
  rw [specialize_twCramerOp_eq_sum, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Fin.revPerm_apply, Fin.val_rev]
  congr 2
  omega

/-- The symbol of the operator of a target is the stationary pullback of the target at
`q = 1`. -/
theorem specialize_twCramerOp_mul_eq (d : ℕ) (T : ℤ[X][X][X]) (hT : T.natDegree ≤ d) :
    C ((-1) ^ d * ((X ^ 2 - 1) ^ d * (X ^ 4 - 1) ^ d)) * specialize (twCramerOp d T) =
      C ((twDet d (1 : ℤ)).comp (X ^ 2)) *
        (moebiusSubst d
          (T.map (Polynomial.mapRingHom (Polynomial.evalRingHom (-1 : ℤ))))).map
            (Polynomial.compRingHom (X ^ 2)) := by
  have hT' : (T.map (Polynomial.mapRingHom (Polynomial.evalRingHom (-1 : ℤ)))).natDegree ≤ d :=
    natDegree_map_le.trans hT
  have h := congrArg (moebiusSubst d) (sum_twCoeff_mul_twBasisPoly d (1 : ℤ) _ hT')
  rw [moebiusSubst_twCramerSum_one_cramerSymbol, moebiusSubst_C_mul] at h
  have h' := congrArg (Polynomial.map (Polynomial.compRingHom (X ^ 2 : ℤ[X]))) h
  have hc : ((-1) ^ d * ((X - 1 : ℤ[X]) ^ d * (X ^ 2 - 1) ^ d)).comp (X ^ 2) =
      (-1) ^ d * ((X ^ 2 - 1) ^ d * (X ^ 4 - 1) ^ d) := by
    simp only [mul_comp, pow_comp, sub_comp, neg_comp, X_comp, one_comp]
    rw [← pow_mul]
  simp only [Polynomial.map_mul, Polynomial.map_sum, Polynomial.map_pow, map_C, map_X,
    coe_compRingHom_apply, hc, sum_rev_twCoeff_one_cramerSymbol] at h'
  exact h'

/-- The dual evaluation of a power of `t` is a power of `-1 + ε`. -/
private theorem dualJetHom_X_pow_cramerSymbol (n : ℕ) :
    dualJetHom (X ^ n) = (-1 + DualNumber.eps) ^ n := by
  rw [map_pow, dualJetHom, coe_eval₂RingHom, eval₂_X]

/-- `(-1 + ε)^n = (-1)^n + n (-1)^(n-1) ε`. -/
private theorem neg_one_add_eps_pow_cramerSymbol (n : ℕ) :
    (-1 + DualNumber.eps : DualNumber ℂ) ^ n =
      TrivSqZeroExt.inl ((-1) ^ n) +
        TrivSqZeroExt.inl ((n : ℂ) * (-1) ^ (n - 1)) * DualNumber.eps := by
  ext
  · simp
  · simp [TrivSqZeroExt.snd_pow]

/-- `(-1 + ε)^(4n) = 1 - 4n ε`. -/
private theorem neg_one_add_eps_pow_four_mul_cramerSymbol (n : ℕ) :
    (-1 + DualNumber.eps : DualNumber ℂ) ^ (4 * n) =
      1 - ((4 * n : ℕ) : DualNumber ℂ) * DualNumber.eps := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [neg_one_add_eps_pow_cramerSymbol]
    have he : Even (4 * n) := ⟨2 * n, by ring⟩
    have ho : Odd (4 * n - 1) := ⟨2 * n - 1, by omega⟩
    rw [he.neg_one_pow, ho.neg_one_pow, ← TrivSqZeroExt.inl_natCast, sub_eq_add_neg]
    ext <;> simp

/-- The value of `q = t⁴` at `t = -1 + ε` is `1 - 4ε`. -/
private theorem dualJetHom_X_pow_four_cramerSymbol : dualJetHom (X ^ 4) = dualQ := by
  have h := neg_one_add_eps_pow_four_mul_cramerSymbol 1
  rw [mul_one] at h
  rw [dualJetHom_X_pow_cramerSymbol, h, dualQ]
  norm_num

/-- The value of `x = t^(4d) M²` at `t = -1 + ε`, `M = m₀` is `(1 - 4dε) m₀²`. -/
private theorem dualJetHom_X_pow_mul_cramerSymbol (d : ℕ) (m₀ : ℂ) :
    dualJetHom (X ^ (4 * d)) * TrivSqZeroExt.inl m₀ ^ 2 = twDualX d m₀ := by
  rw [dualJetHom_X_pow_cramerSymbol, neg_one_add_eps_pow_four_mul_cramerSymbol, twDualX,
    ← TrivSqZeroExt.inl_pow]

/-- The operator of a target at `t = -1 + ε`, `M = m₀`, `L = l`. -/
theorem evalDualPoint_twCramerOp (d : ℕ) (T : ℤ[X][X][X]) (m₀ l : ℂ) :
    evalDualPoint (twCramerOp d T) m₀ l =
      ∑ k : Fin (d + 1),
        (twCoeff d dualQ (T.map (Polynomial.mapRingHom dualJetHom)) (Fin.rev k)).eval
            (twDualX d m₀) * TrivSqZeroExt.inl l ^ (k : ℕ) := by
  rw [evalDualPoint, twCramerOp, Polynomial.map_sum, ← coe_evalEvalRingHom, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coe_evalEvalRingHom, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, coe_mapRingHom,
    Polynomial.map_comp, map_twCoeff, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C,
    evalEval_mul, evalEval_pow, evalEval_X, evalEval_C, eval_comp, eval_mul, eval_pow, eval_X,
    eval_C, dualJetHom_X_pow_four_cramerSymbol, dualJetHom_X_pow_mul_cramerSymbol]

end AJConjecture
