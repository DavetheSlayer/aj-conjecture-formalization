import Mathlib
import AJConjecture.RecurrenceIdeal
import AJConjecture.QAlgOpApplyFieldBasic
import AJFamily.Quantum.FamTransferOp
import AJTwist.Quantum.TwQWindowCramer
import AJTwist.Quantum.TwQWindowMap
import AJTwist.Quantum.TwQWindowKernel
import AJHandoff.TorusQuantum.PairQFormulaBasic

/-!
# The recurrence operator of a target polynomial (Units Q3, Q4)

Source: revision 5, Section 3.3, eq. (physicalrow): `P = ∑_i a_i(q, M²) u^i` with
`𝒩 = ∑_i a_i Δ R_i`; Section 6.3: the operators `D^{[z]}` with `J^z = ∑_i d_i^{[z]} Δ R_i`.

`twCramerOp d T` is the operator `∑_k c_(d-k)(t⁴, t^(4d) M²) L^k` whose coefficients are the
Cramer numerators of the target `T` (a polynomial in `J` and `x` with coefficients in `ℤ[t]`) in
the pole basis of the window `d`: in the library's forward convention it is `L^d` times the
paper's backward operator `∑_i a_i u^i` (`T = ∑_i a_i Δ R_i`), multiplied on the left by the
nonzero scalar `det / ∏_{r<d} q^r (x - q^(r+1))`. The library's `famTransferOp m` is
`twCramerOp (2m + 3) (famTarget m t⁴)` (`famTransferOp_eq_twCramerOp`, by `rfl`).

`twQ_opApplyField_cramerOp` is the outer half of the transfer, for every target and every input
`u`: at the colours `n ≥ 1`, with `N = n + d > d`,
`(twCramerOp d T · F^u)(n) = det(q^N) ∑_{j<N} G_j(N) T(q^N, q^j) D^u_j`.
("the weight `T / Δ` is implemented on any fixed input by the cleared color-shift relation").
Route: `twQ_reducedFormula_sub_eq_sum_twKernel` and the Cramer identity
`sum_twCoeff_mul_twBasisPoly` evaluated at `(q^N, q^j)`, as in
`pairQ_sum_famCoeff_mul_reducedFormula`, `pairQ_opApplyField_famTransferOp`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The coefficient map `ℤ[t] → ℚ(t)`. -/
def twTHom : ℤ[X] →+* RatFunc ℚ :=
  Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X

theorem twTHom_X_pow_four : twTHom (X ^ 4) = qParam := by
  rw [twTHom, map_pow, coe_eval₂RingHom, eval₂_X, qParam]

/-- The operator `∑_k c_(d-k)(t⁴, t^(4d) M²) L^k` of order at most `d` whose coefficients are
the Cramer numerators of the target `T` in the pole basis of the window `d`. -/
def twCramerOp (d : ℕ) (T : ℤ[X][X][X]) : RecOp :=
  ∑ k : Fin (d + 1),
    C ((twCoeff d (X ^ 4 : ℤ[X]) T (Fin.rev k)).comp (C (X ^ (4 * d)) * X ^ 2)) * X ^ (k : ℕ)

/-- The library's transfer operator is the operator of the target `famTarget m` in the window
`2m + 3`. -/
theorem famTransferOp_eq_twCramerOp (m : ℕ) :
    famTransferOp m = twCramerOp (2 * m + 3) (famTarget m (X ^ 4)) := rfl

/-- The inhomogeneous recurrence of a target: for `N > d` and every input `u`,
`∑_{i ≤ d} c_i(q^N) F_(N-i) = det(q^N) ∑_{j<N} G_j(N) T(q^N, q^j) D_j`. -/
theorem twQ_sum_twCoeff_mul_reducedFormula (d : ℕ) (T : (RatFunc ℚ)[X][X])
    (hT : T.natDegree ≤ d) (u : ℕ → RatFunc ℚ) {N : ℕ} (hN : d + 1 ≤ N) :
    ∑ i : Fin (d + 1),
        (twCoeff d qParam T i).eval (qParam ^ (N : ℤ)) * pairQReducedFormula u (N - i) =
      (twDet d qParam).eval (qParam ^ (N : ℤ)) *
        ∑ j ∈ Finset.range N, twKernel d j N *
          T.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * pairQCycloCoeff u j := by
  have hcr : ∀ j : ℕ, ∑ i : Fin (d + 1),
      (twCoeff d qParam T i).eval (qParam ^ (N : ℤ)) *
        (twBasisPoly d qParam i).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) =
      (twDet d qParam).eval (qParam ^ (N : ℤ)) *
        T.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) := by
    intro j
    have h := congrArg (evalEval (qParam ^ (N : ℤ)) (qParam ^ j))
      (sum_twCoeff_mul_twBasisPoly d qParam T hT)
    simpa only [evalEval_finsetSum, evalEval_mul, evalEval_C] using h
  have hF : ∀ i : Fin (d + 1), (twCoeff d qParam T i).eval (qParam ^ (N : ℤ)) *
      pairQReducedFormula u (N - i) =
        ∑ j ∈ Finset.range N, twKernel d j N * pairQCycloCoeff u j *
          ((twCoeff d qParam T i).eval (qParam ^ (N : ℤ)) *
            (twBasisPoly d qParam i).evalEval (qParam ^ (N : ℤ)) (qParam ^ j)) := by
    intro i
    have hi : (i : ℕ) ≤ d := by have := i.isLt; omega
    rw [twQ_reducedFormula_sub_eq_sum_twKernel d u hN hi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  simp only [hF]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hcr]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- The action is additive in the operator, for finite sums. -/
private theorem opApplyField_finsetSum_left_cramerOp {ι : Type*} (s : Finset ι) (P : ι → RecOp)
    (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (∑ k ∈ s, P k) f n = ∑ k ∈ s, opApplyField (P k) f n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, opApplyField, sum_zero_index]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, opApplyField_add_left, ih]

/-- The value at the colour `n` of a coefficient of `twCramerOp d T` is the Cramer numerator
over `ℚ(t)` at `x = q^(n+d)`. -/
private theorem evalAtField_twCoeff_comp_cramerOp (d : ℕ) (T : ℤ[X][X][X]) (n : ℤ)
    (i : Fin (d + 1)) :
    evalAtField n ((twCoeff d (X ^ 4 : ℤ[X]) T i).comp (C (X ^ (4 * d)) * X ^ 2)) =
      (twCoeff d qParam (T.map (Polynomial.mapRingHom twTHom)) i).eval
        (qParam ^ (n + (d : ℤ))) := by
  have hx : eval₂ twTHom (RatFunc.X ^ (2 * n)) (C (X ^ (4 * d)) * X ^ 2) =
      qParam ^ (n + (d : ℤ)) := by
    rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, map_pow, twTHom, coe_eval₂RingHom, eval₂_X,
      qParam, ← zpow_natCast RatFunc.X 4, ← zpow_natCast RatFunc.X (4 * d),
      ← zpow_natCast _ 2, ← zpow_mul, ← zpow_mul, ← zpow_add₀ RatFunc.X_ne_zero]
    congr 1
    push_cast
    ring
  have h : evalAtField n = Polynomial.eval₂RingHom twTHom (RatFunc.X ^ (2 * n)) := rfl
  rw [h, coe_eval₂RingHom, eval₂_comp, hx, eval₂_eq_eval_map, map_twCoeff, twTHom_X_pow_four]

/-- The operator of a target applied to the even reduced sequence of an input `u`, at the
colours `n ≥ 1`. -/
theorem twQ_opApplyField_cramerOp (d : ℕ) (T : ℤ[X][X][X]) (hT : T.natDegree ≤ d)
    (u : ℕ → RatFunc ℚ) {n : ℤ} (hn : 1 ≤ n) :
    opApplyField (twCramerOp d T) (pairQReducedFormulaEven u) n =
      (twDet d qParam).eval (qParam ^ (n + (d : ℤ))) *
        ∑ j ∈ Finset.range (n + (d : ℤ)).toNat, twKernel d j (n + d) *
          (T.map (Polynomial.mapRingHom twTHom)).evalEval (qParam ^ (n + (d : ℤ))) (qParam ^ j) *
            pairQCycloCoeff u j := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
  have hk : 1 ≤ k := by exact_mod_cast hn
  have hT' : (T.map (Polynomial.mapRingHom twTHom)).natDegree ≤ d := natDegree_map_le.trans hT
  have h := twQ_sum_twCoeff_mul_reducedFormula d _ hT' u (N := k + d) (by omega)
  have hcast : ((k + d : ℕ) : ℤ) = (k : ℤ) + d := by push_cast; ring
  have htoNat : ((k : ℤ) + (d : ℤ)).toNat = k + d := by omega
  rw [hcast] at h
  rw [htoNat, ← h, twCramerOp, opApplyField_finsetSum_left_cramerOp]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i ↦ ?_
  rw [C_mul_X_pow_eq_monomial, opApplyField_monomial, evalAtField_twCoeff_comp_cramerOp,
    Fin.revPerm_apply, pairQReducedFormulaEven]
  congr 2
  rw [Fin.val_rev]
  omega

end AJConjecture
