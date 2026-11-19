import Mathlib
import AJTwist.Quantum.TwQTransferOp
import AJTwist.Quantum.TwQAdjointTarget
import AJTwist.Quantum.TwQWindowDet

/-!
# The outer transfer: `P_a` on the reduced sequence of an arbitrary input (Unit Q4)

Source: revision 5, Section 3.3, eq. (physicalforcing), before the input is specified: for every
integer `a`, every input `u` and every colour `n ≥ 1` (so `N = n + d > d`, `d = twWindow a`),
`(P_a F^u)(n) = det(q^N) (q^d q^N)^(|a|+1) ∑_{j<N} G_j(N) (p_a D^u)_j`.

"Thus `P_a` is an inhomogeneous row on the actual reduced tail": the operator depends only on
`a`; the input enters through the inner operator `p_a` applied to `D^u`. For `a = rs`,
`u = pairQOddColor r s` this is `pairQ_opApplyField_famTransferOp` before the truncation of the
sum. `twQ_opApplyField_weightOp` is the same statement for the weight operators `D^{[z]}`.

Checked at random points for `a ∈ {-6, -2, -1, 0, 1, 2, 6}` (scratch `check_transfer.py`, column
`outer`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The scalar `det(q^N) (q^d q^N)^(|a|+1)` between the paper's normalization of `P_a F` and
the Cramer normalization. -/
def twTransferScalar (a : ℤ) (N : ℤ) : RatFunc ℚ :=
  (twDet (twWindow a) qParam).eval (qParam ^ N) *
    (qParam ^ twWindow a * qParam ^ N) ^ (a.natAbs + 1)

/-- The scalar does not vanish on the tail `N > d`. -/
theorem twTransferScalar_ne_zero (a : ℤ) {N : ℤ} (hN : (twWindow a : ℤ) + 1 ≤ N) :
    twTransferScalar a N ≠ 0 := by
  have hq := qParam_ne_zero
  exact mul_ne_zero (twDet_eval_ne_zero _ hN)
    (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hq) (zpow_ne_zero _ hq)))

/-- The outer transfer for `P_a` and an arbitrary input. -/
theorem twQ_opApplyField_transferOp (a : ℤ) (u : ℕ → RatFunc ℚ) {n : ℤ} (hn : 1 ≤ n) :
    opApplyField (twTransferOp a) (pairQReducedFormulaEven u) n =
      twTransferScalar a (n + (twWindow a : ℤ)) *
        ∑ j ∈ Finset.range (n + (twWindow a : ℤ)).toNat,
          twKernel (twWindow a) j (n + twWindow a) * twDefect a u j := by
  have hT : (twTarget a (X ^ 4 : ℤ[X])).natDegree ≤ twWindow a := natDegree_twTarget_le a _
  have hmap : (twTarget a (X ^ 4 : ℤ[X])).map (Polynomial.mapRingHom twTHom) =
      twTarget a qParam := by
    rw [map_twTarget, twTHom_X_pow_four]
  have hcast : (((n + (twWindow a : ℤ)).toNat : ℕ) : ℤ) = n + (twWindow a : ℤ) :=
    Int.toNat_of_nonneg (by omega)
  have hadj := twQ_sum_twKernel_mul_twTarget a u (N := (n + (twWindow a : ℤ)).toNat) (by omega)
  rw [hcast] at hadj
  rw [twTransferOp, twQ_opApplyField_cramerOp _ _ hT u hn, hmap, hadj, twTransferScalar,
    mul_assoc]

/-- The weight operator `D^{[z]}` implements the weight `J^z / Δ` on an arbitrary input. -/
theorem twQ_opApplyField_weightOp (d z : ℕ) (hz : z ≤ d) (u : ℕ → RatFunc ℚ) {n : ℤ}
    (hn : 1 ≤ n) :
    opApplyField (twWeightOp d z) (pairQReducedFormulaEven u) n =
      (twDet d qParam).eval (qParam ^ (n + (d : ℤ))) *
        ∑ j ∈ Finset.range (n + (d : ℤ)).toNat,
          twKernel d j (n + d) * (qParam ^ j) ^ z * pairQCycloCoeff u j := by
  have hT : (X ^ z : ℤ[X][X][X]).natDegree ≤ d := (natDegree_X_pow_le z).trans hz
  rw [twWeightOp, twQ_opApplyField_cramerOp d _ hT u hn]
  simp only [Polynomial.map_pow, map_X, evalEval_pow, evalEval_X]

end AJConjecture
