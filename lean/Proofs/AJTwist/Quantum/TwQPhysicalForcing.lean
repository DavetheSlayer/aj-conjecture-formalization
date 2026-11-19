import Mathlib
import AJTwist.Quantum.TwQOuter
import AJTwist.Quantum.TwQInnerForcing

/-!
# The transfer `P_a F = b` as a finite double sum (Unit Q4)

Source: revision 5, Section 3.3, eq. (physicalforcing):
`(P_a F)(N) = ∑_{0 ≤ n ≤ j < N} C_j(N) K_{jn} g(n) ℛ_η(q^n, q^j) / Δ(q^j)` for `N > d`,
for every `(η, ℓ)`, with `a = η r s - ℓ` and `F` the reduced sequence of the twisted satellite.

In the Cramer normalization of `twTransferOp` (the paper's row times the nonzero scalar
`twTransferScalar a N`, which absorbs the determinant and the clearing power, and with
`twKernel d j N = C_j(N) / P_0(q^N, q^j)` in place of `C_j(N)/Δ(q^j)`), at the colours `n ≥ 1`,
`N = n + d`: `twQ_physicalForcing`. The weight `ℛ_η / Δ` is admissible in the sense of
Section 6.1: its denominator `P_0(q^N, q^j)` does not vanish on the triangle for `N > d`
(`twBasisPoly_zero_evalEval_ne_zero`), and `ℛ_η` is a Laurent polynomial in `(q^n, q^j)` with
coefficients in `ℚ(q)`.

Checked at random points, for both companions and `N = d + 1, d + 2`: `(r, s) = (2,3)` with
`a ∈ {-6, -2, -1, 0, 1, 2, 6}`, `(2,5)` with `a ∈ {-1, 0}`, `(3,4)` with `a ∈ {-1, 0, 1}` (scratch
`check_transfer.py`, column `physical`); and without `IsTorusPair` for `(1,1)`, `(4,2)`, `(3,3)`
(scratch `check_literal.py`).
-/

noncomputable section

namespace AJConjecture

/-- Eq. (physicalforcing): the transfer for the twisted satellite, for every companion sign and
every twist. -/
theorem twQ_physicalForcing (η : Bool) (r s : ℕ) (ℓ : ℤ) {n : ℤ} (hn : 1 ≤ n) :
    opApplyField (twTransferOp (twIndex η r s ℓ)) (twReducedEven η r s ℓ) n =
      twTransferScalar (twIndex η r s ℓ) (n + (twWindow (twIndex η r s ℓ) : ℤ)) *
        ∑ j ∈ Finset.range (n + (twWindow (twIndex η r s ℓ) : ℤ)).toNat,
          ∑ k ∈ Finset.range (j + 1),
            twKernel (twWindow (twIndex η r s ℓ)) j (n + twWindow (twIndex η r s ℓ)) *
              (cycloBilateralKernel j k *
                (qParam ^ (ℓ * (k : ℤ) * ((k : ℤ) + 1)) * twForcingWeight η r s ℓ k j)) := by
  have hF : twReducedEven η r s ℓ = pairQReducedFormulaEven (twInput η r s ℓ) := rfl
  rw [hF, twQ_opApplyField_transferOp _ _ hn]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [twQ_defect_eq_sum, Finset.mul_sum]

end AJConjecture
