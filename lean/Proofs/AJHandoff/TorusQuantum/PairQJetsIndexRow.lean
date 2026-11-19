import Mathlib
import AJFamily.Quantum.FamTransferMap
import AJFamily.Quantum.FamSymbolFacts
import AJHandoff.TorusQuantum.PairQJetsIndexEmbed

/-!
# T-JETS: the backward row of the transfer operator is `∑_i A_i(e^h, z²) u^i`

`pairQJetRow_famTransferOp`: the backward row of `famTransferOp m` is the source's row
`P_m = ∑_i A_i(q, x) u^i` (Cramer coefficients `A_i = famCoeff m q i`) at `q = exp(h)`, `x = z²`:
`t⁴ = exp(h)`, and `σ^d` undoes the factor `t^(4d)` in `x = t^(4d) M²` of the forward operator.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Reflection of a finite sum. -/
private theorem reflect_finsetSum_row {R ι : Type*} [Semiring R] (s : Finset ι) (f : ι → R[X])
    (N : ℕ) : reflect N (∑ i ∈ s, f i) = ∑ i ∈ s, reflect N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, reflect_add, ih]

/-- `t⁴ = exp(h)`. -/
private theorem pairQJetT_pow_four : pairQJetT ^ 4 = PowerSeries.exp ℂ := by
  rw [pairQJetT, neg_pow, ← map_pow, PowerSeries.exp_pow_eq_rescale_exp,
    PowerSeries.rescale_rescale]
  norm_num [PowerSeries.rescale_one]

/-- `t⁴ Q² = 1` for the multiplier `Q = exp(-h/2)` of `σ`. -/
private theorem pairQJetT_pow_four_mul_Q_sq :
    pairQJetT ^ 4 * (pairQJetDilation.Q : PowerSeries ℂ) ^ 2 = 1 := by
  have h := pairQJetT_sq_mul_Q
  calc pairQJetT ^ 4 * (pairQJetDilation.Q : PowerSeries ℂ) ^ 2
      = (pairQJetT ^ 2 * (pairQJetDilation.Q : PowerSeries ℂ)) ^ 2 := by ring
    _ = 1 := by rw [h, one_pow]

/-- **The backward row of the transfer operator.** For `m ≥ 1`,
`pairQJetRow (famTransferOp m) = ∑_i A_i(exp h, z²) u^i`. -/
theorem pairQJetRow_famTransferOp (m : ℕ) (hm : 1 ≤ m) :
    pairQJetRow (famTransferOp m) =
      ∑ i : Fin (2 * m + 4), C ((famCoeff m (PowerSeries.exp ℂ) i).comp (X ^ 2)) * X ^ (i : ℕ) := by
  rw [pairQJetRow, natDegree_famTransferOp m hm, famTransferOp, Polynomial.map_sum,
    reflect_finsetSum_row]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, reflect_C_mul_X_pow,
    revAt_le (by omega : (k : ℕ) ≤ 2 * m + 3), Fin.revPerm_apply, Fin.val_rev]
  congr 2
  · rw [RingHom.comp_apply, RingHom.coe_pow, shiftHom_iterate_eq_comp, pairQJetEmbed,
      coe_mapRingHom, Polynomial.map_comp, map_famCoeff, Polynomial.map_mul,
      map_C, Polynomial.map_pow, map_X, comp_assoc, mul_comp, C_comp, pow_comp, X_comp,
      mul_pow, ← C_pow, ← mul_assoc, ← C_mul, map_pow, map_pow]
    have hX : pairQJetInner X = pairQJetT := by simp [pairQJetInner]
    rw [hX, pairQJetT_pow_four, show pairQJetT ^ (4 * (2 * m + 3)) *
      ((pairQJetDilation.Q : PowerSeries ℂ) ^ (2 * m + 3)) ^ 2 =
        (pairQJetT ^ 4 * (pairQJetDilation.Q : PowerSeries ℂ) ^ 2) ^ (2 * m + 3) by ring,
      pairQJetT_pow_four_mul_Q_sq, one_pow, C_1, one_mul]
  · omega

end AJConjecture
