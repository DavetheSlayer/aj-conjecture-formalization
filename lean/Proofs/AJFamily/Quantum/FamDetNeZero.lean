import Mathlib
import AJFamily.Quantum.FamKernelShift
import AJConjecture.QAlgQParamBasic
import AJFamily.Quantum.FamTransferCoeff
import AJFamily.Quantum.FamTransferDegree

/-!
# The family determinant at `x = q^N`

`famDet_eval_ne_zero`: for `N ≥ 2m + 4`, `famDet m q` does not vanish at `x = q^N`; at the points
`J = q^(N-r-1)` the basis polynomials are triangular.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The value at a point of a polynomial of degree at most `2m + 3` in `J`, in terms of its
coefficients. -/
private theorem evalEval_eq_sum_fin_of_natDegree_lt_fam {R : Type*} [CommRing R] (m : ℕ)
    (p : R[X][X]) (x y : R) (hp : p.natDegree < 2 * m + 4) :
    p.evalEval x y = ∑ k : Fin (2 * m + 4), y ^ (k : ℕ) * (p.coeff k).eval x := by
  rw [evalEval, eval_eq_sum_range' hp, eval_finsetSum,
    Fin.sum_univ_eq_sum_range (fun k ↦ y ^ k * (p.coeff k).eval x) (2 * m + 4)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [eval_mul, eval_pow, eval_C, mul_comm]

/-- Differences of distinct integer powers of `q` do not vanish. -/
private theorem qParam_zpow_sub_zpow_ne_zero_fam {a b : ℤ} (hab : a ≠ b) :
    qParam ^ a - qParam ^ b ≠ 0 := fun h ↦
  hab (qParam_zpow_injective (sub_eq_zero.mp h))

/-- The `i`-th family basis polynomial vanishes at `x = q^N`, `J = q^(N-r-1)` when `r < i`. -/
private theorem famBasisPoly_evalEval_pivot_eq_zero (m : ℕ) (N : ℤ) {r i : ℕ} (hri : r < i) :
    (famBasisPoly m qParam i).evalEval (qParam ^ N) (qParam ^ (N - r - 1)) = 0 := by
  rw [evalEval_famBasisPoly_eq]
  refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_range.mpr hri) ?_) _
  refine mul_eq_zero_of_right _ (sub_eq_zero.mpr ?_)
  rw [← zpow_natCast, ← zpow_add₀ qParam_ne_zero]
  congr 1
  push_cast
  ring

/-- The `r`-th family basis polynomial does not vanish at `x = q^N`, `J = q^(N-r-1)`, when
`N ≥ 2m + 4`. -/
private theorem famBasisPoly_evalEval_pivot_ne_zero (m : ℕ) {N : ℤ}
    (hN : 2 * (m : ℤ) + 4 ≤ N) {r : ℕ} (hr : r ≤ 2 * m + 3) :
    (famBasisPoly m qParam r).evalEval (qParam ^ N) (qParam ^ (N - r - 1)) ≠ 0 := by
  rw [evalEval_famBasisPoly_eq]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun s hs ↦ ?_)
    (Finset.prod_ne_zero_iff.mpr fun s hs ↦ ?_)
  · have hs' : s < r := Finset.mem_range.mp hs
    refine mul_ne_zero ?_ ?_
    · have h := qParam_zpow_sub_zpow_ne_zero_fam (a := (s : ℤ)) (b := N) (by omega)
      rwa [zpow_natCast] at h
    · have h := qParam_zpow_sub_zpow_ne_zero_fam (a := N)
        (b := ((s + 1 : ℕ) : ℤ) + (N - r - 1)) (by omega)
      rwa [zpow_add₀ qParam_ne_zero, zpow_natCast] at h
  · have hs' : r ≤ s ∧ s < 2 * m + 3 := Finset.mem_Ico.mp hs
    refine mul_ne_zero ?_ ?_
    · have h := qParam_zpow_sub_zpow_ne_zero_fam (a := N) (b := ((s + 1 : ℕ) : ℤ)) (by omega)
      rwa [zpow_natCast] at h
    · have h := qParam_zpow_sub_zpow_ne_zero_fam (a := (s : ℤ)) (b := N + (N - r - 1))
        (by omega)
      rwa [zpow_add₀ qParam_ne_zero, zpow_natCast] at h

/-- The family transfer determinant does not vanish at `x = q^N` for `N ≥ 2m + 4`. -/
theorem famDet_eval_ne_zero (m : ℕ) {N : ℤ} (hN : 2 * (m : ℤ) + 4 ≤ N) :
    (famDet m qParam).eval (qParam ^ N) ≠ 0 := by
  set V : Matrix (Fin (2 * m + 4)) (Fin (2 * m + 4)) (RatFunc ℚ) :=
    Matrix.of fun r k ↦ (qParam ^ (N - (r : ℕ) - 1)) ^ (k : ℕ) with hV
  set M' : Matrix (Fin (2 * m + 4)) (Fin (2 * m + 4)) (RatFunc ℚ) :=
    (evalRingHom (qParam ^ N)).mapMatrix (famMatrix m qParam) with hM'
  have hE : ∀ r i : Fin (2 * m + 4), (V * M') r i =
      (famBasisPoly m qParam i).evalEval (qParam ^ N) (qParam ^ (N - (r : ℕ) - 1)) := by
    intro r i
    rw [evalEval_eq_sum_fin_of_natDegree_lt_fam m _ _ _ (lt_of_le_of_lt
      (natDegree_famBasisPoly_le m qParam (by omega)) (by omega)), Matrix.mul_apply]
    rfl
  have htri : (V * M').IsLowerTriangular := by
    intro r i hri
    rw [hE]
    exact famBasisPoly_evalEval_pivot_eq_zero m N
      (Fin.lt_def.mp (OrderDual.toDual_lt_toDual.mp hri))
  have hdet : (V * M').det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular _ htri, Finset.prod_ne_zero_iff]
    intro r _
    rw [hE]
    exact famBasisPoly_evalEval_pivot_ne_zero m hN (by omega)
  rw [Matrix.det_mul] at hdet
  have hM : (famDet m qParam).eval (qParam ^ N) = M'.det := by
    rw [famDet, ← coe_evalRingHom, RingHom.map_det]
  rw [hM]
  exact right_ne_zero_of_mul hdet

end AJConjecture
