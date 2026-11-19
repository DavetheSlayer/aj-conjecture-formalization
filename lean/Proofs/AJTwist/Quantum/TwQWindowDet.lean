import Mathlib
import AJTwist.Quantum.TwQWindowKernel
import AJFamily.Quantum.FamDetNeZero

/-!
# The determinant of the pole basis for an arbitrary window (Unit Q3)

Source: revision 5, Section 3.3 ("At `J = q^(i-1)/x` the columns `Δ R_k` for `k < i` vanish, and
`Δ R_i` has a nonzero pivot", for `N > d`) and Section 5.1 ("Joint regularity of the coefficient
solve": at `q = 1` the basis reduces to `(J - x)^i (1 - x J)^(d-i)`, the `d`-th symmetric power
of an invertible change of basis since `x₀² ≠ 1`).

`twDet_eval_ne_zero`: the determinant does not vanish on the colour orbit `x = q^N`, `N > d`.
This is `AJFamily/Quantum/FamDetNeZero.lean` with `2m + 3` replaced by `d`: the product of the
coefficient matrix with the Vandermonde matrix of the points `J = q^(N-r-1)` is triangular with
nonzero pivots. The determinant at `q = 1` is in `AJTwist.Quantum.TwQWindowDetOne`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value at a point of a polynomial of degree at most `d` in `J`, in terms of its
coefficients. -/
private theorem evalEval_eq_sum_fin_of_natDegree_lt_windowDet {R : Type*} [CommRing R] (d : ℕ)
    (p : R[X][X]) (x y : R) (hp : p.natDegree < d + 1) :
    p.evalEval x y = ∑ k : Fin (d + 1), y ^ (k : ℕ) * (p.coeff k).eval x := by
  rw [evalEval, eval_eq_sum_range' hp, eval_finsetSum,
    Fin.sum_univ_eq_sum_range (fun k ↦ y ^ k * (p.coeff k).eval x) (d + 1)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [eval_mul, eval_pow, eval_C, mul_comm]

/-- Differences of distinct integer powers of `q` do not vanish. -/
private theorem qParam_zpow_sub_zpow_ne_zero_windowDet {a b : ℤ} (hab : a ≠ b) :
    qParam ^ a - qParam ^ b ≠ 0 := fun h ↦
  hab (qParam_zpow_injective (sub_eq_zero.mp h))

/-- The `i`-th basis polynomial vanishes at `x = q^N`, `J = q^(N-r-1)` when `r < i`. -/
private theorem twBasisPoly_evalEval_pivot_eq_zero_windowDet (d : ℕ) (N : ℤ) {r i : ℕ}
    (hri : r < i) :
    (twBasisPoly d qParam i).evalEval (qParam ^ N) (qParam ^ (N - r - 1)) = 0 := by
  rw [evalEval_twBasisPoly_eq]
  refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_range.mpr hri) ?_) _
  refine mul_eq_zero_of_right _ (sub_eq_zero.mpr ?_)
  rw [← zpow_natCast, ← zpow_add₀ qParam_ne_zero]
  congr 1
  push_cast
  ring

/-- The `r`-th basis polynomial does not vanish at `x = q^N`, `J = q^(N-r-1)`, when `N > d`. -/
private theorem twBasisPoly_evalEval_pivot_ne_zero_windowDet (d : ℕ) {N : ℤ}
    (hN : (d : ℤ) + 1 ≤ N) {r : ℕ} (hr : r ≤ d) :
    (twBasisPoly d qParam r).evalEval (qParam ^ N) (qParam ^ (N - r - 1)) ≠ 0 := by
  rw [evalEval_twBasisPoly_eq]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun s hs ↦ ?_)
    (Finset.prod_ne_zero_iff.mpr fun s hs ↦ ?_)
  · have hs' : s < r := Finset.mem_range.mp hs
    refine mul_ne_zero ?_ ?_
    · have h := qParam_zpow_sub_zpow_ne_zero_windowDet (a := (s : ℤ)) (b := N) (by omega)
      rwa [zpow_natCast] at h
    · have h := qParam_zpow_sub_zpow_ne_zero_windowDet (a := N)
        (b := ((s + 1 : ℕ) : ℤ) + (N - r - 1)) (by omega)
      rwa [zpow_add₀ qParam_ne_zero, zpow_natCast] at h
  · have hs' : r ≤ s ∧ s < d := Finset.mem_Ico.mp hs
    refine mul_ne_zero ?_ ?_
    · have h := qParam_zpow_sub_zpow_ne_zero_windowDet (a := N) (b := ((s + 1 : ℕ) : ℤ))
        (by omega)
      rwa [zpow_natCast] at h
    · have h := qParam_zpow_sub_zpow_ne_zero_windowDet (a := (s : ℤ)) (b := N + (N - r - 1))
        (by omega)
      rwa [zpow_add₀ qParam_ne_zero, zpow_natCast] at h

/-- The determinant of the pole basis does not vanish at `x = q^N` for `N > d`. -/
theorem twDet_eval_ne_zero (d : ℕ) {N : ℤ} (hN : (d : ℤ) + 1 ≤ N) :
    (twDet d qParam).eval (qParam ^ N) ≠ 0 := by
  set V : Matrix (Fin (d + 1)) (Fin (d + 1)) (RatFunc ℚ) :=
    Matrix.of fun r k ↦ (qParam ^ (N - (r : ℕ) - 1)) ^ (k : ℕ) with hV
  set M' : Matrix (Fin (d + 1)) (Fin (d + 1)) (RatFunc ℚ) :=
    (evalRingHom (qParam ^ N)).mapMatrix (twMatrix d qParam) with hM'
  have hE : ∀ r i : Fin (d + 1), (V * M') r i =
      (twBasisPoly d qParam i).evalEval (qParam ^ N) (qParam ^ (N - (r : ℕ) - 1)) := by
    intro r i
    rw [evalEval_eq_sum_fin_of_natDegree_lt_windowDet d _ _ _ (lt_of_le_of_lt
      (natDegree_twBasisPoly_le d qParam (by omega)) (by omega)), Matrix.mul_apply]
    rfl
  have htri : (V * M').IsLowerTriangular := by
    intro r i hri
    rw [hE]
    exact twBasisPoly_evalEval_pivot_eq_zero_windowDet d N
      (Fin.lt_def.mp (OrderDual.toDual_lt_toDual.mp hri))
  have hdet : (V * M').det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular _ htri, Finset.prod_ne_zero_iff]
    intro r _
    rw [hE]
    exact twBasisPoly_evalEval_pivot_ne_zero_windowDet d hN (by omega)
  rw [Matrix.det_mul] at hdet
  have hM : (twDet d qParam).eval (qParam ^ N) = M'.det := by
    rw [twDet, ← coe_evalRingHom, RingHom.map_det]
  rw [hM]
  exact right_ne_zero_of_mul hdet

end AJConjecture
