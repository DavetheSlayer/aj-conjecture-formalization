import Mathlib
import AJConjecture.QAlgOreResidue

/-!
# The determinant of the companion matrix

`det C_R = (-1)^d R(0)` for monic `R` of degree `d`: expand along the first row, whose only
nonzero entry is `-R.coeff 0` in the last column; the complementary minor is the identity
matrix. (For `d = 0` both sides are `1`.)
-/

open Polynomial

namespace AJConjecture

/-- The determinant of a matrix of companion shape, of any size `d` and with last column `-c`:
it is `(-1)^d c 0` for `d > 0`. -/
private theorem det_companionShape_eq {A : Type*} [CommRing A] (d : ℕ) (c : ℕ → A) :
    (Matrix.of fun k j : Fin d ↦
      if (j : ℕ) + 1 = d then -c k else if (k : ℕ) = j + 1 then 1 else 0).det =
      if d = 0 then 1 else (-1) ^ d * c 0 := by
  cases d with
  | zero => simp
  | succ n =>
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last n)]
    · have hsub : (Matrix.of fun k j : Fin (n + 1) ↦
          if (j : ℕ) + 1 = n + 1 then -c k else if (k : ℕ) = j + 1 then 1 else 0).submatrix
          Fin.succ (Fin.last n).succAbove = 1 := by
        ext k j
        have hj : (j : ℕ) ≠ n := by omega
        simp [Matrix.one_apply, Fin.ext_iff, hj]
      rw [hsub, Matrix.det_one]
      simp [pow_succ]
    · intro j _ hj
      have hj' : (j : ℕ) ≠ n := fun h ↦ hj (Fin.ext h)
      simp [hj']
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- The determinant of the companion matrix of a monic polynomial of degree `d` is
`(-1)^d` times its constant coefficient. -/
theorem det_oreCompanion {A : Type*} [CommRing A] {R : A[X]} (hR : R.Monic) :
    (oreCompanion R).det = (-1) ^ R.natDegree * R.coeff 0 := by
  have h := det_companionShape_eq R.natDegree R.coeff
  rw [oreCompanion, h]
  split_ifs with h0
  · have h1 : R = 1 := hR.natDegree_eq_zero.mp h0
    rw [h0, h1]
    simp
  · rfl

end AJConjecture
