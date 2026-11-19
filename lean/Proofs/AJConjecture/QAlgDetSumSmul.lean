import Mathlib

/-!
# The determinant of columns that are linear combinations

If the `i`-th column of a square matrix is `∑_j a i j • w j`, the determinant is
`∑_s (∏_i a i (s i)) • det(w (s i))`, the sum over all maps `s` from the columns to the index
set of the family `w`: the determinant is multilinear in the columns
(`Matrix.detRowAlternating` on the transpose, `MultilinearMap.map_sum`,
`MultilinearMap.map_smul_univ`). This replaces the Cauchy–Binet formula.
-/

namespace AJConjecture

/-- The determinant of a matrix whose columns are combinations `∑_j a i j • w j` of a finite
family `w` of vectors. -/
theorem det_sum_smul_eq_sum {O F : Type*} [CommRing O] [CommRing F] [Algebra O F] {n ι : Type*}
    [Fintype n] [DecidableEq n] [Fintype ι] (a : n → ι → O) (w : ι → n → F) :
    (Matrix.of fun k i ↦ ∑ j, a i j • w j k).det =
      ∑ s : n → ι, (∏ i, a i (s i)) • (Matrix.of fun k i ↦ w (s i) k).det := by
  classical
  have hdet : ∀ v : n → n → F, (Matrix.of fun k i ↦ v i k).det =
      (Matrix.detRowAlternating : (n → F) [⋀^n]→ₗ[F] F) v := fun v ↦ by
    rw [← Matrix.det_transpose]
    rfl
  have hv : (fun (i : n) (k : n) ↦ ∑ j, a i j • w j k) =
      fun i ↦ ∑ j, algebraMap O F (a i j) • w j := by
    funext i k
    simp only [Finset.sum_apply, Pi.smul_apply, algebraMap_smul]
  rw [hdet fun i k ↦ ∑ j, a i j • w j k, hv]
  erw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  erw [MultilinearMap.map_smul_univ]
  simp only [RingHom.id_apply]
  rw [hdet fun i ↦ w (s i), ← map_prod, algebraMap_smul]
  rfl

end AJConjecture
