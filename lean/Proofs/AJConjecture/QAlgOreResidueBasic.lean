import Mathlib
import AJConjecture.QAlgOreResidue

/-!
# The first residues are the standard basis

For `m < d` the residue `ρ_m` is the basis vector `e_m` (induction: `C_R e_m = e_(m+1)` for
`m + 1 < d`), so the determinant of `ρ_0, …, ρ_(d-1)` is `1`.
-/

open Polynomial

namespace AJConjecture

/-- For `m < d` the residue `ρ_m` is the basis vector `e_m`. -/
theorem oreResidue_of_lt {A : Type*} [CommRing A] (τ : A →+* A) (R : A[X]) {m : ℕ}
    (hm : m < R.natDegree) (k : Fin R.natDegree) :
    oreResidue τ R m k = if (k : ℕ) = m then 1 else 0 := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
    have hm' : m < R.natDegree := by omega
    change (oreCompanion R).mulVec (fun k ↦ τ (oreResidue τ R m k)) k = _
    simp only [Matrix.mulVec, dotProduct, ih hm']
    rw [Finset.sum_eq_single ⟨m, hm'⟩]
    · have hne : m + 1 ≠ R.natDegree := by omega
      simp [oreCompanion, hne]
    · intro j _ hj
      have hjm : (j : ℕ) ≠ m := fun h ↦ hj (Fin.ext h)
      simp [hjm]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- The determinant of the residues `ρ_0, …, ρ_(d-1)` is `1`. -/
theorem oreResidueDet_val {A : Type*} [CommRing A] (τ : A →+* A) (R : A[X]) :
    oreResidueDet τ R (fun i ↦ (i : ℕ)) = 1 := by
  have h : (Matrix.of fun k i : Fin R.natDegree ↦ oreResidue τ R (i : ℕ) k) = 1 := by
    ext k i
    rw [Matrix.of_apply, oreResidue_of_lt τ R i.isLt k, Matrix.one_apply]
    simp only [Fin.ext_iff]
  rw [oreResidueDet, h, Matrix.det_one]

end AJConjecture
