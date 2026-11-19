import Mathlib
import AJConjecture.QAlgOreResidue

/-!
# Shifting the indices of a determinant of residues

The matrix with columns `ρ_(t i + 1) = C_R τ(ρ_(t i))` is `C_R` times the image under `τ` of the
matrix with columns `ρ_(t i)`; determinants are multiplicative and commute with ring
homomorphisms (`Matrix.det_mul`, `RingHom.map_det`).
-/

open Polynomial

namespace AJConjecture

/-- `det(ρ_(t i + 1)) = det(C_R) τ(det(ρ_(t i)))`. -/
theorem oreResidueDet_succ {A : Type*} [CommRing A] (τ : A →+* A) (R : A[X])
    (t : Fin R.natDegree → ℕ) :
    oreResidueDet τ R (fun i ↦ t i + 1) = (oreCompanion R).det * τ (oreResidueDet τ R t) := by
  have h : (Matrix.of fun k i ↦ oreResidue τ R (t i + 1) k) =
      oreCompanion R * τ.mapMatrix (Matrix.of fun k i ↦ oreResidue τ R (t i) k) := by
    ext k i
    rfl
  rw [oreResidueDet, h, Matrix.det_mul, ← RingHom.map_det]
  rfl

end AJConjecture
