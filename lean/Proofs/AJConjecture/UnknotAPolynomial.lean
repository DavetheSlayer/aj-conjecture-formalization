import Mathlib
import AJConjecture.Unknot
import AJConjecture.ZeroSetDvd

/-!
# The A-polynomial of the unknot

The knot group of the unknot is infinite cyclic, its longitude is trivial, the boundary
eigenvalue set is `{(M, 1) | M ≠ 0}`, and the A-polynomial is `L - 1`.
-/

open Polynomial

namespace AJConjecture

/-- The preferred longitude of the unknot is trivial. -/
private theorem longitude_unknot_eq_one : longitude unknot = 1 :=
  rfl

/-- The diagonal matrix with entries `m`, `m⁻¹` in `SL₂(ℂ)`. -/
private noncomputable def unknotDiagonalMatrix (m : ℂ) (hm : m ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![m, 0; 0, m⁻¹], by simp [Matrix.det_fin_two, hm]⟩

/-- Every point `(m, 1)` with `m ≠ 0` is in the eigenvalue set of the unknot. -/
private theorem mk_one_mem_eigenvalueSet_unknot {m : ℂ} (hm : m ≠ 0) :
    (m, 1) ∈ eigenvalueSet unknot := by
  have hrels : ∀ r ∈ artinRels unknot,
      FreeGroup.lift (fun _ : Fin unknot.strands ↦ unknotDiagonalMatrix m hm) r = 1 := by
    rintro r ⟨k, rfl⟩
    have hword : artinWord unknot.strands unknot.word k = (k, 1) := rfl
    rw [hword, one_mul, inv_one, mul_one, inv_mul_cancel, map_one]
  refine ⟨PresentedGroup.toGroup hrels, ?_⟩
  rw [longitude_unknot_eq_one, map_one, meridian, PresentedGroup.toGroup.of]
  simp [unknotDiagonalMatrix]

/-- Every point of the eigenvalue set of the unknot has second coordinate `1`. -/
private theorem snd_eq_one_of_mem_eigenvalueSet_unknot {p : ℂ × ℂ}
    (hp : p ∈ eigenvalueSet unknot) : p.2 = 1 := by
  obtain ⟨ρ, -, -, -, h⟩ := hp
  rw [longitude_unknot_eq_one, map_one] at h
  simpa using h.symm

/-- On the line `L = 1` the value of `P` is the value of the one-variable polynomial
`P.eval 1`. -/
private theorem evalPoint_mk_one_eq_eval_eval_one (P : ℂ[X][X]) (m : ℂ) :
    evalPoint P (m, 1) = (P.eval 1).eval m := by
  simp [evalPoint]

/-- The value of `L - 1` at a point. -/
private theorem evalPoint_X_sub_C_one (p : ℂ × ℂ) :
    evalPoint (X - C 1 : ℂ[X][X]) p = p.2 - 1 := by
  simp [evalPoint]

/-- The Zariski closure of the eigenvalue set of the unknot is the line `L = 1`. -/
private theorem mem_zariskiClosure_eigenvalueSet_unknot_iff (p : ℂ × ℂ) :
    p ∈ zariskiClosure (eigenvalueSet unknot) ↔ p.2 = 1 := by
  constructor
  · intro hp
    have h := hp (X - C 1) fun s hs ↦ by
      rw [evalPoint_X_sub_C_one, snd_eq_one_of_mem_eigenvalueSet_unknot hs, sub_self]
    rw [evalPoint_X_sub_C_one] at h
    exact sub_eq_zero.1 h
  · obtain ⟨m, l⟩ := p
    rintro rfl P hP
    have hzero : P.eval 1 * X = 0 := Polynomial.funext fun x ↦ by
      rw [eval_mul, eval_X, eval_zero]
      rcases eq_or_ne x 0 with rfl | hx
      · exact mul_zero _
      · rw [← evalPoint_mk_one_eq_eval_eval_one, hP _ (mk_one_mem_eigenvalueSet_unknot hx),
          zero_mul]
    have hQ : P.eval 1 = 0 := (mul_eq_zero.1 hzero).resolve_right X_ne_zero
    rw [evalPoint_mk_one_eq_eval_eval_one, hQ, eval_zero]

/-- `L - 1` is the A-polynomial of the unknot. -/
theorem isAPolynomialOf_unknot : IsAPolynomialOf (eigenvalueSet unknot) (X - 1) := by
  have hmap : (X - 1 : ℤ[X][X]).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) = X - C 1 := by
    simp
  have hirr : Irreducible (X - C 1 : ℂ[X][X]) := irreducible_X_sub_C 1
  refine ⟨?_, fun g hg ↦ ?_⟩
  · rw [hmap]
    exact hirr.squarefree
  · rw [hmap]
    constructor
    · rintro ⟨c, hc⟩ p hp
      rw [mem_zariskiClosure_eigenvalueSet_unknot_iff]
      have h := evalPoint_X_sub_C_one p
      rw [hc, evalPoint, eval₂_mul, ← evalPoint, hp, zero_mul] at h
      exact sub_eq_zero.1 h.symm
    · intro h
      refine dvd_of_forall_evalPoint_eq_zero hg fun p hp ↦ ?_
      rw [evalPoint_X_sub_C_one, (mem_zariskiClosure_eigenvalueSet_unknot_iff p).1 (h p hp),
        sub_self]

end AJConjecture
