import Mathlib
import AJFamily.Quantum.FamBasisAtOne
import AJConjecture.QAlgMoebiusSubstMul
import AJFamily.Quantum.FamTransferCoeff

/-!
# The family determinant at `q = 1`

`famDet_one_eval_ne_zero`: `famDet m 1` does not vanish at `x₀ ≠ ±1`, since it divides a power of
`(x - 1)(x² - 1)`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The sign bookkeeping of the product of the two powers, for an odd total exponent. -/
private theorem famBasisAtOne_sign_identity_det {A : Type*} [CommRing A] (a L : A) {i j d : ℕ}
    (hd : Odd d) (h : i + j = d) : (-a) ^ i * (-(a * L)) ^ j = -(a ^ d * L ^ j) := by
  have h1 : ∀ c : A, c ^ d = -1 → (c * a) ^ i * (c * (a * L)) ^ j = -(a ^ d * L ^ j) := by
    intro c hc
    rw [← h] at hc ⊢
    linear_combination (a ^ (i + j) * L ^ j) * hc
  have h2 := h1 (-1) hd.neg_one_pow
  simpa only [neg_one_mul] using h2

/-- The family determinant at `q = 1` divides `((x - 1)^d (x² - 1)^d)^(d+1)`, `d = 2m + 3`. -/
private theorem exists_mul_famDet_one_eq (m : ℕ) :
    ∃ D : ℤ[X], D * famDet m (1 : ℤ) =
      ((X - 1) ^ (2 * m + 3) * (X ^ 2 - 1) ^ (2 * m + 3)) ^ (2 * m + 4) := by
  refine ⟨(Matrix.of fun l k : Fin (2 * m + 4) ↦
    ((C X * X + 1 : ℤ[X][X]) ^ (k : ℕ) * (C X + X) ^ (2 * m + 3 - (k : ℕ))).coeff
      (2 * m + 3 - (l : ℕ))).det, ?_⟩
  have hmul : (Matrix.of fun l k : Fin (2 * m + 4) ↦
      ((C X * X + 1 : ℤ[X][X]) ^ (k : ℕ) * (C X + X) ^ (2 * m + 3 - (k : ℕ))).coeff
        (2 * m + 3 - (l : ℕ))) * famMatrix m (1 : ℤ) =
      Matrix.diagonal fun _ ↦ -((X - 1) ^ (2 * m + 3) * (X ^ 2 - 1) ^ (2 * m + 3)) := by
    refine Matrix.ext fun l i ↦ ?_
    have hi : (i : ℕ) ≤ 2 * m + 3 := by omega
    have h := congrArg (fun p : ℤ[X][X] ↦ p.coeff (2 * m + 3 - (l : ℕ)))
      (moebiusSubst_famBasisPoly_one m hi)
    simp only [moebiusSubst, finsetSum_coeff, mul_assoc, coeff_C_mul, coeff_neg,
      coeff_X_pow] at h
    rw [Matrix.mul_apply, Matrix.diagonal_apply]
    simp only [Matrix.of_apply, famMatrix]
    rw [Finset.sum_range] at h
    refine (Finset.sum_congr rfl fun k _ ↦ mul_comm _ _).trans (h.trans ?_)
    have hiff : (2 * m + 3 - (l : ℕ) = 2 * m + 3 - (i : ℕ)) ↔ l = i := by
      rw [Fin.ext_iff]
      omega
    simp only [hiff]
    split_ifs <;> simp
  rw [famDet, ← Matrix.det_mul, hmul, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Even.neg_pow ⟨m + 2, by ring⟩]

/-- The family determinant at `q = 1` does not vanish away from `x = ±1`. -/
theorem famDet_one_eval_ne_zero (m : ℕ) {x₀ : ℂ} (h1 : x₀ ≠ 1) (h2 : x₀ ≠ -1) :
    ((famDet m (1 : ℤ)).map (Int.castRingHom ℂ)).eval x₀ ≠ 0 := by
  obtain ⟨D, hD⟩ := exists_mul_famDet_one_eq m
  intro h0
  have h := congrArg (fun p : ℤ[X] ↦ (p.map (Int.castRingHom ℂ)).eval x₀) hD
  simp only [Polynomial.map_mul, eval_mul, h0, mul_zero, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_one, map_X, eval_pow, eval_sub, eval_X, eval_one] at h
  have h3 : (x₀ - 1) ^ (2 * m + 3) * (x₀ ^ 2 - 1) ^ (2 * m + 3) = 0 :=
    pow_eq_zero_iff (by omega) |>.mp h.symm
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact h1 (sub_eq_zero.mp (pow_eq_zero_iff (by omega) |>.mp h4))
  · have h5 : (x₀ - 1) * (x₀ + 1) = 0 := by
      rw [← pow_eq_zero_iff (by omega) |>.mp h4]
      ring
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact h1 (sub_eq_zero.mp h6)
    · exact h2 (eq_neg_of_add_eq_zero_left h6)

end AJConjecture
