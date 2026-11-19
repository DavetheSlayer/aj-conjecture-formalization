import Mathlib
import AJTwist.Quantum.TwQWindowPoly
import AJConjecture.QAlgMoebiusSubstMul
import AJFamily.Quantum.FamDetAtOne

/-!
# The pole basis and its determinant at `q = 1` for an arbitrary window (Unit Q3)

Source: revision 5, Section 5.1 (`operators.tex`, "Joint regularity of the coefficient solve"):
at `q = 1` the basis `Δ R_i` reduces to `(J - x)^i (1 - x J)^(d-i)`; "its matrix is the `d`-th
symmetric power of an invertible change of basis on linear forms since `x₀² ≠ 1`".

* `moebiusSubst_twBasisPoly_one`: at `q = 1` the stationary substitution `J = (x L + 1)/(L + x)`
  sends the `i`-th basis polynomial to `(-1)^d (x - 1)^d (x² - 1)^d L^(d-i)`;
* `twDet_one_eval_ne_zero`: at `q = 1` the determinant does not vanish at `x₀ ≠ ± 1`.

These are `AJFamily/Quantum/FamBasisAtOne.lean`, `FamDetAtOne.lean` with `2m + 3` replaced by
`d`; the sign `(-1)^d` records the parity of the window.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- At `q = 1` the basis polynomial of the window `d` is a product of two powers. -/
private theorem twBasisPoly_one_eq_pow_windowDetOne (d i : ℕ) :
    twBasisPoly d (1 : ℤ) i =
      (C (1 - X) * (C X - X)) ^ i * (C (X - 1) * (1 - C X * X)) ^ (d - i) := by
  have hc : (Finset.Ico i d).card = d - i := Nat.card_Ico i d
  simp only [twBasisPoly, one_pow, C_1, one_mul, Finset.prod_const, Finset.card_range, hc]

/-- The sign bookkeeping of the product of the two powers. -/
private theorem sign_identity_windowDetOne {A : Type*} [CommRing A] (a L : A) {i j d : ℕ}
    (h : i + j = d) : (-a) ^ i * (-(a * L)) ^ j = (-1) ^ d * (a ^ d * L ^ j) := by
  rw [← h, neg_eq_neg_one_mul a, neg_eq_neg_one_mul (a * L)]
  ring

/-- At `q = 1`, the stationary substitution sends the `i`-th basis polynomial of the window `d`
to `(-1)^d (x - 1)^d (x² - 1)^d L^(d-i)`. -/
theorem moebiusSubst_twBasisPoly_one (d : ℕ) {i : ℕ} (hi : i ≤ d) :
    moebiusSubst d (twBasisPoly d (1 : ℤ) i) =
      C ((-1) ^ d * ((X - 1) ^ d * (X ^ 2 - 1) ^ d)) * X ^ (d - i) := by
  have hl : (C (1 - X) * (C X - X) : ℤ[X][X]).natDegree ≤ 1 := by compute_degree
  have hr : (C (X - 1) * (1 - C X * X) : ℤ[X][X]).natDegree ≤ 1 := by compute_degree
  have h := moebiusSubst_mul (natDegree_pow_le_of_le i hl)
    (natDegree_pow_le_of_le (d - i) hr)
  have hij : i + (d - i) = d := by omega
  rw [show i * 1 + (d - i) * 1 = d by omega,
    famMoebiusSubst_pow_of_natDegree_le hl, famMoebiusSubst_pow_of_natDegree_le hr,
    famMoebiusSubst_one_basisFactor_left, famMoebiusSubst_one_basisFactor_right] at h
  rw [twBasisPoly_one_eq_pow_windowDetOne d i, h, sign_identity_windowDetOne _ _ hij]
  simp only [C_mul, C_pow, C_neg, C_1, mul_pow, mul_assoc]

/-- The determinant at `q = 1` divides `((-1)^d (x - 1)^d (x² - 1)^d)^(d+1)`. -/
private theorem exists_mul_twDet_one_eq_windowDetOne (d : ℕ) :
    ∃ D : ℤ[X], D * twDet d (1 : ℤ) =
      ((-1) ^ d * ((X - 1) ^ d * (X ^ 2 - 1) ^ d)) ^ (d + 1) := by
  refine ⟨(Matrix.of fun l k : Fin (d + 1) ↦
    ((C X * X + 1 : ℤ[X][X]) ^ (k : ℕ) * (C X + X) ^ (d - (k : ℕ))).coeff
      (d - (l : ℕ))).det, ?_⟩
  have hmul : (Matrix.of fun l k : Fin (d + 1) ↦
      ((C X * X + 1 : ℤ[X][X]) ^ (k : ℕ) * (C X + X) ^ (d - (k : ℕ))).coeff
        (d - (l : ℕ))) * twMatrix d (1 : ℤ) =
      Matrix.diagonal fun _ ↦ (-1) ^ d * ((X - 1) ^ d * (X ^ 2 - 1) ^ d) := by
    refine Matrix.ext fun l i ↦ ?_
    have hi : (i : ℕ) ≤ d := by omega
    have h := congrArg (fun p : ℤ[X][X] ↦ p.coeff (d - (l : ℕ)))
      (moebiusSubst_twBasisPoly_one d hi)
    simp only [moebiusSubst, finsetSum_coeff, mul_assoc, coeff_C_mul, coeff_X_pow] at h
    rw [Matrix.mul_apply, Matrix.diagonal_apply]
    simp only [Matrix.of_apply, twMatrix]
    rw [Finset.sum_range] at h
    refine (Finset.sum_congr rfl fun k _ ↦ mul_comm _ _).trans (h.trans ?_)
    have hiff : (d - (l : ℕ) = d - (i : ℕ)) ↔ l = i := by
      rw [Fin.ext_iff]
      omega
    simp only [hiff]
    split_ifs <;> simp
  rw [twDet, ← Matrix.det_mul, hmul, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- At `q = 1` the determinant of the pole basis does not vanish away from `x = ± 1`. -/
theorem twDet_one_eval_ne_zero (d : ℕ) {x₀ : ℂ} (h1 : x₀ ≠ 1) (h2 : x₀ ≠ -1) :
    ((twDet d (1 : ℤ)).map (Int.castRingHom ℂ)).eval x₀ ≠ 0 := by
  obtain ⟨D, hD⟩ := exists_mul_twDet_one_eq_windowDetOne d
  intro h0
  have h := congrArg (fun p : ℤ[X] ↦ (p.map (Int.castRingHom ℂ)).eval x₀) hD
  simp only [Polynomial.map_mul, eval_mul, h0, mul_zero, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_neg, Polynomial.map_one, map_X, eval_pow, eval_sub, eval_neg, eval_X,
    eval_one] at h
  have ha : x₀ - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hb : x₀ ^ 2 - 1 ≠ 0 := by
    rw [show x₀ ^ 2 - 1 = (x₀ - 1) * (x₀ + 1) by ring]
    exact mul_ne_zero ha fun h6 ↦ h2 (eq_neg_of_add_eq_zero_left h6)
  exact pow_ne_zero (d + 1) (mul_ne_zero (pow_ne_zero d (neg_ne_zero.mpr one_ne_zero))
    (mul_ne_zero (pow_ne_zero d ha) (pow_ne_zero d hb))) h.symm

end AJConjecture
