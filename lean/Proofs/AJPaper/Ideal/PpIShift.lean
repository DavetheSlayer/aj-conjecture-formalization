import Mathlib
import AJPaper.Ideal.PpIMapOp

/-!
# Left multiplication by a monomial in the quantum torus (Unit PpI, node `PpI_Shift`)

Source: Section 1.1 of the paper: the primitive minimum is determined "up to the coefficient
units `± t^i M^j`" after shifting the lowest `L`-exponent to zero; Section 8.5 compares raw
Laurent-polynomial annihilators with the polynomial rows.

`ppiShift a b c P` is the left multiple `t^c M^a L^b · P` in the quantum torus:
`t^c M^a L^b · c_{k,l} M^k L^l = t^{c + 2kb} c_{k,l} M^{k+a} L^{l+b}` (`L^b M^k = t^{2kb} M^k L^b`).

* `ppiApply_ppiShift`: `((t^c M^a L^b P) f)(n) = t^{c + 2an} (P f)(n + b)`; in particular the
  shift of an annihilator is an annihilator.
* `ppiMapOp_ppiShift`: the shift commutes with a change of coefficients.
* `ppiEval_ppiEps_ppiShift`: at `t = -1` and a point with `M, L ≠ 0` the shift multiplies the
  value by `(-1)^c M^a L^b`.

The first and the third identity were checked on random data (`SCR/S/py/s03_torus.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The left multiple `t^c M^a L^b · P` in the quantum torus. -/
def ppiShift {A : Type} [CommRing A] (a b c : ℕ) (P : PpiOp A) : PpiOp A :=
  P.sum fun kl coef ↦ Finsupp.single (kl.1 + a, kl.2 + b)
    (LaurentPolynomial.T ((c : ℤ) + 2 * kl.1 * b) * coef)

/-- A sum over the coefficients of a shift is the sum of the shifted terms. -/
private theorem ppiShift_sum_Shift {A N : Type} [CommRing A] [AddCommMonoid N] (a b c : ℕ)
    (P : PpiOp A) (h : ℤ × ℤ → LaurentPolynomial A → N) (h0 : ∀ kl, h kl 0 = 0)
    (hadd : ∀ kl x y, h kl (x + y) = h kl x + h kl y) :
    (ppiShift a b c P).sum h = P.sum fun kl coef ↦
      h (kl.1 + a, kl.2 + b) (LaurentPolynomial.T ((c : ℤ) + 2 * kl.1 * b) * coef) := by
  unfold ppiShift
  rw [Finsupp.sum_sum_index h0 hadd]
  refine Finsupp.sum_congr fun kl _ ↦ ?_
  rw [Finsupp.sum_single_index (h0 _)]

/-- The value at a point of the specialization `t = -1`, as a sum over the coefficients. -/
private theorem ppiEval_ppiEps_eq_sum_Shift (P : PpiOp ℂ) (p : ℂ × ℂ) :
    ppiEval p (ppiEps P) = P.sum fun kl c ↦
      LaurentPolynomial.eval₂ (RingHom.id ℂ) (-1 : ℂˣ) c * p.1 ^ kl.1 * p.2 ^ kl.2 := by
  unfold ppiEval ppiEps
  rw [AddMonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapRange_index (fun kl ↦ by simp)]

/-- The action of a shift: `((t^c M^a L^b P) f)(n) = t^{c + 2an} (P f)(n + b)`. -/
theorem ppiApply_ppiShift {A : Type} [CommRing A] (a b c : ℕ) (P : PpiOp A)
    (f : ℤ → LaurentPolynomial A) (n : ℤ) :
    ppiApply (ppiShift a b c P) f n =
      LaurentPolynomial.T ((c : ℤ) + 2 * a * n) * ppiApply P f (n + b) := by
  unfold ppiApply
  rw [ppiShift_sum_Shift a b c P _ (fun kl ↦ by simp) (fun kl x y ↦ by ring), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun kl _ ↦ ?_
  have hT : (LaurentPolynomial.T ((c : ℤ) + 2 * kl.1 * b) : LaurentPolynomial A) *
      LaurentPolynomial.T (2 * (kl.1 + a) * n) =
      LaurentPolynomial.T ((c : ℤ) + 2 * a * n) * LaurentPolynomial.T (2 * kl.1 * (n + b)) := by
    rw [← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
    congr 1
    ring
  have hf : n + (kl.2 + b) = n + b + kl.2 := by ring
  rw [hf]
  linear_combination (P kl * f (n + b + kl.2)) * hT

/-- The shift commutes with a change of the coefficient ring. -/
theorem ppiMapOp_ppiShift {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (a b c : ℕ)
    (P : PpiOp A) : ppiMapOp φ (ppiShift a b c P) = ppiShift a b c (ppiMapOp φ P) := by
  have hT (m : ℤ) : AddMonoidAlgebra.mapRingHom ℤ φ (LaurentPolynomial.T m) =
      LaurentPolynomial.T m := by
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]
  have hmap (X : PpiOp A) : ppiMapOp φ X = Finsupp.mapRange.addMonoidHom
      (AddMonoidAlgebra.mapRingHom ℤ φ).toAddMonoidHom X := rfl
  unfold ppiShift
  rw [hmap, map_finsuppSum]
  unfold ppiMapOp
  rw [Finsupp.sum_mapRange_index (fun kl ↦ by simp)]
  refine Finsupp.sum_congr fun kl _ ↦ ?_
  simp only [Finsupp.mapRange.addMonoidHom_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass, Finsupp.mapRange_single, map_mul, hT]

/-- The specialization of a shift at a point with nonzero coordinates. -/
theorem ppiEval_ppiEps_ppiShift (a b c : ℕ) (P : PpiOp ℂ) {p : ℂ × ℂ} (h1 : p.1 ≠ 0)
    (h2 : p.2 ≠ 0) :
    ppiEval p (ppiEps (ppiShift a b c P)) =
      (-1) ^ c * p.1 ^ a * p.2 ^ b * ppiEval p (ppiEps P) := by
  rw [ppiEval_ppiEps_eq_sum_Shift, ppiEval_ppiEps_eq_sum_Shift,
    ppiShift_sum_Shift a b c P _ (fun kl ↦ by simp) (fun kl x y ↦ by rw [map_add]; ring),
    Finsupp.mul_sum]
  refine Finsupp.sum_congr fun kl _ ↦ ?_
  have hT : LaurentPolynomial.eval₂ (RingHom.id ℂ) (-1 : ℂˣ)
      (LaurentPolynomial.T ((c : ℤ) + 2 * kl.1 * b)) = (-1) ^ c := by
    have he : Even (2 * kl.1 * (b : ℤ)) := ⟨kl.1 * b, by ring⟩
    rw [LaurentPolynomial.eval₂_T, zpow_add, he.neg_one_zpow, mul_one, zpow_natCast]
    simp
  rw [map_mul, hT, zpow_add₀ h1, zpow_add₀ h2, zpow_natCast, zpow_natCast]
  ring

end AJConjecture
