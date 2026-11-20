import Mathlib
import AJPaper.Ideal.PpIMapOp

/-!
# Rational coordinates of a complex annihilator (Unit PpI, node `PpI_Coord`)

Source: Section 8.5 of the paper (`conclusion.tex`): "a raw Laurent-polynomial annihilator with
complex coefficients is a finite complex linear combination of rational Laurent-polynomial
annihilators. To see this, choose a basis over `ℚ` for the span of its finitely many scalar
coefficients after substitution. The sequence is `ℚ(t)`-valued, so linear independence over
`ℚ(t)` makes each rational row annihilate the signed sequence."

* `ppiCoord φ P`: a `ℚ`-linear functional `φ : ℂ → ℚ` (a coordinate of a `ℚ`-basis) applied to
  every scalar coefficient of `P`.
* `ppiAnnihilates_ppiCoord`: if `P` annihilates the coloured Jones function, so does
  `ppiCoord φ P`. Route: `φ` applied coefficient-wise is additive on `ℂ[t^{±1}]` and satisfies
  `φ_*(c · t^m · \bar{j}) = φ_*(c) · t^m · \bar{j}` for `j ∈ ℤ[t^{±1}]` (a coefficient of the
  product is an integer combination of the scalar coefficients of `c`, and `φ` is `ℚ`-linear);
  apply `φ_*` to `(P J_K)(n) = 0`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A `ℚ`-linear functional applied to all scalar coefficients of an element of the quantum
torus over `ℂ[t, t⁻¹]`. -/
def ppiCoord (φ : ℂ →ₗ[ℚ] ℚ) (P : PpiOp ℂ) : PpiOp ℚ :=
  P.mapRange (fun c ↦ AddMonoidAlgebra.ofCoeff (c.coeff.mapRange φ (map_zero φ)))
    (by ext; simp)

/-- The coefficient-wise application of a `ℚ`-linear functional to a Laurent polynomial, as
an additive map. -/
private def laurentCoordHom_Coord (φ : ℂ →ₗ[ℚ] ℚ) :
    LaurentPolynomial ℂ →+ LaurentPolynomial ℚ where
  toFun c := AddMonoidAlgebra.ofCoeff (c.coeff.mapRange φ (map_zero φ))
  map_zero' := by ext; simp
  map_add' x y := by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.mapRange_add (map_add φ),
      AddMonoidAlgebra.ofCoeff_add]

/-- The coefficient-wise functional on a monomial. -/
private theorem laurentCoordHom_single_Coord (φ : ℂ →ₗ[ℚ] ℚ) (m : ℤ) (r : ℂ) :
    laurentCoordHom_Coord φ (AddMonoidAlgebra.single m r) = AddMonoidAlgebra.single m (φ r) := by
  change AddMonoidAlgebra.ofCoeff (Finsupp.mapRange φ (map_zero φ) (Finsupp.single m r)) = _
  rw [Finsupp.mapRange_single]
  rfl

/-- The coefficient-wise functional commutes with multiplication by a Laurent polynomial with
integer coefficients. -/
private theorem laurentCoordHom_mul_map_Coord (φ : ℂ →ₗ[ℚ] ℚ) (c : LaurentPolynomial ℂ)
    (z : LaurentPolynomial ℤ) :
    laurentCoordHom_Coord φ (c * AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom ℂ) z) =
      laurentCoordHom_Coord φ c * AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom ℚ) z := by
  induction z using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, mul_add, mul_add, map_add, hp, hq]
  | C_mul_T n a =>
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.mapRingHom_single,
      AddMonoidAlgebra.mapRingHom_single]
    induction c using LaurentPolynomial.induction_on' with
    | add p q hp hq => rw [add_mul, map_add, map_add, add_mul, hp, hq]
    | C_mul_T m r =>
      rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.single_mul_single,
        laurentCoordHom_single_Coord, laurentCoordHom_single_Coord,
        AddMonoidAlgebra.single_mul_single]
      congr 1
      have h : r * (Int.castRingHom ℂ) a = a • r := by
        rw [zsmul_eq_mul, eq_intCast, mul_comm]
      rw [h, map_zsmul, zsmul_eq_mul, eq_intCast, mul_comm]

/-- The coordinates of an annihilator are annihilators. -/
theorem ppiAnnihilates_ppiCoord (φ : ℂ →ₗ[ℚ] ℚ) {P : PpiOp ℂ} {K : BraidKnot}
    (hP : PpiAnnihilates P K) : PpiAnnihilates (ppiCoord φ P) K := by
  intro n
  have h := congrArg (laurentCoordHom_Coord φ) (hP n)
  rw [map_zero] at h
  rw [← h]
  unfold ppiApply ppiCoord
  rw [Finsupp.sum_mapRange_index (fun kl ↦ by simp), map_finsuppSum]
  refine Finsupp.sum_congr fun kl _ ↦ ?_
  have hT (A : Type) [CommRing A] (m : ℤ) : (LaurentPolynomial.T m : LaurentPolynomial A) =
      AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom A) (LaurentPolynomial.T m) := by
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]
  have hJ (A : Type) [CommRing A] (x : LaurentPolynomial A) (m : ℤ) :
      x * LaurentPolynomial.T m * ppiJones A K (n + kl.2) =
        x * AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom A)
          (LaurentPolynomial.T m * coloredJones K (n + kl.2)) := by
    rw [map_mul, ← hT, mul_assoc]
    rfl
  rw [hJ, hJ, laurentCoordHom_mul_map_Coord]
  rfl

end AJConjecture
