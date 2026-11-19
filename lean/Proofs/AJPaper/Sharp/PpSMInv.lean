import Mathlib
import AJTwist.Main.TwMReflectComparison

/-!
# The meridian inversion of the comparison ring (Unit PpS, node `PpS_MInv`)

Source: Section 8.2 of the paper (`conclusion.tex`, "Transport under the satellite mirror"):
`f_{S^*}(M, L) ≐ f_S(M⁻¹, L)`; Section 9 calls this involution of `R = ℚ(M)[L, L⁻¹]`
`ρ g = g(M⁻¹, L)`.

* `ppsMInv`: the ring endomorphism `g(M, L) ↦ g(M⁻¹, L)` of `R`: the field automorphism
  `twQBar` (`X ↦ X⁻¹` of `ℚ(X)`) applied to the coefficients of a Laurent polynomial in `L`.
* `ppsMInv_C_mul_T`, `ppsMInv_C`, `ppsMInv_T`: its values on monomials.
* `ppsMInv_ppsMInv`: it is an involution.
* `ppsMInv_toLaurent`: on polynomials it is `Polynomial.map twQBar`.
* `toComparison_twmMReflect`: the image in `R` of `M^B F(M⁻¹, L)` (`twmMReflect B F`) is `M^B`
  times the meridian inversion of the image of `F`.

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The meridian inversion `g(M, L) ↦ g(M⁻¹, L)` of the comparison ring `ℚ(M)[L, L⁻¹]`. -/
def ppsMInv : ComparisonRing →+* ComparisonRing :=
  AddMonoidAlgebra.mapRingHom ℤ twQBar

theorem ppsMInv_C_mul_T (c : RatFunc ℚ) (n : ℤ) :
    ppsMInv (LaurentPolynomial.C c * LaurentPolynomial.T n) =
      LaurentPolynomial.C (twQBar c) * LaurentPolynomial.T n := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T, ppsMInv,
    AddMonoidAlgebra.mapRingHom_single]

theorem ppsMInv_C (c : RatFunc ℚ) :
    ppsMInv (LaurentPolynomial.C c) = LaurentPolynomial.C (twQBar c) := by
  have h := ppsMInv_C_mul_T c 0
  rwa [LaurentPolynomial.T_zero, mul_one, mul_one] at h

theorem ppsMInv_T (n : ℤ) : ppsMInv (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  have h := ppsMInv_C_mul_T 1 n
  rwa [map_one, map_one, map_one, one_mul] at h

/-- The meridian inversion is an involution. -/
theorem ppsMInv_ppsMInv (F : ComparisonRing) : ppsMInv (ppsMInv F) = F := by
  induction F using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | C_mul_T n a => rw [ppsMInv_C_mul_T, ppsMInv_C_mul_T, twQBar_twQBar]

/-- On polynomials in `L` the meridian inversion is the coefficient map `twQBar`. -/
theorem ppsMInv_toLaurent (p : (RatFunc ℚ)[X]) :
    ppsMInv (toLaurent p) = toLaurent (p.map twQBar) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.map_add, map_add]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.toLaurent_C_mul_T, Polynomial.toLaurent_C_mul_T,
      ppsMInv_C_mul_T]

/-- The image in `ℚ(M)[L, L⁻¹]` of `M^B F(M⁻¹, L)` is `M^B` times the meridian inversion of the
image of `F`, for a bound `B` of the degrees in `M` of the coefficients of `F`. -/
theorem toComparison_twmMReflect (B : ℕ) (F : ℤ[X][X])
    (hB : ∀ i : ℕ, (F.coeff i).natDegree ≤ B) :
    toComparison (twmMReflect B F) =
      LaurentPolynomial.C ((RatFunc.X : RatFunc ℚ) ^ B) * ppsMInv (toComparison F) := by
  rw [toComparison_eq_toLaurent_map, toComparison_eq_toLaurent_map, map_twmMReflect B F hB,
    ppsMInv_toLaurent, map_mul, Polynomial.toLaurent_C]

end AJConjecture
