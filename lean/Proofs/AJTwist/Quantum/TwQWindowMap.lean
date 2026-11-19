import Mathlib
import AJTwist.Quantum.TwQWindowPoly

/-!
# Naturality of the transfer data for an arbitrary pole window (Unit Q3)

The basis polynomials, the cleared adjoint, the adjoint trace polynomials, the determinant and
the Cramer numerators commute with ring homomorphisms, as in
`AJFamily/Quantum/FamTransferMap.lean`. This is how the operator over `ℤ[t]` is evaluated at
`q = t⁴ ∈ ℚ(t)` (the transfer), at `q = 1` (the symbol) and at `q = 1 - 4ε` (the first jets).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `divX` commutes with ring homomorphisms. -/
private theorem map_divX_of_ringHom_windowMap {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) (p : A[X]) : (divX p).map f = divX (p.map f) := by
  ext n
  simp only [coeff_map, coeff_divX]

/-- The basis polynomials commute with ring homomorphisms. -/
theorem map_twBasisPoly {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ) (q : R)
    (i : ℕ) :
    (twBasisPoly d q i).map (Polynomial.mapRingHom φ) = twBasisPoly d (φ q) i := by
  simp only [twBasisPoly, Polynomial.map_prod, Polynomial.map_mul, Polynomial.map_sub,
    map_C, map_X, coe_mapRingHom, Polynomial.map_pow, map_pow]

/-- The cleared adjoint commutes with ring homomorphisms. -/
theorem map_twAdjoint {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ) (q : R)
    (n : R[X][X]) :
    (twAdjoint d q n).map (Polynomial.mapRingHom φ) =
      twAdjoint d (φ q) (n.map (Polynomial.mapRingHom φ)) := by
  simp only [twAdjoint, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
    map_divX_of_ringHom_windowMap, Polynomial.map_comp, map_C, map_X, Polynomial.map_one,
    coe_mapRingHom, Polynomial.map_pow, map_pow]

/-- The adjoint trace polynomials commute with ring homomorphisms. -/
theorem map_twCheb {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ) (q : R)
    (k : ℕ) (n : R[X][X]) :
    (twCheb d q k n).map (Polynomial.mapRingHom φ) =
      twCheb d (φ q) k (n.map (Polynomial.mapRingHom φ)) := by
  induction k using Nat.twoStepInduction generalizing n with
  | zero => rw [twCheb, twCheb, Polynomial.map_mul, Polynomial.map_ofNat]
  | one => rw [twCheb, twCheb, map_twAdjoint]
  | more k ih0 ih1 =>
    rw [twCheb, twCheb, Polynomial.map_sub, Polynomial.map_mul, ih1, map_twAdjoint, ih0]
    simp only [map_C, map_X, coe_mapRingHom, Polynomial.map_mul, Polynomial.map_pow, map_pow]

/-- The coefficient matrix commutes with ring homomorphisms. -/
private theorem mapMatrix_twMatrix_windowMap {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d : ℕ) (q : R) :
    (Polynomial.mapRingHom φ).mapMatrix (twMatrix d q) = twMatrix d (φ q) := by
  ext k i : 1
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, twMatrix, twMatrix, Matrix.of_apply,
    Matrix.of_apply, ← map_twBasisPoly, coeff_map]

/-- The determinant commutes with ring homomorphisms. -/
theorem map_twDet {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ) (q : R) :
    (twDet d q).map φ = twDet d (φ q) := by
  rw [twDet, twDet, ← coe_mapRingHom, RingHom.map_det, mapMatrix_twMatrix_windowMap]

/-- The Cramer numerators commute with ring homomorphisms. -/
theorem map_twCoeff {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ) (q : R)
    (T : R[X][X]) (i : Fin (d + 1)) :
    (twCoeff d q T i).map φ = twCoeff d (φ q) (T.map (Polynomial.mapRingHom φ)) i := by
  rw [twCoeff, twCoeff, Matrix.cramer_apply, Matrix.cramer_apply, ← coe_mapRingHom,
    RingHom.map_det, ← mapMatrix_twMatrix_windowMap φ d q, RingHom.mapMatrix_apply,
    RingHom.mapMatrix_apply, Matrix.map_updateCol]
  congr 2
  ext k : 1
  rw [Function.comp_apply, coeff_map]

end AJConjecture
