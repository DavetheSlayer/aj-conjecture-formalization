import Mathlib
import AJFamily.Quantum.FamTransferCoeff

/-!
# Naturality of the family transfer data

The target polynomial, the determinant and the Cramer coefficients commute with ring
homomorphisms.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `divX` commutes with ring homomorphisms. -/
private theorem map_divX_of_ringHom_fam {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B)
    (p : A[X]) : (divX p).map f = divX (p.map f) := by
  ext n
  simp only [coeff_map, coeff_divX]

/-- The family basis polynomials commute with ring homomorphisms. -/
private theorem map_famBasisPoly {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ)
    (q : R) (i : ℕ) :
    (famBasisPoly m q i).map (Polynomial.mapRingHom φ) = famBasisPoly m (φ q) i := by
  simp only [famBasisPoly, Polynomial.map_prod, Polynomial.map_mul, Polynomial.map_sub,
    map_C, map_X, coe_mapRingHom, Polynomial.map_pow, map_pow]

/-- The family adjoint operator commutes with ring homomorphisms. -/
private theorem map_famAdjoint {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ)
    (q : R) (n : R[X][X]) :
    (famAdjoint m q n).map (Polynomial.mapRingHom φ) =
      famAdjoint m (φ q) (n.map (Polynomial.mapRingHom φ)) := by
  simp only [famAdjoint, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
    map_divX_of_ringHom_fam, Polynomial.map_comp, map_C, map_X, Polynomial.map_one,
    coe_mapRingHom, Polynomial.map_pow, map_pow]

/-- The family adjoint Chebyshev operators commute with ring homomorphisms. -/
private theorem map_famCheb {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ)
    (q : R) : ∀ (d : ℕ) (n : R[X][X]), (famCheb m q d n).map (Polynomial.mapRingHom φ) =
      famCheb m (φ q) d (n.map (Polynomial.mapRingHom φ))
  | 0, n => by
    rw [famCheb, famCheb, Polynomial.map_mul, Polynomial.map_ofNat]
  | 1, n => by
    rw [famCheb, famCheb, map_famAdjoint]
  | d + 2, n => by
    rw [famCheb, famCheb, Polynomial.map_sub, Polynomial.map_mul,
      map_famCheb φ m q (d + 1), map_famAdjoint, map_famCheb φ m q d]
    simp only [map_C, map_X, coe_mapRingHom, Polynomial.map_mul, Polynomial.map_pow, map_pow]

/-- The family target polynomial commutes with ring homomorphisms. -/
theorem map_famTarget {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) (q : R) :
    (famTarget m q).map (Polynomial.mapRingHom φ) = famTarget m (φ q) := by
  simp only [famTarget, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
    map_famCheb, map_C, map_X, Polynomial.map_one, coe_mapRingHom, Polynomial.map_pow,
    map_pow]

/-- The family coefficient matrix commutes with ring homomorphisms. -/
private theorem mapMatrix_famMatrix {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (m : ℕ) (q : R) :
    (Polynomial.mapRingHom φ).mapMatrix (famMatrix m q) = famMatrix m (φ q) := by
  ext k i : 1
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, famMatrix, famMatrix, Matrix.of_apply,
    Matrix.of_apply, ← map_famBasisPoly, coeff_map]

/-- The family determinant commutes with ring homomorphisms. -/
theorem map_famDet {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) (q : R) :
    (famDet m q).map φ = famDet m (φ q) := by
  rw [famDet, famDet, ← coe_mapRingHom, RingHom.map_det, mapMatrix_famMatrix]

/-- The family Cramer coefficients commute with ring homomorphisms. -/
theorem map_famCoeff {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) (q : R)
    (i : Fin (2 * m + 4)) : (famCoeff m q i).map φ = famCoeff m (φ q) i := by
  rw [famCoeff, famCoeff, Matrix.cramer_apply, Matrix.cramer_apply, ← coe_mapRingHom,
    RingHom.map_det, ← mapMatrix_famMatrix φ m q, RingHom.mapMatrix_apply,
    RingHom.mapMatrix_apply, Matrix.map_updateCol]
  congr 2
  ext k : 1
  rw [Function.comp_apply, ← map_famTarget, coeff_map]

end AJConjecture
