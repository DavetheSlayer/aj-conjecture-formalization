import Mathlib
import AJConjecture.KnotGroup

/-!
# The A-polynomial

The boundary eigenvalue set of a knot is the set of pairs `(M, L)` of eigenvalues of the
meridian and the preferred longitude on a common eigenvector, over all representations of the
knot group into `SL₂(ℂ)`. The A-polynomial is the square-free defining polynomial of the union
of the one-dimensional components of its Zariski closure; the abelian representations give
the factor `L - 1`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The set of pairs `(M, L)` of eigenvalues of the meridian and of the longitude on a common
eigenvector, over all representations of the knot group into `SL₂(ℂ)`. -/
def eigenvalueSet (K : BraidKnot) : Set (ℂ × ℂ) :=
  {p | ∃ ρ : KnotGroup K →* Matrix.SpecialLinearGroup (Fin 2) ℂ,
    (ρ (meridian K)).1 1 0 = 0 ∧ (ρ (longitude K)).1 1 0 = 0 ∧
    (ρ (meridian K)).1 0 0 = p.1 ∧ (ρ (longitude K)).1 0 0 = p.2}

/-- The value of `P ∈ ℂ[M][L]` (inner variable `M`, outer variable `L`) at a point `(M, L)`. -/
def evalPoint (P : ℂ[X][X]) (p : ℂ × ℂ) : ℂ :=
  P.eval₂ (Polynomial.evalRingHom p.1) p.2

/-- The Zariski closure of a subset of the affine plane. -/
def zariskiClosure (S : Set (ℂ × ℂ)) : Set (ℂ × ℂ) :=
  {p | ∀ P : ℂ[X][X], (∀ s ∈ S, evalPoint P s = 0) → evalPoint P p = 0}

/-- `A ∈ ℤ[M][L]` is a square-free defining polynomial of the union of the one-dimensional
components of the Zariski closure of `S`: it is square-free over `ℂ`, and an irreducible
polynomial divides it exactly when its zero set is contained in the closure of `S`. -/
def IsAPolynomialOf (S : Set (ℂ × ℂ)) (A : ℤ[X][X]) : Prop :=
  Squarefree (A.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) ∧
    ∀ g : ℂ[X][X], Irreducible g →
      (g ∣ A.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) ↔
        ∀ p : ℂ × ℂ, evalPoint g p = 0 → p ∈ zariskiClosure S)

end AJConjecture
