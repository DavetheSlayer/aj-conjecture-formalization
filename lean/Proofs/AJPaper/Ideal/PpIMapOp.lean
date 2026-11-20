import Mathlib
import AJPaper.Ideal.PpIDefs

/-!
# Change of the coefficient ring in the quantum torus (Unit PpI, node `PpI_MapOp`)

* `ppiMapOp φ`: change of the coefficient ring of an element of the quantum torus along
  `φ : A →+* B`.
* `ppiApply_ppiMapOp`: it commutes with the action on sequences. Route: `Finsupp.sum_mapRange_index`
  and multiplicativity of `AddMonoidAlgebra.mapRingHom ℤ φ`
  (`AddMonoidAlgebra.mapRingHom_single` for the monomial `T (2kn)`).
* `ppiAnnihilates_ppiMapOp_iff`: annihilation of the coloured Jones function is unchanged along
  an injective `φ`: `ppiJones B K = φ ∘ ppiJones A K` because
  `Int.castRingHom B = φ.comp (Int.castRingHom A)`, and `AddMonoidAlgebra.mapRingHom ℤ φ` is
  injective when `φ` is.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Change of the coefficient ring of an element of the quantum torus. -/
def ppiMapOp {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (P : PpiOp A) : PpiOp B :=
  P.mapRange (AddMonoidAlgebra.mapRingHom ℤ φ) (map_zero _)

/-- A change of coefficients fixes the monomials `t^m`. -/
private theorem ppiMapRingHom_T_MapOp {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (m : ℤ) : AddMonoidAlgebra.mapRingHom ℤ φ (LaurentPolynomial.T m) = LaurentPolynomial.T m := by
  simp only [LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]

/-- The action commutes with a change of the coefficient ring. -/
theorem ppiApply_ppiMapOp {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (P : PpiOp A)
    (g : ℤ → LaurentPolynomial A) (n : ℤ) :
    ppiApply (ppiMapOp φ P) (fun m ↦ AddMonoidAlgebra.mapRingHom ℤ φ (g m)) n =
      AddMonoidAlgebra.mapRingHom ℤ φ (ppiApply P g n) := by
  unfold ppiApply ppiMapOp
  rw [Finsupp.sum_mapRange_index (fun kl ↦ by simp), map_finsuppSum]
  refine Finsupp.sum_congr fun kl _ ↦ ?_
  rw [map_mul, map_mul, ppiMapRingHom_T_MapOp]

/-- Along an injective change of coefficients, annihilation of the coloured Jones function is
unchanged. -/
theorem ppiAnnihilates_ppiMapOp_iff {A B : Type} [CommRing A] [CommRing B] {φ : A →+* B}
    (hφ : Function.Injective φ) (P : PpiOp A) (K : BraidKnot) :
    PpiAnnihilates (ppiMapOp φ P) K ↔ PpiAnnihilates P K := by
  have hJ : ppiJones B K = fun m ↦ AddMonoidAlgebra.mapRingHom ℤ φ (ppiJones A K m) := by
    funext m
    have hc : Int.castRingHom B = φ.comp (Int.castRingHom A) := RingHom.ext_int _ _
    simp only [ppiJones]
    rw [hc, AddMonoidAlgebra.mapRingHom_comp, RingHom.comp_apply]
  have hinj : Function.Injective (AddMonoidAlgebra.mapRingHom ℤ φ) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    ext m
    have hm := congrArg (fun y ↦ y.coeff m) hx
    simp only [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply] at hm
    simpa using (map_eq_zero_iff φ hφ).1 hm
  unfold PpiAnnihilates
  refine forall_congr' fun n ↦ ?_
  rw [hJ, ppiApply_ppiMapOp, map_eq_zero_iff _ hinj]

end AJConjecture
