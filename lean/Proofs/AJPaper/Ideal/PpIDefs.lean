import Mathlib
import AJConjecture.AJStatement
import AJConjecture.ColoredJones

/-!
# The quantum torus, raw annihilators and the specialization `t = -1` (Unit PpI, definitions)

Source: Section 8.5 of the paper (`conclusion.tex`, "The invariant recurrence ideal"), and the
two formulations it cites: A. T. Tran, *Proof of a stronger version of the AJ conjecture for
torus knots*, Algebr. Geom. Topol. 13 (2013), Section 1.1–1.2 (arXiv:1111.5065, Sections
0.1–0.2), and A. S. Sikora, *Quantizations of character varieties and quantum knot invariants*,
arXiv:0807.0943v2, Sections 1.3–1.6.

Tran: `ℛ = ℂ[t^{±1}]`, operators `(L f)(n) = f(n + 1)`, `(M f)(n) = t^{2n} f(n)` on functions
`f : ℤ → ℛ`, the quantum torus `𝒯 = ℛ⟨L^{±1}, M^{±1}⟩ / (L M - t² M L)` and the recurrence ideal
`𝒜_K = {P ∈ 𝒯 ∣ P J_K = 0}`; `ε` is the map reducing `t = -1`, with values in
`𝔱 = ℂ[M^{±1}, L^{±1}]`.

* `PpiOp A`: the elements of the quantum torus over `A[t^{±1}]` in the normal form
  `∑ c_{k,l}(t) M^k L^l` (finitely supported families of coefficients indexed by `(k, l)`).
  Only the module structure and the action on sequences are used: the conjectures are stated
  through the action, so the non-commutative product is not needed.
* `ppiApply P f n = ∑ c_{k,l}(t) t^{2kn} f(n + l)`: the action of `P` on a sequence.
* `ppiJones A K`: the coloured Jones function of the library with coefficients in `A`
  (`J_K(n) ∈ ℤ[t^{±1}]`, `J_unknot(n) = [n]`, `J_K(-n) = -J_K(n)`: Tran's normalization).
* `PpiAnnihilates P K`: `P J_K = 0` at every integer; over `ℂ` this is `P ∈ 𝒜_K`.
* `ppiOpSigma`: the involution `σ(M^k L^l) = M^{-k} L^{-l}` of the quantum torus.
* `PpiTorus = 𝔱 = ℂ[M^{±1}, L^{±1}]` (the group algebra of `ℤ × ℤ`; the monomial `M^k L^l` is
  `AddMonoidAlgebra.single (k, l) 1`) and its involution `ppiSigma`.
* `ppiEps`: the map `ε` reducing `t = -1`, coefficient by coefficient.
* `ppiEval p g`: the value of `g ∈ 𝔱` at a point `p = (M, L)`; it is a ring homomorphism in `g`
  when `M, L ≠ 0`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The elements `∑ c_{k,l}(t) M^k L^l` of the quantum torus with coefficients in `A[t, t⁻¹]`:
the family of coefficients, indexed by the exponents `(k, l)` of `M^k L^l`. -/
abbrev PpiOp (A : Type) [CommRing A] : Type := (ℤ × ℤ) →₀ LaurentPolynomial A

/-- The action on sequences: `(M^k L^l f)(n) = t^{2kn} f(n + l)`, so
`(P f)(n) = ∑ c_{k,l}(t) t^{2kn} f(n + l)`. -/
def ppiApply {A : Type} [CommRing A] (P : PpiOp A) (f : ℤ → LaurentPolynomial A) (n : ℤ) :
    LaurentPolynomial A :=
  P.sum fun kl c ↦ c * LaurentPolynomial.T (2 * kl.1 * n) * f (n + kl.2)

/-- The coloured Jones function of `K` with coefficients in `A`. -/
def ppiJones (A : Type) [CommRing A] (K : BraidKnot) (n : ℤ) : LaurentPolynomial A :=
  AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom A) (coloredJones K n)

/-- `P` annihilates the coloured Jones function of `K` at every integer colour: for `A = ℂ`
this is membership in the recurrence ideal `𝒜_K` of the quantum torus. -/
def PpiAnnihilates {A : Type} [CommRing A] (P : PpiOp A) (K : BraidKnot) : Prop :=
  ∀ n : ℤ, ppiApply P (ppiJones A K) n = 0

/-- The involution `σ(M^k L^l) = M^{-k} L^{-l}` of the quantum torus (the action of the Weyl
group `ℤ/2`). -/
def ppiOpSigma {A : Type} [CommRing A] (P : PpiOp A) : PpiOp A :=
  P.mapDomain fun kl ↦ -kl

/-- The commutative torus algebra `𝔱 = ℂ[M^{±1}, L^{±1}]`; `M^k L^l` is the basis element of
`(k, l) ∈ ℤ × ℤ`. -/
abbrev PpiTorus : Type := AddMonoidAlgebra ℂ (ℤ × ℤ)

/-- The involution `σ(M^k L^l) = M^{-k} L^{-l}` of `𝔱`. -/
def ppiSigma : PpiTorus ≃ₐ[ℂ] PpiTorus :=
  AddMonoidAlgebra.domCongr ℂ ℂ (AddEquiv.neg (ℤ × ℤ))

/-- The map `ε` reducing `t = -1`: every coefficient `c_{k,l}(t)` is replaced by
`c_{k,l}(-1)`. -/
def ppiEps (P : PpiOp ℂ) : PpiTorus :=
  AddMonoidAlgebra.ofCoeff
    (P.mapRange (LaurentPolynomial.eval₂ (RingHom.id ℂ) (-1 : ℂˣ)) (map_zero _))

/-- The value `∑ g_{k,l} M^k L^l` of `g ∈ 𝔱` at the point `p = (M, L)`. -/
def ppiEval (p : ℂ × ℂ) (g : PpiTorus) : ℂ :=
  g.coeff.sum fun kl c ↦ c * p.1 ^ kl.1 * p.2 ^ kl.2

end AJConjecture
