import Mathlib
import AJConjecture.QAlgWeylSymbol

/-!
# Jets at `t = -1` of coefficients, over `ℤ` and over `ℂ`

Coefficients live in `ℤ[t][M]` (`Coeff`) or, after base change, in `ℂ[t][M]`.

* `coeffToComplex`: the base change `ℤ[t][M] → ℂ[t][M]`.
* `complexShift`: the shift `M ↦ t² M` on `ℂ[t][M]` (the base change of `coeffShift`).
* `complexSpec f = f(-1, M)` and `complexJet f = (∂f/∂t)(-1, M)`, in `ℂ[M]`; `coeffJet` is the
  first jet on `ℤ[t][M]`, the coefficientwise version of `specializeJet`.
* `nodeNumer R`, `nodeDenom R ∈ ℤ[M]`: for an operator `R` of degree `d` with constant
  coefficient `r_0` and leading coefficient `r_d`, the first jet of `r_0 / r_d` at `t = -1`
  divided by its value is `nodeNumer R / nodeDenom R`, where
  `nodeNumer R = r_0¹ r_d⁰ - r_0⁰ r_d¹` and `nodeDenom R = r_0⁰ r_d⁰`
  (upper index `0`: value at `t = -1`; upper index `1`: derivative in `t` at `t = -1`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The base change `ℤ[t][M] → ℂ[t][M]`. -/
def coeffToComplex : Coeff →+* ℂ[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℂ))

/-- The shift `M ↦ t² M` on `ℂ[t][M]`. -/
def complexShift : ℂ[X][X] →+* ℂ[X][X] :=
  Polynomial.compRingHom (C (X ^ 2) * X)

/-- The value `f(-1, M) ∈ ℂ[M]` at `t = -1` of `f ∈ ℂ[t][M]`. -/
def complexSpec : ℂ[X][X] →+* ℂ[X] :=
  Polynomial.mapRingHom (Polynomial.evalRingHom (-1))

/-- The first jet `(∂f/∂t)(-1, M) ∈ ℂ[M]` at `t = -1` of `f ∈ ℂ[t][M]`. -/
def complexJet (f : ℂ[X][X]) : ℂ[X] :=
  f.sum fun e a ↦ monomial e ((derivative a).eval (-1))

/-- The first jet `(∂c/∂t)(-1, M) ∈ ℤ[M]` at `t = -1` of a coefficient `c ∈ ℤ[t][M]`. -/
def coeffJet (c : Coeff) : ℤ[X] :=
  c.sum fun e a ↦ monomial e ((derivative a).eval (-1))

/-- The numerator `r_0¹ r_d⁰ - r_0⁰ r_d¹` of the logarithmic first jet of `r_0 / r_d`. -/
def nodeNumer (R : RecOp) : ℤ[X] :=
  (specializeJet R).coeff 0 * (specialize R).coeff R.natDegree -
    (specialize R).coeff 0 * (specializeJet R).coeff R.natDegree

/-- The denominator `r_0⁰ r_d⁰` of the logarithmic first jet of `r_0 / r_d`. -/
def nodeDenom (R : RecOp) : ℤ[X] :=
  (specialize R).coeff 0 * (specialize R).coeff R.natDegree

end AJConjecture
