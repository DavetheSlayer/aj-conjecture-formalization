import Mathlib
import AJConjecture.QAlgNodeJet

/-!
# The maximal ideal of the point `(t, M) = (-1, m₀)` of `ℂ[t][M]`

`nodeIdeal m₀` is the kernel of `f ↦ f(-1, m₀)`, a prime (maximal) ideal; the local ring of the
plane at the point is `Localization.AtPrime (nodeIdeal m₀)`, a unique factorisation domain.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The ideal of the polynomials of `ℂ[t][M]` vanishing at `(t, M) = (-1, m₀)`. -/
def nodeIdeal (m₀ : ℂ) : Ideal ℂ[X][X] :=
  RingHom.ker ((Polynomial.evalRingHom m₀).comp complexSpec)

/-- The ideal of a point is prime. -/
instance nodeIdeal_isPrime (m₀ : ℂ) : (nodeIdeal m₀).IsPrime :=
  RingHom.ker_isPrime _

end AJConjecture
