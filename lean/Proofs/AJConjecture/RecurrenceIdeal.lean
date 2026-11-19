import Mathlib

/-!
# Recurrence operators and the recurrence polynomial

Operators `∑ D_i(t, M) L^i` act on sequences `f : ℤ → ℤ[t, t⁻¹]` by `(M f)(n) = t^(2n) f(n)`,
`(L f)(n) = f(n + 1)`, so that `L M = t² M L`; coefficients are written on the left. The
recurrence polynomial of `f` is the primitive element of minimal `L`-degree of the annihilator
ideal of `f` localised over `ℚ(t, M)`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The coefficient ring `ℤ[t][M]` of recurrence operators: inner variable `t`, outer `M`. -/
abbrev Coeff : Type := ℤ[X][X]

/-- Recurrence operators `∑ D_i(t, M) L^i`, coefficients written on the left. -/
abbrev RecOp : Type := Coeff[X]

/-- The value `D(t, t^(2n))` of a coefficient at the colour `n` (`M` acts by `t^(2n)`). -/
def evalAt (n : ℤ) : Coeff →+* ℤ[T;T⁻¹] :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℤ[T;T⁻¹]) (T 1)) (T (2 * n))

/-- The action of a recurrence operator on a sequence: `(P f)(n) = ∑ D_i(t, t^(2n)) f(n + i)`. -/
def opApply (P : RecOp) (f : ℤ → ℤ[T;T⁻¹]) (n : ℤ) : ℤ[T;T⁻¹] :=
  P.sum fun i D ↦ evalAt n D * f (n + i)

/-- `P` annihilates `f` at every integer colour. -/
def Annihilates (P : RecOp) (f : ℤ → ℤ[T;T⁻¹]) : Prop :=
  ∀ n : ℤ, opApply P f n = 0

/-- `Q` belongs to the localisation over `ℚ(t, M)` of the annihilator ideal of `f`: some nonzero
left coefficient multiple of `Q` annihilates `f` at every integer colour. -/
def InLocalizedAnnihilator (f : ℤ → ℤ[T;T⁻¹]) (Q : RecOp) : Prop :=
  ∃ c : Coeff, c ≠ 0 ∧ Annihilates (Polynomial.C c * Q) f

/-- `α` is the primitive generator of minimal `L`-degree of the localised annihilator ideal of
`f`: the recurrence polynomial `α_K` when `f` is the coloured Jones function of `K`. -/
def IsRecurrencePolynomial (f : ℤ → ℤ[T;T⁻¹]) (α : RecOp) : Prop :=
  α ≠ 0 ∧ InLocalizedAnnihilator f α ∧
    (∀ Q : RecOp, Q ≠ 0 → InLocalizedAnnihilator f Q → α.natDegree ≤ Q.natDegree) ∧
    α.IsPrimitive

/-- The specialisation `α(t, M, L) ↦ α(-1, M, L)` with `M` kept as an indeterminate. -/
def specialize : RecOp →+* ℤ[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.evalRingHom (-1 : ℤ)))

/-- The comparison ring `R = ℚ(M)[L, L⁻¹]`. -/
abbrev ComparisonRing : Type := (RatFunc ℚ)[T;T⁻¹]

/-- The map `ℤ[M][L] → ℚ(M)[L, L⁻¹]`. -/
def toComparison : ℤ[X][X] →+* ComparisonRing :=
  (Polynomial.toLaurent).comp
    (Polynomial.mapRingHom
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))))

end AJConjecture
