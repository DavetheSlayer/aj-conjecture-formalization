import Mathlib
import AJConjecture.RecurrenceIdeal

/-!
# Sequences in `ℚ(t)` and the action of recurrence operators on them

In the field `ℚ(t)`, with `q = t⁴`: the embedding `laurentToField` of `ℤ[t, t⁻¹]`, the quantum
integers, the `q`-Pochhammer symbols, the cyclotomic kernel
`C_j(N) = ∏_{s=1}^{j} (1 - q^(s+N)) (1 - q^(s-N))`, and the action `opApplyField` of recurrence
operators on sequences with values in `ℚ(t)`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The embedding `ℤ[t, t⁻¹] → ℚ(t)`. -/
def laurentToField : ℤ[T;T⁻¹] →+* RatFunc ℚ :=
  LaurentPolynomial.eval₂ (Int.castRingHom (RatFunc ℚ)) (Units.mk0 RatFunc.X RatFunc.X_ne_zero)

/-- The parameter `q = t⁴`. -/
def qParam : RatFunc ℚ :=
  RatFunc.X ^ 4

/-- The quantum integer `[m] = (t^(2m) - t^(-2m)) / (t² - t⁻²)`. -/
def quantumInt (m : ℤ) : RatFunc ℚ :=
  (RatFunc.X ^ (2 * m) - RatFunc.X ^ (-(2 * m))) / (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))

/-- The `q`-Pochhammer symbol `(a; q)_j = ∏_{s < j} (1 - a q^s)`. -/
def qPochhammer (a : RatFunc ℚ) (j : ℕ) : RatFunc ℚ :=
  ∏ s ∈ Finset.range j, (1 - a * qParam ^ s)

/-- The cyclotomic kernel `C_j(N) = ∏_{s=1}^{j} (1 - q^(s+N)) (1 - q^(s-N))`. -/
def cyclotomicKernel (j : ℕ) (N : ℤ) : RatFunc ℚ :=
  ∏ s ∈ Finset.Icc 1 j, (1 - qParam ^ ((s : ℤ) + N)) * (1 - qParam ^ ((s : ℤ) - N))

/-- The value `D(t, t^(2n))` in `ℚ(t)` of a coefficient at the colour `n`. -/
def evalAtField (n : ℤ) : Coeff →+* RatFunc ℚ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X)
    (RatFunc.X ^ (2 * n))

/-- The action of a recurrence operator on a sequence with values in `ℚ(t)`:
`(P f)(n) = ∑ D_i(t, t^(2n)) f(n + i)`. -/
def opApplyField (P : RecOp) (f : ℤ → RatFunc ℚ) (n : ℤ) : RatFunc ℚ :=
  P.sum fun i D ↦ evalAtField n D * f (n + i)

end AJConjecture
