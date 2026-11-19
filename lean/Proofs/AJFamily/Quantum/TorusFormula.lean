import Mathlib
import AJConjecture.WhiteheadFormula

/-!
# The torus formula

The closed formula `torusWhiteheadFormula a n = [n] F_n`, `F_N = ∑_{j<N} C_j(N) D_j`, built from the
odd colours of `T(2, a)`. For `a = 2k + 1` it is the coloured Jones function of
`whiteheadTorusKnot k` (`laurentToField_coloredJones_whiteheadTorusKnot`).
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The odd colours of `T(2, a)`:
`u_n = q^(-2a n(n+1)) ∑_{s=-n}^{n} q^(a s(2s+1)) [4s+1]`. -/
def torusOddColor (a : ℕ) (n : ℕ) : RatFunc ℚ :=
  qParam ^ (-(2 * (a : ℤ) * (n : ℤ) * ((n : ℤ) + 1))) *
    ∑ s ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), qParam ^ ((a : ℤ) * s * (2 * s + 1)) * quantumInt (4 * s + 1)

/-- The cyclotomic coefficients `D_j` of `T(2, a)`. -/
def torusCyclotomicCoeff (a : ℕ) (j : ℕ) : RatFunc ℚ :=
  qParam ^ j * (1 - qParam) * qPochhammer qParam j *
    ∑ n ∈ Finset.range (j + 1), (-1) ^ n * qParam ^ (n * (n + 1) / 2) * torusOddColor a n /
      (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))

/-- The reduced formula `F_N = ∑_{j < N} C_j(N) D_j`. -/
def torusReducedFormula (a : ℕ) (N : ℕ) : RatFunc ℚ :=
  ∑ j ∈ Finset.range N, cyclotomicKernel j N * torusCyclotomicCoeff a j

/-- The unreduced formula `[n] F_n`, extended to all integers as an odd function. -/
def torusWhiteheadFormula (a : ℕ) (n : ℤ) : RatFunc ℚ :=
  if 0 < n then quantumInt n * torusReducedFormula a n.toNat
  else if n < 0 then -(quantumInt (-n) * torusReducedFormula a (-n).toNat)
  else 0

end AJConjecture
