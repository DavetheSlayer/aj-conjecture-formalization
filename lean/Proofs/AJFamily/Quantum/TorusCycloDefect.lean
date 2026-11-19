import Mathlib
import AJConjecture.QAlgCycloStep
import AJFamily.Quantum.TorusFormula

/-!
# The cyclotomic defect

The defect `e_j = (S_(m-1)(V) + (1 - q^(j+1)) S_m(V) - q^(j+1) S_(m+1)(V)) D_j`, `m = 2a`, of the
cyclotomic coefficients of `T(2, a)`, where `S_k(V)` is `cycloCheb k`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The defect of the family's cyclotomic coefficients (`m = 2a`). -/
def torusCycloDefect (a : ℕ) (j : ℕ) : RatFunc ℚ :=
  cycloCheb (2 * a - 1) (torusCyclotomicCoeff a) j
    + (1 - qParam * qParam ^ j) * cycloCheb (2 * a) (torusCyclotomicCoeff a) j
    - qParam * qParam ^ j * cycloCheb (2 * a + 1) (torusCyclotomicCoeff a) j

end AJConjecture
