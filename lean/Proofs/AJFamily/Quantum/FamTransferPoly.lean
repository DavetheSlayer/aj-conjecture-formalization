import Mathlib

/-!
# The polynomials of the family transfer construction

The basis polynomials, the adjoint `famAdjoint` of `V = cycloStep` with its Chebyshev iterates,
and the target polynomial, from which `famTransferOp m` is built by Cramer's rule.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The basis polynomials `∏_{r<i} (q^r - x)(x - q^(r+1) J) ∏_{i≤r<d} (x - q^(r+1))(q^r - x J)`. -/
def famBasisPoly {R : Type*} [CommRing R] (m : ℕ) (q : R) (i : ℕ) : R[X][X] :=
  (∏ r ∈ Finset.range i, (C (C (q ^ r) - X) * (C X - C (C (q ^ (r + 1))) * X))) *
    ∏ r ∈ Finset.Ico i (2 * m + 3), (C (X - C (q ^ (r + 1))) * (C (C (q ^ r)) - C X * X))

/-- The adjoint of the operator `V = cycloStep` on numerators, multiplied by `q^d x`. -/
def famAdjoint {R : Type*} [CommRing R] (m : ℕ) (q : R) (n : R[X][X]) : R[X][X] :=
  C (C (q ^ (2 * m + 3)) * X) * X * n +
    divX (C (C (q ^ (2 * m + 2)) * X) * n -
      (1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ (2 * m + 2))) - C X * X) *
        n.comp (C (C q) * X))

/-- The adjoints of the twisted Chebyshev operators `cycloCheb k`. -/
def famCheb {R : Type*} [CommRing R] (m : ℕ) (q : R) : ℕ → R[X][X] → R[X][X]
  | 0, n => 2 * n
  | 1, n => famAdjoint m q n
  | k + 2, n =>
      famCheb m q (k + 1) (famAdjoint m q n) - C (C (q ^ (4 * m + 5)) * X ^ 2) * famCheb m q k n

/-- The target polynomial `(q^d x)² Š_{m-1}(1) + (q^d x) Š_m(1 - qJ) - Š_{m+1}(qJ)`, where
`Š_k = famCheb m q k`. -/
def famTarget {R : Type*} [CommRing R] (m : ℕ) (q : R) : R[X][X] :=
  C ((C (q ^ (2 * m + 3)) * X) ^ 2) * famCheb m q (m - 1) 1 +
    C (C (q ^ (2 * m + 3)) * X) * famCheb m q m (1 - C (C q) * X) -
      famCheb m q (m + 1) (C (C q) * X)

end AJConjecture
