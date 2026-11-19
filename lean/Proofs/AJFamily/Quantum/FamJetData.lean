import Mathlib
import AJConjecture.QAlgTransferJetData

/-!
# Data for the first-order jets

The expressions in `(q, x, j)` describing the family adjoint, Chebyshev operators and target
polynomial when `(1 - q)² = 0`, and the dual number `famDualX`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `ζ(q, x, J)`, the multiplier of `n` in the first-order expansion of `famAdjoint`. -/
def famJetZeta {R : Type*} [CommRing R] (m : ℕ) (q x j : R) : R :=
  x ^ 2 + q ^ (2 * m + 3) * (1 + x) + (q ^ (2 * m + 3) * x - q ^ (2 * m + 4) - q * x * (1 + x)) * j +
    q ^ 2 * x * j ^ 2

/-- The `J`-derivative of `famJetZeta`. -/
def famJetZetaDeriv {R : Type*} [CommRing R] (m : ℕ) (q x j : R) : R :=
  q ^ (2 * m + 3) * x - q ^ (2 * m + 4) - q * x * (1 + x) + 2 * (q ^ 2 * x * j)

/-- The cubic `A = (1 - qJ)(x - qJ)(q^(2m+2) - xJ)`. -/
def famJetCubic {R : Type*} [CommRing R] (m : ℕ) (q x j : R) : R :=
  (1 - q * j) * (x - q * j) * (q ^ (2 * m + 2) - x * j)

/-- The first-order value of `famCheb m q k` at `(x, j)` on a numerator with value `v` and
`J`-derivative `v'`. -/
def famChebJetValue {R : Type*} [CommRing R] (m : ℕ) (q x j : R) (k : ℕ) (v v' : R) : R :=
  transferLucas (famJetZeta m q x j) (q ^ (4 * m + 5) * x ^ 2) k * v +
    (1 - q) * famJetCubic m q x j *
      (transferLucasDeriv (famJetZeta m q x j) (q ^ (4 * m + 5) * x ^ 2) k * v' +
        transferLucasHasse (famJetZeta m q x j) (q ^ (4 * m + 5) * x ^ 2) k *
          famJetZetaDeriv m q x j * v)

/-- The first-order value of `famTarget m q` at `(x, j)`. -/
def famTargetJetValue {R : Type*} [CommRing R] (m : ℕ) (q x j : R) : R :=
  (q ^ (2 * m + 3) * x) ^ 2 * famChebJetValue m q x j (m - 1) 1 0 +
    q ^ (2 * m + 3) * x * famChebJetValue m q x j m (1 - q * j) (-q) -
    famChebJetValue m q x j (m + 1) (q * j) q

/-- The dual number `(1 - 4dε) m₀²`, the value of `x = t^(4d) M²` at `t = -1 + ε`, `M = m₀`. -/
def famDualX (m : ℕ) (m₀ : ℂ) : DualNumber ℂ :=
  (1 - ((4 * (2 * m + 3) : ℕ) : DualNumber ℂ) * DualNumber.eps) * TrivSqZeroExt.inl (m₀ ^ 2)

end AJConjecture
