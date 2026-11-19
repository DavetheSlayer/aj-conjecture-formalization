import Mathlib
import AJConjecture.WhiteheadFormula

/-!
# The bilateral kernel of the Bailey-type transform

`K_(j,n) = q^j (1 - q) (q;q)_j (-1)^n q^(n(n+1)/2) / ((q;q)_(j-n) (q;q)_(j+n+1))` for
`-j-1 ≤ n ≤ j`, and `0` otherwise. The cyclotomic coefficients of `T(2, a)` are half of the
bilateral sum of its odd colours against this kernel.
-/

noncomputable section

namespace AJConjecture

/-- The bilateral kernel `K_(j,n)`, supported on `-j-1 ≤ n ≤ j`. -/
def cycloBilateralKernel (j : ℕ) (n : ℤ) : RatFunc ℚ :=
  if -((j : ℤ) + 1) ≤ n ∧ n ≤ j then
    qParam ^ j * (1 - qParam) * qPochhammer qParam j * (-1) ^ n * qParam ^ (n * (n + 1) / 2)
      / (qPochhammer qParam ((j : ℤ) - n).toNat * qPochhammer qParam ((j : ℤ) + n + 1).toNat)
  else 0

/-- The bilateral transform `∑_{n = -j-1}^{j} K_(j,n) g(n)` of a sequence `g` on `ℤ`. -/
def cycloBilateralSum (g : ℤ → RatFunc ℚ) (j : ℕ) : RatFunc ℚ :=
  ∑ n ∈ Finset.Icc (-((j : ℤ) + 1)) (j : ℤ), cycloBilateralKernel j n * g n

end AJConjecture
