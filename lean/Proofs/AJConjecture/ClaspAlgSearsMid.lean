import Mathlib
import AJConjecture.WhiteheadFormula

/-!
# The middle term of the Sears transformation behind the clasp identity

With `P_m = (q; q)_m`, `c = n + M` and `p = n + i`:
`Mid(n, M) = ∑_{p=n}^{c} q^(-(c+1)p) P_(c+1+p) P_p / (P_(c-p) P_(p-n) P_(p+n+1))`.
Both sides of the identity J3 between the clasp eigenvalue `ξ_{c,n}` and the clasp coefficient
`claspAlgCoeff (c+1) n` are equal to `t^(4c²+6c) Mid(n, c-n)`.
-/

noncomputable section

namespace AJConjecture

/-- The middle term `∑_{i=0}^{M} q^(-(n+M+1)(n+i)) P_(2n+M+1+i) P_(n+i) / (P_(M-i) P_i P_(2n+1+i))`
of the Sears transformation, with `P_m = (q; q)_m`. -/
def claspAlgSearsMid (n M : ℕ) : RatFunc ℚ :=
  ∑ i ∈ Finset.range (M + 1),
    qParam ^ (-(((n + M + 1) * (n + i) : ℕ) : ℤ)) * qPochhammer qParam (2 * n + M + 1 + i) *
      qPochhammer qParam (n + i) /
      (qPochhammer qParam (M - i) * qPochhammer qParam i * qPochhammer qParam (2 * n + 1 + i))

end AJConjecture
