import Mathlib
import AJConjecture.ClaspAlgClaspEigenMid
import AJConjecture.ClaspAlgCoeffMid

/-!
# The clasp eigenvalues are the clasp coefficients (identity J3)

`(-1)^c θ_c² ξ_{c,n} = claspAlgCoeff (c+1) n` for `0 ≤ n ≤ c`, with `θ_c² = t^(2c(c+2))`.

Route. Write `P_m = (q; q)_m` and `M = c - n`. Termwise,
`(-1)^c θ_c² s_k d_{c-k,n} = t^(4c²+2c) P_(c-n) P_(c+n+1) q^(k²-2ck) P_k / (P_(c-k)² P_(k-n) P_(k+n+1))`
and `[N] C_j(N) K_{j,n} = t^(-2c) (-1)^(n+j) q^(n(n+1)/2 + j(j+1)/2 - cj) P_(c+1+j) P_j /
(P_(c-j) P_(j-n) P_(j+n+1))`. Up to explicit factors the left side is the terminating series
`₃φ₂(q^(-M), q^(-M), q^(n+1); q^(2n+2), 0; q, q)` and the right side is
`₃φ₂(q^(-M), q^(2n+2+M), q^(n+1); q^(2n+2), 0; q, q)`: the identity is the case `e = 0` of Sears'
transformation `₃φ₂(q^(-M), a, b; d, e; q, q) = ((de/ab; q)_M / (e; q)_M) (ab/d)^M
₃φ₂(q^(-M), d/a, d/b; d, de/ab; q, q)` (Gasper–Rahman (III.11)) with `a = q^(-M)`, `b = q^(n+1)`,
`d = b²`. Proof of that case: both sides are equal to an explicit multiple of
`∑_{p=n}^{c} q^(-(c+1)p) P_(c+1+p) P_p / (P_(c-p) P_(p-n) P_(p+n+1))`; for each side, expand one
factor of the summand by the `q`-Chu–Vandermonde sum, exchange the two summations, and evaluate
the inner sum by the case `C = 0` of the `q`-Chu–Vandermonde sum
(`claspAlgClaspEigen_eq_searsMid`, `claspAlgCoeff_eq_searsMid`). The hypothesis `n ≤ c` is
needed (at `n = c + 1` the left side is not zero and the right side is).
-/

namespace AJConjecture

/-- Identity J3: the eigenvalue of the clasp in the turnback basis, normalised by the framing
factor `(-1)^c θ_c²`, is the clasp coefficient of the cyclotomic formula at the colour `c + 1`. -/
theorem claspAlgClaspEigen_eq_claspAlgCoeff (c n : ℕ) (hn : n ≤ c) :
    (-1) ^ c * (RatFunc.X : RatFunc ℚ) ^ (2 * (c : ℤ) * ((c : ℤ) + 2)) * claspAlgClaspEigen c n =
      claspAlgCoeff (c + 1) n := by
  rw [claspAlgClaspEigen_eq_searsMid c n hn, claspAlgCoeff_eq_searsMid c n hn]

end AJConjecture
