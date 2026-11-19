import Mathlib
import AJConjecture.QAlgCycloBilateralKernel

/-!
# The scalars of the clasp computation

The skein-theoretic evaluation of the coloured Jones function of a Whitehead double ends with
explicit scalars in `ℚ(t)`. With `[m] = quantumInt m`, `q = t⁴` and `c = N - 1` the cabling
parameter of the colour `N`, they are:

* `λ_{c,n} = (-1)^(c-n) t^(2n(n+1) - c(c+2))`, the eigenvalues of the cabled half twist on two
  bundles carrying Jones–Wenzl projectors (`0 ≤ n ≤ c`);
* `d_{j,n} = ∏_{i<j} (-[c-n-i][c+n+1-i] / [c-i]²)`, the eigenvalues of the turnback element `D_j`
  of the two-bundle algebra (they depend on `c`; `d_{j,n} = 0` for `c - n < j ≤ c`);
* the quantum factorial `[k]!` and the quantum binomial `[c choose k]`;
* `s_k = t^(2c² - 4ck + k² - k) (t² - t⁻²)^k [c]!² / ([c-k]!² [k]!)`, the coefficients of the cabled
  full twist in the turnback basis;
* `ξ_{c,n} = ∑_{k=0}^{c} s_k d_{c-k,n}`, the eigenvalues of the clasp (the terms with `k < n`
  vanish);
* `claspAlgCoeff N n = [N] ∑_{j=n}^{N-1} C_j(N) K_{j,n}`, the coefficient of the odd colour `u_n`
  of the companion in the unreduced formula `[N] F_N`.

The kink scalar `θ_k = (-1)^k t^(k(k+2))` is not defined here; the statements of this family
of files write `(-1)^c θ_c² = (-1)^c t^(2c(c+2))` and `θ_{2n}³ = t^(12n(n+1))` explicitly.
-/

noncomputable section

namespace AJConjecture

/-- The eigenvalue `λ_{c,n} = (-1)^(c-n) t^(2n(n+1) - c(c+2))` of the cabled half twist; the sign
is written `(-1)^(c+n)`. -/
def claspAlgHalfTwistEigen (c n : ℕ) : RatFunc ℚ :=
  (-1) ^ (c + n) *
    (RatFunc.X : RatFunc ℚ) ^ (2 * (n : ℤ) * ((n : ℤ) + 1) - (c : ℤ) * ((c : ℤ) + 2))

/-- The eigenvalue `d_{j,n} = ∏_{i<j} (-[c-n-i][c+n+1-i] / [c-i]²)` of the turnback element `D_j`
at the cabling parameter `c`. -/
def claspAlgTurnbackEigen (c j n : ℕ) : RatFunc ℚ :=
  ∏ i ∈ Finset.range j,
    -(quantumInt ((c : ℤ) - n - i) * quantumInt ((c : ℤ) + n + 1 - i)) / quantumInt ((c : ℤ) - i) ^ 2

/-- The quantum factorial `[k]! = [1][2]⋯[k]`. -/
def claspAlgQFactorial (k : ℕ) : RatFunc ℚ :=
  ∏ i ∈ Finset.range k, quantumInt ((i : ℤ) + 1)

/-- The coefficient `s_k = t^(2c² - 4ck + k² - k) (t² - t⁻²)^k [c]!² / ([c-k]!² [k]!)` of the
turnback element `D_k` in the cabled full twist. -/
def claspAlgFullTwistCoeff (c k : ℕ) : RatFunc ℚ :=
  (RatFunc.X : RatFunc ℚ) ^ (2 * (c : ℤ) ^ 2 - 4 * (c : ℤ) * (k : ℤ) + (k : ℤ) ^ 2 - (k : ℤ)) *
    ((RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) ^ k *
    claspAlgQFactorial c ^ 2 / (claspAlgQFactorial (c - k) ^ 2 * claspAlgQFactorial k)

/-- The eigenvalue `ξ_{c,n} = ∑_{k=0}^{c} s_k d_{c-k,n}` of the clasp. -/
def claspAlgClaspEigen (c n : ℕ) : RatFunc ℚ :=
  ∑ k ∈ Finset.range (c + 1), claspAlgFullTwistCoeff c k * claspAlgTurnbackEigen c (c - k) n

/-- The clasp coefficient `[N] ∑_{j=n}^{N-1} C_j(N) K_{j,n}`: the coefficient of the odd colour
`u_n` in the unreduced formula `[N] F_N`. -/
def claspAlgCoeff (N n : ℕ) : RatFunc ℚ :=
  quantumInt N * ∑ j ∈ Finset.Ico n N, cyclotomicKernel j N * cycloBilateralKernel j n

end AJConjecture
