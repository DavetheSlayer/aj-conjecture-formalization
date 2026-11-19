import Mathlib
import AJConjecture.QAlgCycloStep
import AJFamily.Quantum.TorusCycloDefect
import AJFamily.Quantum.TorusOddColorInt
import AJFamily.Quantum.FamTransferKernel
import AJFamily.Quantum.FamTransferCoeff

/-!
# The closed formula of a companion input, and the odd colours of `T(r, s)`

For an input sequence `u : ℕ → ℚ(t)` (the companion's coloured Jones polynomials at the odd
colours `2n + 1`) the satellite formula is `[N] F_N`, `F_N = ∑_{j<N} C_j(N) D_j`,
`D_j = ∑_{n ≤ j} K_{j,n} u_n`, with the cyclotomic kernel `C_j(N)` and the Bailey kernel `K_{j,n}`
of the library (source `quantum_torus_transfer.md`, Q4). The definitions are those of
`AJFamily.Quantum.TorusFormula` with `torusOddColor a` replaced by an arbitrary `u`; the bridge
lemmas below record that the library's objects are the instance `u = torusOddColor a`.

`pairQTransferRhs m c e` is the right-hand side of the transfer identity Q10.

`pairQOddColor r s` is the source formula Q1 (Zheng, arXiv:math/0508138v4, (4.1)) for the odd
colours of the torus knot `T(r, s)`; `pairQForcing r s` is the forcing term of its first-order
recurrence Q3, written, like `torusForcing`, with powers of `t`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The odd colours of the torus knot `T(r, s)` (source Q1):
`u_n = q^(-rs n(n+1)) ∑_{k=-n}^{n} q^(r k(sk+1)) [2sk+1]`. -/
def pairQOddColor (r s : ℕ) (n : ℕ) : RatFunc ℚ :=
  qParam ^ (-((r : ℤ) * s * n * ((n : ℤ) + 1))) *
    ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
      qParam ^ ((r : ℤ) * k * ((s : ℤ) * k + 1)) * quantumInt (2 * (s : ℤ) * k + 1)

/-- The cyclotomic coefficients `D_j = ∑_{n ≤ j} K_{j,n} u_n` of an input sequence `u`. -/
def pairQCycloCoeff (u : ℕ → RatFunc ℚ) (j : ℕ) : RatFunc ℚ :=
  qParam ^ j * (1 - qParam) * qPochhammer qParam j *
    ∑ n ∈ Finset.range (j + 1), (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
      (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))

/-- The reduced formula `F_N = ∑_{j < N} C_j(N) D_j` of an input sequence `u`. -/
def pairQReducedFormula (u : ℕ → RatFunc ℚ) (N : ℕ) : RatFunc ℚ :=
  ∑ j ∈ Finset.range N, cyclotomicKernel j N * pairQCycloCoeff u j

/-- The unreduced formula `[n] F_n` of an input sequence `u`, extended to all integers as an odd
function. -/
def pairQFormula (u : ℕ → RatFunc ℚ) (n : ℤ) : RatFunc ℚ :=
  if 0 < n then quantumInt n * pairQReducedFormula u n.toNat
  else if n < 0 then -(quantumInt (-n) * pairQReducedFormula u (-n).toNat)
  else 0

/-- The even extension `n ↦ F_|n|` of the reduced formula. -/
def pairQReducedFormulaEven (u : ℕ → RatFunc ℚ) (n : ℤ) : RatFunc ℚ :=
  pairQReducedFormula u n.natAbs

/-- An input sequence extended to all integers by `u_(-n-1) = -u_n`. -/
def pairQOddExt (u : ℕ → RatFunc ℚ) (n : ℤ) : RatFunc ℚ :=
  if 0 ≤ n then u n.toNat else -u (-n - 1).toNat

/-- The defect `e_j = (S_(m-1)(V) + (1 - q^(j+1)) S_m(V) - q^(j+1) S_(m+1)(V)) D_j` of the
cyclotomic coefficients of `u`, for the parameter `m` (source Q8; `S_k(V)` is `cycloCheb k`). -/
def pairQCycloDefect (m : ℕ) (u : ℕ → RatFunc ℚ) (j : ℕ) : RatFunc ℚ :=
  cycloCheb (m - 1) (pairQCycloCoeff u) j
    + (1 - qParam * qParam ^ j) * cycloCheb m (pairQCycloCoeff u) j
    - qParam * qParam ^ j * cycloCheb (m + 1) (pairQCycloCoeff u) j

/-- The forcing term `h_(r,s)(q^n)` of the recurrence of the odd colours of `T(r, s)` (source Q3),
with `m = rs`: `(t² - t⁻²) h = t^(4(r+s-m)(n+1)+2) - t^(4(r-s-m)(n+1)-2) - t^(4(s-r-m)(n+1)-2)
+ t^(-4(r+s+m)(n+1)+2)`. -/
def pairQForcing (r s : ℕ) (n : ℤ) : RatFunc ℚ :=
  (RatFunc.X ^ (4 * ((r : ℤ) + s - r * s) * (n + 1) + 2)
      - RatFunc.X ^ (4 * ((r : ℤ) - s - r * s) * (n + 1) - 2)
      - RatFunc.X ^ (4 * ((s : ℤ) - r - r * s) * (n + 1) - 2)
      + RatFunc.X ^ (-4 * ((r : ℤ) + s + r * s) * (n + 1) + 2))
    / (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))

/-- The right-hand side of the transfer identity (source Q10, in the integral normalization of
`famTransferOp m`): for the colour `n`, with `d = 2m + 3` and `N = n + d`,
`det(q^N) (q^d q^N)^(m+1) ∑_{j < c} G_j(N) e_j`, where `G_j(N) = famKernel m j N` and `e_j` are
the finitely many nonzero defects. -/
def pairQTransferRhs (m c : ℕ) (e : ℕ → RatFunc ℚ) (n : ℤ) : RatFunc ℚ :=
  (famDet m qParam).eval (qParam ^ (n + (2 * m + 3))) *
    (qParam ^ (2 * m + 3) * qParam ^ (n + (2 * m + 3))) ^ (m + 1) *
      ∑ j ∈ Finset.range c, famKernel m j (n + (2 * m + 3)) * e j

/-! ### The library's objects are the instance `u = torusOddColor a` -/

theorem pairQCycloCoeff_torus (a : ℕ) :
    pairQCycloCoeff (torusOddColor a) = torusCyclotomicCoeff a := rfl

theorem pairQReducedFormula_torus (a : ℕ) :
    pairQReducedFormula (torusOddColor a) = torusReducedFormula a := rfl

theorem pairQFormula_torus (a : ℕ) :
    pairQFormula (torusOddColor a) = torusWhiteheadFormula a := rfl

theorem pairQOddExt_torus (a : ℕ) : pairQOddExt (torusOddColor a) = torusOddColorInt a := rfl

theorem pairQCycloDefect_torus (a : ℕ) :
    pairQCycloDefect (2 * a) (torusOddColor a) = torusCycloDefect a := rfl

end AJConjecture
