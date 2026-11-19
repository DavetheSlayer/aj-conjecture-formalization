import Mathlib
import AJTwist.TwDefs
import AJHandoff.TorusQuantum.PairQFormulaBasic

/-!
# The twisted companion input and the finite sum (Unit Q1)

Source: revision 5, Section 3 (`transfer.tex`), eq. (commoninput), (claspfinite),
(universalbailey). For the negative clasp put `m = r s` and `a = twIndex η r s ℓ = ± m - ℓ`. The
input of the finite transform is
`v_n = q^(-a n(n+1)) V_n(q^{±1}) = q^(ℓ n(n+1)) Φ_{T(r, ± s)}(2n+1)`, with the centred torus sum
`V_n(q) = ∑_{k=-n}^{n} q^(r k (s k + 1)) [2 s k + 1]`: the odd colours of the zero-framed
companion times the eigenvalue `q^(ℓ n(n+1))` of `ℓ` full twists. The mirror companion
(`η = false`) enters by inverting `q` in the torus sum; the clasp kernel is unchanged.

* `twInput η r s ℓ` is `v`; `twReduced`, `twReducedEven`, `twFormula` are the reduced sequence
  `F_N = ∑_{j<N} C_j(N) D_j`, its even extension and the unreduced formula `[n] F_|n|`, by the
  library's triangular transform (`pairQReducedFormula`, `pairQFormula`).
* `twFormula_true_zero`: for `ℓ = 0` and the right-handed companion this is the library's
  `pairQFormula (pairQOddColor r s)`.
* `AJTwist.Quantum.TwQInputBar`: the input of the mirror companion with twist `ℓ` is the bar of
  the input of the right-handed companion with twist `-ℓ`.
* `twPeriodInput ℓ c` is the input `w_n = q^(ℓ n(n+1)) (Q^c - \hat Q^c)` of the Gaussian period
  `G_c^{(ℓ)}` (Section 6.3).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The twisted companion input `v_n = q^(-a n(n+1)) V_n(q^{±1})`, `a = twIndex η r s ℓ`
(eq. (commoninput)). -/
def twInput (η : Bool) (r s : ℕ) (ℓ : ℤ) (n : ℕ) : RatFunc ℚ :=
  qParam ^ (-(twIndex η r s ℓ * n * ((n : ℤ) + 1))) *
    ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
      qParam ^ ((if η then 1 else -1) * ((r : ℤ) * k * ((s : ℤ) * k + 1))) *
        quantumInt (2 * (s : ℤ) * k + 1)

/-- The reduced sequence `F_N = ∑_{j<N} C_j(N) D_j` of the twisted satellite
(eq. (universalbailey)). -/
def twReduced (η : Bool) (r s : ℕ) (ℓ : ℤ) (N : ℕ) : RatFunc ℚ :=
  pairQReducedFormula (twInput η r s ℓ) N

/-- The even extension `n ↦ F_|n|` of the reduced sequence. -/
def twReducedEven (η : Bool) (r s : ℕ) (ℓ : ℤ) (n : ℤ) : RatFunc ℚ :=
  pairQReducedFormulaEven (twInput η r s ℓ) n

/-- The unreduced formula `[n] F_|n|` of the twisted satellite at every integer colour. -/
def twFormula (η : Bool) (r s : ℕ) (ℓ : ℤ) (n : ℤ) : RatFunc ℚ :=
  pairQFormula (twInput η r s ℓ) n

/-- The input `w_n^{(ℓ,c)} = q^(ℓ n(n+1)) (q^(c n) - q^(-c(n+1)))` of the Gaussian period
`G_c^{(ℓ)}` (Section 6.3). -/
def twPeriodInput (ℓ c : ℤ) (n : ℕ) : RatFunc ℚ :=
  qParam ^ (ℓ * n * ((n : ℤ) + 1)) * (qParam ^ (c * n) - qParam ^ (-(c * ((n : ℤ) + 1))))

/-- For the right-handed companion the input is `q^(ℓ n(n+1))` times the odd colours of
`T(r, s)`. -/
theorem twInput_true (r s : ℕ) (ℓ : ℤ) (n : ℕ) :
    twInput true r s ℓ n = qParam ^ (ℓ * n * ((n : ℤ) + 1)) * pairQOddColor r s n := by
  rw [twInput, pairQOddColor, ← mul_assoc, ← zpow_add₀ qParam_ne_zero, twIndex]
  congr 1
  · congr 1
    push_cast
    simp only [ite_true]
    ring
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [ite_true, one_mul]

/-- Without twist and for the right-handed companion the input is the library's. -/
theorem twInput_true_zero (r s : ℕ) : twInput true r s 0 = pairQOddColor r s := by
  funext n
  rw [twInput_true, zero_mul, zero_mul, zpow_zero, one_mul]

/-- Without twist and for the right-handed companion the formula is the library's formula of
the untwisted family. -/
theorem twFormula_true_zero (r s : ℕ) :
    twFormula true r s 0 = pairQFormula (pairQOddColor r s) := by
  funext n
  rw [twFormula, twInput_true_zero]

/-- `v_0 = 1`. -/
theorem twInput_zero (η : Bool) (r s : ℕ) (ℓ : ℤ) : twInput η r s ℓ 0 = 1 := by
  have h1 : quantumInt 1 = 1 := by
    rw [quantumInt, mul_one]
    exact div_self claspAlg_ratFuncX_sq_sub_ne_zero
  simp [twInput, h1]

/-- `F_1 = 1`. -/
theorem twReduced_one (η : Bool) (r s : ℕ) (ℓ : ℤ) : twReduced η r s ℓ 1 = 1 := by
  have hq : (1 : RatFunc ℚ) - qParam ≠ 0 := claspAlg_one_sub_qParam_ne_zero
  simp [twReduced, pairQReducedFormula, pairQCycloCoeff, cyclotomicKernel, qPochhammer,
    twInput_zero, hq]

/-- The unreduced formula is `[n] F_|n|`. -/
theorem twFormula_eq_quantumInt_mul (η : Bool) (r s : ℕ) (ℓ : ℤ) (n : ℤ) :
    twFormula η r s ℓ n = quantumInt n * twReducedEven η r s ℓ n :=
  pairQFormula_eq_quantumInt_mul _ n

end AJConjecture
