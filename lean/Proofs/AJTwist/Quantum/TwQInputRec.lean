import Mathlib
import AJTwist.Quantum.TwQInputBar
import AJHandoff.TorusQuantum.PairQOddColorRec

/-!
# The first-order recurrence of the twisted input (Unit Q4)

Source: revision 5, Section 3.2, eq. (twistedinner):
`v_(n+1) = q^(-2a) Q^(-2a) v_n + g(n+1) H_η(q, Q)`, `g(n) = q^(ℓ n(n+1))`, `Q = q^n`, extended to
all integers by `v_(-n-1) = -v_n` (with `g(-n-1) = g(n)`, `H_η(q, q⁻¹) = 2`).

`twForcing η r s ℓ n = g(n+1) H_η(q, q^n)`, where `H_+(q, q^n)` is the library's
`pairQForcing r s n` and `H_-` is its bar. `twInput_rec` follows from the library's
`pairQOddColor_rec` (the untwisted right-handed case) by multiplying with `g`, which is
invariant under `n ↦ -n-1` and satisfies `g(n+1) = q^(2ℓ(n+1)) g(n)`, and, for the mirror
companion, by applying the bar involution (`twInput_true`, `twInput_false`).

Checked at random points on `-6 ≤ n ≤ 5` for 60 choices of `(η, r, s, ℓ)` (scratch
`check_inner.py`, `check_misc.py`, column `recurrence`); the identity does not use coprimality
or `r < s`.
-/

noncomputable section

namespace AJConjecture

/-- The forcing `g(n+1) H_η(q, q^n)` of the first-order recurrence of the twisted input. -/
def twForcing (η : Bool) (r s : ℕ) (ℓ : ℤ) (n : ℤ) : RatFunc ℚ :=
  qParam ^ (ℓ * (n + 1) * (n + 2)) *
    (if η then pairQForcing r s n else twQBar (pairQForcing r s n))

/-- The odd extension of the twisted input is `g` times that of the (barred) torus input. -/
theorem pairQOddExt_twInput (η : Bool) (r s : ℕ) (ℓ : ℤ) (n : ℤ) :
    pairQOddExt (twInput η r s ℓ) n =
      qParam ^ (ℓ * n * (n + 1)) *
        (if η then pairQOddExt (pairQOddColor r s) n
          else twQBar (pairQOddExt (pairQOddColor r s) n)) := by
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [pairQOddExt, pairQOddExt, ite_eq_left hn, Int.toNat_natCast]
    cases η
    · simp only [Bool.false_eq_true, ite_false]
      exact twInput_false r s ℓ p
    · simp only [ite_true]
      exact twInput_true r s ℓ p
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    have hp : (-(-(p : ℤ) - 1) - 1).toNat = p := by omega
    have he : ℓ * (-(p : ℤ) - 1) * (-(p : ℤ) - 1 + 1) = ℓ * p * ((p : ℤ) + 1) := by ring
    have hneg : ¬(0 : ℤ) ≤ -(p : ℤ) - 1 := by omega
    simp only [pairQOddExt, ite_eq_right hneg, hp, he]
    cases η
    · simp only [Bool.false_eq_true, ite_false]
      rw [twInput_false, map_neg, mul_neg]
    · simp only [ite_true]
      rw [twInput_true, mul_neg]

/-- The recurrence (twistedinner) of the twisted input at every integer. -/
theorem twInput_rec (η : Bool) (r s : ℕ) (ℓ : ℤ) (n : ℤ) :
    pairQOddExt (twInput η r s ℓ) (n + 1) =
      qParam ^ (-(2 * twIndex η r s ℓ * (n + 1))) * pairQOddExt (twInput η r s ℓ) n +
        twForcing η r s ℓ n := by
  have hq := qParam_ne_zero
  have hrec := pairQOddColor_rec r s n
  rw [pairQOddExt_twInput, pairQOddExt_twInput, twForcing, twIndex,
    show n + 1 + 1 = n + 2 by ring]
  cases η
  · have e : qParam ^ (ℓ * (n + 1) * (n + 2)) * qParam ^ (-(-(2 * ((r : ℤ) * s) * (n + 1)))) =
        qParam ^ (-(2 * (-((r * s : ℕ) : ℤ) - ℓ) * (n + 1))) * qParam ^ (ℓ * n * (n + 1)) := by
      rw [← zpow_add₀ hq, ← zpow_add₀ hq]
      congr 1
      push_cast
      ring
    simp only [Bool.false_eq_true, ite_false]
    rw [hrec, map_add, map_mul, twQBar_qParam_zpow]
    linear_combination twQBar (pairQOddExt (pairQOddColor r s) n) * e
  · have e : qParam ^ (ℓ * (n + 1) * (n + 2)) * qParam ^ (-(2 * ((r : ℤ) * s) * (n + 1))) =
        qParam ^ (-(2 * (((r * s : ℕ) : ℤ) - ℓ) * (n + 1))) * qParam ^ (ℓ * n * (n + 1)) := by
      rw [← zpow_add₀ hq, ← zpow_add₀ hq]
      congr 1
      push_cast
      ring
    simp only [ite_true]
    rw [hrec]
    linear_combination pairQOddExt (pairQOddColor r s) n * e

end AJConjecture
