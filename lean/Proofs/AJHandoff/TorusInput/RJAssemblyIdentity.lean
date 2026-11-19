import Mathlib
import AJHandoff.TorusInput.RJDefs
import AJHandoff.TorusQuantum.PairQOddColorSymm

/-!
# The Rosso–Jones sum is the source formula Q1 (node RA6.2)

`∑_(i=-n)^n (t^(4ri²+4i)/θ_(2n))^s [2ri+1] = t^(4(r-1)s n(n+1)) u_n`, `u_n = pairQOddColor r s n`.

Route. `θ_(2n) = t^(4n(n+1)) = q^(n(n+1))`; the left side is
`t^(-4sn(n+1)) ∑_i q^(si(ri+1)) [2ri+1]`, which is
`t^(4(r-1)sn(n+1)) pairQOddColor s r n` term by term (`pairQOddColor`, `qParam`, `zpow_add₀`,
`ring_nf` on exponents); conclude with `pairQOddColor_comm`. Estimate 50–90 lines.
-/

noncomputable section

namespace AJConjecture

/-- The Rosso–Jones sum at even `b = 2n` is the source formula Q1 with its framing factor. -/
theorem rj_assembly_identity (r s n : ℕ) (hr : 1 ≤ r) :
    ∑ i ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        (RatFunc.X ^ (4 * (r : ℤ) * i ^ 2 + 4 * i) / kinkScalar (2 * n)) ^ s *
          quantumInt (2 * (r : ℤ) * i + 1) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (((r - 1) * s : ℕ) : ℤ) * (n : ℤ) * ((n : ℤ) + 1)) *
        pairQOddColor r s n := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hK : kinkScalar (2 * n) = (RatFunc.X : RatFunc ℚ) ^ (4 * (n : ℤ) * ((n : ℤ) + 1)) := by
    rw [kinkScalar, (even_two_mul n).neg_one_pow, one_mul]
    congr 1
    push_cast
    ring
  have hq : (qParam : RatFunc ℚ) = RatFunc.X ^ (4 : ℤ) := by
    rw [qParam]
    norm_cast
  rw [pairQOddColor_comm, pairQOddColor, ← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hK, hq, ← zpow_sub₀ hX, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← mul_assoc,
    ← zpow_add₀ hX, ← zpow_add₀ hX]
  congr 2
  push_cast [Nat.cast_sub hr]
  ring

end AJConjecture
