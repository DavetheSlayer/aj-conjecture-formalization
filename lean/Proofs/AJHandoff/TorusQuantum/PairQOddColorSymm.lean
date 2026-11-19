import Mathlib
import AJHandoff.TorusQuantum.PairQOddColorRec

/-!
# Symmetry of the odd colours

`pairQOddColor r s = pairQOddColor s r` (source, after Q3): the forcing term is symmetric in
`(r, s)` (the two middle monomials exchange), so both sequences satisfy the same recurrence
`u_(n+1) = q^(-2rs(n+1)) u_n + h(n)` with `u_0 = 1`; induction on `n`. In particular the library's
odd colours of `T(2, a)` are `torusOddColor a = pairQOddColor a 2 = pairQOddColor 2 a`; the first
equality is a reindexing of the exponents (`r k (s k + 1) = a k (2k + 1)`, `2sk + 1 = 4k + 1`,
`rs = 2a`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The forcing term is symmetric in `(r, s)`. -/
theorem pairQForcing_comm (r s : ℕ) : pairQForcing r s = pairQForcing s r := by
  funext n
  rw [pairQForcing, pairQForcing, show (s : ℤ) + r - s * r = r + s - r * s by ring,
    show (s : ℤ) - r - s * r = s - r - r * s by ring,
    show (r : ℤ) - s - s * r = r - s - r * s by ring,
    show (s : ℤ) + r + s * r = r + s + r * s by ring]
  ring

/-- The odd extension agrees with the sequence at natural indices. -/
private theorem pairQOddExt_natCast_symm (u : ℕ → RatFunc ℚ) (n : ℕ) :
    pairQOddExt u (n : ℤ) = u n := by
  rw [pairQOddExt, ite_eq_left (Int.natCast_nonneg n), Int.toNat_natCast]

/-- The odd colours are symmetric in `(r, s)`. -/
theorem pairQOddColor_comm (r s : ℕ) : pairQOddColor r s = pairQOddColor s r := by
  funext n
  induction n with
  | zero => rw [pairQOddColor_zero, pairQOddColor_zero]
  | succ n ih =>
    have h1 := pairQOddColor_rec r s n
    have h2 := pairQOddColor_rec s r n
    rw [← Nat.cast_one, ← Nat.cast_add, pairQOddExt_natCast_symm,
      pairQOddExt_natCast_symm] at h1 h2
    rw [h1, h2, ih, pairQForcing_comm, mul_comm (r : ℤ)]

/-- The odd colours of `T(a, 2)` are the library's odd colours of `T(2, a)`. -/
theorem pairQOddColor_two_right (a : ℕ) : pairQOddColor a 2 = torusOddColor a := by
  funext n
  rw [pairQOddColor, torusOddColor, show -((a : ℤ) * ((2 : ℕ) : ℤ) * n * ((n : ℤ) + 1)) =
    -(2 * (a : ℤ) * n * ((n : ℤ) + 1)) by push_cast; ring]
  congr 1

end AJConjecture
