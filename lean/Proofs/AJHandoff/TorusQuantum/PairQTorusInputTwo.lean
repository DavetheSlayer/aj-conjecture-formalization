import Mathlib
import AJConjecture.SkeinLongKnotChannel
import AJConjecture.SkeinChebyshevProjector
import AJFamily.Skein.TorusTrace
import AJHandoff.TorusQuantum.PairQTorusInput
import AJHandoff.TorusQuantum.PairQOddColorSymm

/-!
# The companion input for `r = 2` (calibration)

`pairQ_torusInput_two`: for the pairs `(2, s)` the input formula holds, from the library. Since
`s` is odd, `torusPairWord 2 s = List.replicate s (0, true) = torusWord ((s - 1) / 2)`, so the
coloured Jones function of `torusPairKnot 2 s h` is that of `torusKnot ((s - 1) / 2)` (it depends
only on the strand number and the word). The library computes the bracket of its `2n`-cable with
`f_{2n}`: `qtr_longKnotOp_torusKnot_mul_channelIdem` with `m = 0` and
`qtr_longKnotOp_mul_channelIdem` give `t^(4s n(n+1)) torusOddColor s n`; the framing correction
`laurentToField_coloredJonesPos` with writhe `s` removes `t^(4s n(n+1))`; and
`torusOddColor s = pairQOddColor s 2 = pairQOddColor 2 s` (`PairQOddColorSymm`).

This shows that `PairQTorusInput` is consistent with the library's conventions (mirror,
framing, normalization) and is not vacuous.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- For odd `s = 2k + 1`, the knot `T(2, s)` of the pair package is the library's `torusKnot k`. -/
private theorem torusPairKnot_two_eq_torusKnot (k : ℕ) (h : IsTorusPair 2 (2 * k + 1)) :
    torusPairKnot 2 (2 * k + 1) h = torusKnot k := by
  have hw : torusPairWord 2 (2 * k + 1) = torusWord k := by
    simp only [torusPairWord, torusWord, Nat.add_one_sub_one, List.range_one, List.map_cons,
      List.map_nil, List.flatten_replicate_singleton]
  unfold torusPairKnot torusKnot
  congr 1

/-- The input formula holds for the pairs `(2, s)`. -/
theorem pairQ_torusInput_two (s : ℕ) (h : IsTorusPair 2 s) : PairQTorusInput 2 s h := by
  intro n
  obtain ⟨k, rfl⟩ : ∃ k, s = 2 * k + 1 := by
    obtain ⟨k, hk⟩ := Nat.coprime_two_left.mp h.2.2
    exact ⟨k, hk⟩
  have hθ : kinkScalar (2 * n) ≠ 0 := kinkScalar_ne_zero (2 * n)
  have hsign : (-1 : RatFunc ℚ) ^ (2 * n) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
  have htr : knotTrace (torusPairKnot 2 (2 * k + 1) h) (2 * n) (jwAt (2 * n) 0 (2 * n)) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1)) *
        torusOddColor (2 * k + 1) n := by
    rw [torusPairKnot_two_eq_torusKnot, ← qtr_longKnotOp_mul_channelIdem (torusKnot k) n 0,
      qtr_longKnotOp_torusKnot_mul_channelIdem]
  have hθw : kinkScalar (2 * n) ^ (((2 - 1) * (2 * k + 1) : ℕ) : ℤ) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1)) := by
    rw [kinkScalar, zpow_natCast, mul_pow, hsign, one_pow, one_mul, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  have hpos : (0 : ℤ) < 2 * (n : ℤ) + 1 := by omega
  have hnat : (2 * (n : ℤ) + 1).toNat - 1 = 2 * n := by omega
  rw [coloredJones, ite_eq_left hpos, hnat, laurentToField_coloredJonesPos]
  change (-1) ^ (2 * n) * kinkScalar (2 * n) ^ (-writhe (torusPairWord 2 (2 * k + 1))) *
    knotTrace (torusPairKnot 2 (2 * k + 1) h) (2 * n) (jwAt (2 * n) 0 (2 * n)) = _
  rw [pairQ_writhe_torusPairWord, hsign, one_mul, htr, ← hθw, ← mul_assoc, ← zpow_add₀ hθ,
    neg_add_cancel, zpow_zero, one_mul, pairQOddColor_comm, pairQOddColor_two_right]

end AJConjecture
