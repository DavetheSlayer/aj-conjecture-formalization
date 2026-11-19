import Mathlib
import AJHandoff.PairDefs
import AJHandoff.TorusQuantum.PairQJones

/-!
# The companion input for a torus pair (interface of the crux)

`PairQTorusInput r s h` is the statement that the coloured Jones function of the torus knot
`T(r, s) = torusPairKnot r s h`, as defined in `AJConjecture.ColoredJones` (Kauffman bracket of
Chebyshev cables of the closed braid, zero-framed by the writhe), takes at every odd colour
`2n + 1` the value `pairQOddColor r s n` of the source formula Q1 (Zheng, arXiv:math/0508138v4,
(4.1); equivalently the Rosso–Jones / Morton formula for torus knots at odd colours).

This is the only input about the companion that the quantum side of Theorem T uses. It is
proved for `r = 2` from the library (`AJHandoff.TorusQuantum.PairQTorusInputTwo`); for `r ≥ 3`
it is the crux node `pairQ_torusInput` (`AJHandoff.TorusQuantum.PairQTorusInputProof`). Every
downstream theorem takes it as an explicit hypothesis, so that the rest of Theorem T does not
depend on the crux.

Here it is converted into the channel form used by T-JONES (`pairQ_knotTrace_torusPair_of_input`;
the framing exponent is the writhe `(r - 1) s` of `torusPairWord r s`), and T-JONES is stated for
any braid knot `K` whose long-knot operator is the band-and-clasp partial trace over `T(r, s)`
with `2 (r - 1) s` negative half twists and whose writhe is `2 (r - 1) s - 2` (the identity that
the knot package P2 proves for `pairWhiteheadKnot r s h`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The writhe of the positive torus braid `(σ_0 ⋯ σ_(r-2))^s` is `(r - 1) s`. -/
theorem pairQ_writhe_torusPairWord (r s : ℕ) :
    writhe (torusPairWord r s) = (((r - 1) * s : ℕ) : ℤ) := by
  simp only [writhe, torusPairWord, List.map_flatten, List.map_replicate, List.sum_flatten,
    List.sum_replicate, List.map_map, Function.comp_def, ite_true, List.map_const',
    List.length_range]
  push_cast
  ring

/-- The input formula for the companion `T(r, s)`: its coloured Jones polynomial at every odd
colour `2n + 1` is the source formula Q1. (Literature: Morton 1995, Rosso–Jones 1993,
Zheng (4.1).) -/
def PairQTorusInput (r s : ℕ) (h : IsTorusPair r s) : Prop :=
  ∀ n : ℕ, laurentToField (coloredJones (torusPairKnot r s h) (2 * (n : ℤ) + 1)) =
    pairQOddColor r s n

/-- The input formula in channel form: the bracket of the `2n`-cable of `T(r, s)` with the
projector `f_{2n}` is `t^(4(r-1)s n(n+1)) u_n`. -/
theorem pairQ_knotTrace_torusPair_of_input {r s : ℕ} {h : IsTorusPair r s}
    (hT : PairQTorusInput r s h) (n : ℕ) :
    knotTrace (torusPairKnot r s h) (2 * n) (jwAt (2 * n) 0 (2 * n)) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (((r - 1) * s : ℕ) : ℤ) * (n : ℤ) * ((n : ℤ) + 1)) *
        pairQOddColor r s n := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hθ : kinkScalar (2 * n) ≠ 0 := kinkScalar_ne_zero (2 * n)
  have h0 := hT n
  have hpos : (0 : ℤ) < 2 * (n : ℤ) + 1 := by omega
  have hnat : (2 * (n : ℤ) + 1).toNat - 1 = 2 * n := by omega
  rw [coloredJones, ite_eq_left hpos, hnat, laurentToField_coloredJonesPos] at h0
  change (-1) ^ (2 * n) * kinkScalar (2 * n) ^ (-writhe (torusPairWord r s)) *
    knotTrace (torusPairKnot r s h) (2 * n) (jwAt (2 * n) 0 (2 * n)) = pairQOddColor r s n at h0
  have hsign : (-1 : RatFunc ℚ) ^ (2 * n) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
  rw [pairQ_writhe_torusPairWord, hsign, one_mul] at h0
  have hθw : kinkScalar (2 * n) ^ (((r - 1) * s : ℕ) : ℤ) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (((r - 1) * s : ℕ) : ℤ) * (n : ℤ) * ((n : ℤ) + 1)) := by
    rw [kinkScalar, zpow_natCast, mul_pow, hsign, one_pow, one_mul,
      ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [← h0, ← hθw, ← mul_assoc, ← zpow_add₀ hθ, add_neg_cancel, zpow_zero, one_mul]

/-- T-JONES for a torus pair, conditional on the input formula: a braid knot whose long-knot
operator is the band-and-clasp partial trace over `T(r, s)` with `2 (r - 1) s` negative half
twists, and whose writhe is `2 (r - 1) s - 2`, has the coloured Jones function
`pairQFormula (pairQOddColor r s)` at every integer colour. -/
theorem pairQ_coloredJones_of_longKnotOp_torusPair {r s : ℕ} {h : IsTorusPair r s}
    (hT : PairQTorusInput r s h) (K : BraidKnot)
    (hK : ∀ c : ℕ, longKnotOp K c =
      ptrTail c (2 * c) (longKnotOp (torusPairKnot r s h) (2 * c) *
        (halfTwist c false ^ (2 * ((r - 1) * s)) * claspOp c)))
    (hw : writhe K.word = 2 * (((r - 1) * s : ℕ) : ℤ) - 2) (n : ℤ) :
    laurentToField (coloredJones K n) = pairQFormula (pairQOddColor r s) n :=
  pairQ_laurentToField_coloredJones K (torusPairKnot r s h) ((r - 1) * s) (pairQOddColor r s)
    (pairQ_knotTrace_torusPair_of_input hT) hK hw n

end AJConjecture
