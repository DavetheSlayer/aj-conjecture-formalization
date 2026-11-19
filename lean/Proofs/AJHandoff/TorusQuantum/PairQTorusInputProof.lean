import Mathlib
import AJHandoff.TorusQuantum.PairQTorusInput
import AJHandoff.TorusInput.RJTorusInput

/-!
# The companion input for every torus pair (crux)

`pairQ_torusInput`: the coloured Jones function of `T(r, s)` at the odd colours is the source
formula Q1. This is the literature input of T-JONES (Rosso–Jones, Morton, Zheng (4.1)). The case
`r = 2` is also `pairQ_torusInput_two`. No downstream theorem of the package imports this file:
they take `PairQTorusInput r s h` as a hypothesis.

The proof is the short assembly below from the channel form
`rj_knotTrace_torusPair_jw` (`AJHandoff.TorusInput.RJTorusInput`): the coloured Jones polynomial
at the colour `2n + 1` is `θ_(2n)^(-writhe) knotTrace(T(r,s), 2n, f_(2n))`
(`laurentToField_coloredJonesPos`) and the writhe of `torusPairWord r s` is `(r - 1) s`
(`pairQ_writhe_torusPairWord`). The channel form is proved in `AJHandoff/TorusInput` by the
route of the design notes: fusion of unequal bundles, the spectral decomposition of the cabled
full twist, the Galois step `AJHandoff.TorusQuantum.PairQCruxGalois`, the isotopy
`closure(c) ∪ axis ≅ T(2, 2r)` and the Hopf functionals.
-/

noncomputable section

namespace AJConjecture

/-- Crux: the input formula holds for every admissible pair. -/
theorem pairQ_torusInput (r s : ℕ) (h : IsTorusPair r s) : PairQTorusInput r s h := by
  intro n
  have hθ : kinkScalar (2 * n) ≠ 0 := kinkScalar_ne_zero (2 * n)
  have hpos : (0 : ℤ) < 2 * (n : ℤ) + 1 := by omega
  have hnat : (2 * (n : ℤ) + 1).toNat - 1 = 2 * n := by omega
  rw [coloredJones, ite_eq_left hpos, hnat, laurentToField_coloredJonesPos]
  change (-1) ^ (2 * n) * kinkScalar (2 * n) ^ (-writhe (torusPairWord r s)) *
    knotTrace (torusPairKnot r s h) (2 * n) (jwAt (2 * n) 0 (2 * n)) = pairQOddColor r s n
  have hsign : (-1 : RatFunc ℚ) ^ (2 * n) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
  have hθw : kinkScalar (2 * n) ^ (((r - 1) * s : ℕ) : ℤ) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (((r - 1) * s : ℕ) : ℤ) * (n : ℤ) * ((n : ℤ) + 1)) := by
    rw [kinkScalar, zpow_natCast, mul_pow, hsign, one_pow, one_mul,
      ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [rj_knotTrace_torusPair_jw, pairQ_writhe_torusPairWord, hsign, one_mul, ← hθw, ← mul_assoc,
    ← zpow_add₀ hθ, neg_add_cancel, zpow_zero, one_mul]

end AJConjecture
