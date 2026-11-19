import Mathlib
import AJHandoff.TorusInput.RJDefs

/-!
# The embedding `t ↦ t^r` (node RA4.0)

`rjEmbed r X = X^r` (`r ≥ 1`), `rjEmbed r` is injective, maps `X^e` to `X^(re)`, and
`ν_N^r = rjEmbed r μ_N` for even `b`, `N`; `ν_N ≠ 0`.

Route. `RatFunc.mapRingHom` applied to `algebraMap ℚ[X] ℚ(t) p` is `algebraMap (expand p)`
(`RatFunc.map_apply_ofFractionRing_mk` or `RatFunc.mapRingHom_algebraMap`-type lemmas;
`Polynomial.expand_X`); a ring homomorphism out of a field is injective
(`RingHom.injective`); `kinkScalar N = t^(N(N+2))` for even `N` (`Even.neg_one_pow`).
Estimate 60–100 lines.
-/

noncomputable section

namespace AJConjecture

/-- `rjEmbed r` sends `t` to `t^r`. -/
theorem rjEmbed_X (r : ℕ) (hr : 1 ≤ r) : rjEmbed r RatFunc.X = RatFunc.X ^ r := by
  have h : (RatFunc.X : RatFunc ℚ) =
      algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X /
        algebraMap (Polynomial ℚ) (RatFunc ℚ) 1 := by
    rw [map_one, div_one, RatFunc.algebraMap_X]
  rw [h, rjEmbed, RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply_div, Polynomial.expand_X,
    map_one, map_one, div_one, map_pow, RatFunc.algebraMap_X, max_eq_left hr, div_one]

/-- `rjEmbed r` is injective. -/
theorem rjEmbed_injective (r : ℕ) : Function.Injective (rjEmbed r) :=
  (rjEmbed r).injective

/-- `rjEmbed r` on integer powers of `t`. -/
theorem rjEmbed_zpow_X (r : ℕ) (hr : 1 ≤ r) (e : ℤ) :
    rjEmbed r (RatFunc.X ^ e) = RatFunc.X ^ ((r : ℤ) * e) := by
  rw [map_zpow₀, rjEmbed_X r hr, ← zpow_natCast, ← zpow_mul]

set_option linter.unusedVariables false in
/-- `ν_N` is an `r`-th root of `μ_N` for even `b` and `N`. -/
theorem rjNu_pow (b r N : ℕ) (hr : 1 ≤ r) (hb : Even b) (hN : Even N) :
    rjNu b r N ^ r = rjEmbed r (rjTwistEigen b r N) := by
  rw [rjNu, rjTwistEigen, map_div₀, map_pow, div_pow, kinkScalar.eq_def N, hN.neg_one_pow,
    one_mul, rjEmbed_zpow_X r hr, ← pow_mul, ← zpow_natCast]
  congr 2
  push_cast
  ring

/-- `ν_N ≠ 0`. -/
theorem rjNu_ne_zero (b r N : ℕ) : rjNu b r N ≠ 0 := by
  have hk : kinkScalar b ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (zpow_ne_zero _ RatFunc.X_ne_zero)
  exact div_ne_zero (pow_ne_zero _ RatFunc.X_ne_zero) ((map_ne_zero (rjEmbed r)).mpr hk)

end AJConjecture
