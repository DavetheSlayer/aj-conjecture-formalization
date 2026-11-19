import Mathlib
import AJConjecture.ComparisonDvdDescent
import AJConjecture.QAlgTwistFactorPrime
import AJFamily.Quantum.TwistPolyBasic

/-!
# Primality of `B_1` (TwF, unit F3)

Source: revision 5, Section 5.1 (`operators.tex`): "At `a = 1`,
`B_1 = x² L² - (x⁴ - x³ - 2x² - x + 1) L + x²`. Its discriminant is
`(x - 1)² (x + 1)² (x² - 3x + 1)(x² + x + 1)`. The last two factors have disjoint simple roots,
none zero, and remain square-free together after `x = M²`. Thus `B_1` is irreducible over `ℂ(M)`.
Its monic constant is `1`, whereas that of `E` is `x²`."

The library proves the primality of `B_m` for `m ≥ 2` (`prime_toComparison_twistPoly`, by the
degree argument); the case `m = 1` is a quadratic.

The explicit form `B_1 = M⁴ L² - (M⁸ - M⁶ - 2M⁴ - M² + 1) L + M⁴` is the library's
`twistPoly_one_eq_explicit` (`AJFamily/Quantum/TwistPolyBasic.lean`).

* `prime_toComparison_twistPoly_one`: `B_1` is prime in `ℚ(M)[L, L⁻¹]`.
* `not_toComparison_dvd_twistPoly_one`: neither `L - 1` nor `E` divides `B_1` there.

Route: over the field `ℚ(M)` a polynomial of degree `2` is irreducible iff it has no root
(`Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three`); a root `l` gives
`(2 M⁴ l - c)² = c² - 4 M⁸ = (M² - 1)² (M² + 1)² (M⁴ - 3M² + 1)(M⁴ + M² + 1)`, so
`(M⁴ - 3M² + 1)(M⁴ + M² + 1)` would be a square in `ℚ(M)`, hence in `ℚ[M]` (integrally closed),
but it is square-free of positive degree (e.g. `M² + M + 1` divides it exactly once). Then
`prime_toLaurent_of_prime` with the constant coefficient `M⁴ ≠ 0`. For the last statement:
`B_1(M, 1) = -(M⁴ - 3M² + 1)(M² + 1)² ≠ 0`, and `B_1`, `E` are non-associated primes of the same
degree (`E` is monic with constant `M⁴`, `B_1` has leading coefficient `M⁴` and constant `M⁴`:
`E = c B_1` would force `c = M⁻⁴` and `c = 1`).
Checked: factorisation and discriminant by computer algebra (scratch `check_blocks.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The image of `B_1` over `ℚ(M)` is an explicit quadratic. -/
private theorem map_twistPoly_one_twfOnePrime :
    (twistPoly 1).map
        ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))) =
      C (algebraMap ℚ[X] (RatFunc ℚ) (X ^ 4)) * X ^ 2 +
        C (algebraMap ℚ[X] (RatFunc ℚ) (-X ^ 8 + X ^ 6 + 2 * X ^ 4 + X ^ 2 - 1)) * X +
        C (algebraMap ℚ[X] (RatFunc ℚ) (X ^ 4)) := by
  rw [twistPoly_one_eq_explicit]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_sub,
    Polynomial.map_neg, Polynomial.map_one, Polynomial.map_ofNat]

/-- The discriminant of `B_1` is not a square in `ℚ(M)`: it is negative at `M = 3/2`. -/
private theorem sq_ne_discriminant_twfOnePrime (z : RatFunc ℚ) :
    z ^ 2 ≠ algebraMap ℚ[X] (RatFunc ℚ) (-X ^ 8 + X ^ 6 + 2 * X ^ 4 + X ^ 2 - 1) ^ 2 -
      4 * algebraMap ℚ[X] (RatFunc ℚ) (X ^ 4) ^ 2 := by
  intro hz
  rw [← map_pow, ← map_pow, ← map_ofNat (algebraMap ℚ[X] (RatFunc ℚ)) 4, ← map_mul,
    ← map_sub] at hz
  have hmonic : (X ^ 2 - C ((-X ^ 8 + X ^ 6 + 2 * X ^ 4 + X ^ 2 - 1) ^ 2 - 4 * (X ^ 4) ^ 2) :
      ℚ[X][X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hroot : aeval z (X ^ 2 -
      C ((-X ^ 8 + X ^ 6 + 2 * X ^ 4 + X ^ 2 - 1) ^ 2 - 4 * (X ^ 4) ^ 2) : ℚ[X][X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hz, sub_self]
  obtain ⟨z₀, rfl, -⟩ := exists_integer_of_is_root_of_monic hmonic hroot
  rw [← map_pow] at hz
  have h3 := congrArg (eval (3 / 2 : ℚ)) (IsFractionRing.injective ℚ[X] (RatFunc ℚ) hz)
  simp only [eval_pow, eval_sub, eval_add, eval_mul, eval_neg, eval_X, eval_ofNat,
    eval_one] at h3
  have h4 := sq_nonneg (z₀.eval (3 / 2 : ℚ))
  rw [h3] at h4
  norm_num at h4

/-- `B_1` is irreducible over `ℚ(M)`. -/
private theorem irreducible_map_twistPoly_one_twfOnePrime :
    Irreducible ((twistPoly 1).map
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)))) := by
  have ha : algebraMap ℚ[X] (RatFunc ℚ) (X ^ 4) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr (pow_ne_zero 4 X_ne_zero)
  rw [map_twistPoly_one_twfOnePrime, irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [natDegree_quadratic ha]) (by rw [natDegree_quadratic ha]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun l hl ↦ ?_
  have hroot := (mem_roots'.mp hl).2
  simp only [IsRoot, eval_add, eval_mul, eval_C, eval_pow, eval_X] at hroot
  refine sq_ne_discriminant_twfOnePrime (2 * algebraMap ℚ[X] (RatFunc ℚ) (X ^ 4) * l +
    algebraMap ℚ[X] (RatFunc ℚ) (-X ^ 8 + X ^ 6 + 2 * X ^ 4 + X ^ 2 - 1)) ?_
  linear_combination 4 * algebraMap ℚ[X] (RatFunc ℚ) (X ^ 4) * hroot

/-- The value of `L - 1` at `(M, L) = (0, 1)` is `0`, that of `B_1` is `-1`; the values at
`(2, 1)` of `E` and `B_1` are `16` and `-125`. -/
private theorem eval_eval_twistPoly_one_twfOnePrime :
    ((twistPoly 1).eval 1).eval 0 = -1 ∧ ((twistPoly 1).eval 1).eval 2 = -125 ∧
      (extraFactor.eval 1).eval 2 = 16 := by
  rw [twistPoly_one_eq_explicit, extraFactor]
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_neg, eval_one,
    eval_ofNat]
  norm_num

/-- `B_1` is prime in the comparison ring `ℚ(M)[L, L⁻¹]`. -/
theorem prime_toComparison_twistPoly_one : Prime (toComparison (twistPoly 1)) := by
  refine prime_toLaurent_of_prime irreducible_map_twistPoly_one_twfOnePrime.prime ?_
  rw [coe_mapRingHom, map_twistPoly_one_twfOnePrime]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C_zero]
  norm_num
  exact RatFunc.X_ne_zero

/-- In the comparison ring neither `L - 1` nor `E` divides `B_1`. -/
theorem not_toComparison_dvd_twistPoly_one :
    ¬ toComparison (X - 1) ∣ toComparison (twistPoly 1) ∧
      ¬ toComparison extraFactor ∣ toComparison (twistPoly 1) := by
  obtain ⟨h0, h2, hE⟩ := eval_eval_twistPoly_one_twfOnePrime
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show (X - 1 : ℤ[X][X]) = X - C 1 by rw [C_1]] at h
    have hdvd : (X - C 1 : ℤ[X][X]) ∣ twistPoly 1 := by
      rw [← Polynomial.map_dvd_map _ intPolyToRatFunc_injective (monic_X_sub_C 1)]
      refine dvd_of_toLaurent_dvd ?_ h
      simp
    have := map_dvd ((evalRingHom (0 : ℤ)).comp (evalRingHom (1 : ℤ[X]))) hdvd
    simp only [RingHom.comp_apply, coe_evalRingHom, eval_sub, eval_X, eval_C, sub_self,
      h0] at this
    norm_num at this
  · have := map_dvd ((evalRingHom (2 : ℤ)).comp (evalRingHom (1 : ℤ[X])))
      (extraFactor_dvd_of_toComparison_dvd h)
    simp only [RingHom.comp_apply, coe_evalRingHom, h2, hE] at this
    norm_num at this

end AJConjecture
