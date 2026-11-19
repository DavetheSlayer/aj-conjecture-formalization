import Mathlib
import AJConjecture.SkeinKnotTraceJwStep
import AJConjecture.SkeinBandClaspCompress
import AJConjecture.SkeinSatelliteEval
import AJFamily.Skein.TorusFramingScalar
import AJFamily.Skein.TorusSatellite
import AJFamily.Skein.TorusTrace
import AJFamily.Skein.TorusWhiteheadSum

/-!
# Evaluation of the satellite bracket

`torusSatelliteTrace_eq`: the satellite bracket is `(-1)^c θ_c^(4k) [c+1] F_{c+1}`. The operator of
the band is diagonal on the channels of the two bundles; each channel contributes the trace of
`T(2, 2k+1)` on it (`qtr_longKnotOp_torusKnot_mul_channelIdem`) times a clasp eigenvalue and a
framing scalar, and the sum is evaluated by `claspAlg_sum_claspEigen_mul_torusOddColor`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The trace of the long knot of `T(2, 2k+1)` on the channel `Q_n`, for `n ≤ c`. -/
private theorem qtr_longKnotOp_torusKnot_mul_channelIdem_of_le (k c n : ℕ) (hn : n ≤ c) :
    qtr (2 * c) (longKnotOp (torusKnot k) (2 * c) * channelIdem c n) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1)) *
        torusOddColor (2 * k + 1) n := by
  obtain ⟨m, rfl⟩ : ∃ m, c = n + m := ⟨c - n, by omega⟩
  exact qtr_longKnotOp_torusKnot_mul_channelIdem k n m

/-- The operator of the torus satellite trace on the channels. -/
private theorem torusSatelliteOp_eq_sum_channelIdem (k c : ℕ) :
    twoBundleProj c * halfTwist c false ^ (2 * (2 * k + 1)) * bandClaspOp c * twoBundleProj c =
      ∑ n ∈ Finset.range (c + 1),
        (claspAlgClaspEigen c n * ((claspAlgHalfTwistEigen c n)⁻¹) ^ (2 * (2 * k + 1))) •
          channelIdem c n := by
  have hcomm : Commute (halfTwist c false ^ (2 * (2 * k + 1))) (twoBundleProj c) :=
    (show Commute (halfTwist c false) (twoBundleProj c) from
      halfTwist_mul_twoBundleProj c false).pow_left _
  rw [← hcomm.eq, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (twoBundleProj c),
    twoBundleProj_mul_bandClaspOp_mul_twoBundleProj_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Matrix.mul_smul, halfTwist_false_pow_mul_channelIdem c n _
    (by have := Finset.mem_range.mp hn; omega), smul_smul]

/-- `(-1)^c θ_c^(4k) (-1)^c t^(2c(c+2)) = t^(2(2k+1)c(c+2))`. -/
private theorem kinkScalar_pow_four_mul_torusSatelliteEval (k c : ℕ) :
    (-1 : RatFunc ℚ) ^ c * kinkScalar c ^ (4 * k) *
        ((-1) ^ c * (RatFunc.X : RatFunc ℚ) ^ (2 * (c : ℤ) * ((c : ℤ) + 2))) =
      (RatFunc.X : RatFunc ℚ) ^ (2 * (2 * (k : ℤ) + 1) * (c : ℤ) * ((c : ℤ) + 2)) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h1 : ((-1 : RatFunc ℚ) ^ c) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have h4 : ((-1 : RatFunc ℚ) ^ c) ^ (4 * k) = 1 := by
    rw [show 4 * k = 2 * (2 * k) by ring, pow_mul, h1, one_pow]
  have e : (RatFunc.X : RatFunc ℚ) ^ (2 * (2 * (k : ℤ) + 1) * (c : ℤ) * ((c : ℤ) + 2)) =
      ((RatFunc.X : RatFunc ℚ) ^ ((c : ℤ) * ((c : ℤ) + 2))) ^ (4 * k) *
        (RatFunc.X : RatFunc ℚ) ^ (2 * (c : ℤ) * ((c : ℤ) + 2)) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hX]
    congr 1
    push_cast
    ring
  rw [e, kinkScalar, mul_pow, h4]
  linear_combination (((RatFunc.X : RatFunc ℚ) ^ ((c : ℤ) * ((c : ℤ) + 2))) ^ (4 * k) *
    (RatFunc.X : RatFunc ℚ) ^ (2 * (c : ℤ) * ((c : ℤ) + 2))) * h1

/-- The torus satellite trace as a sum over the channels. -/
private theorem torusSatelliteTrace_eq_sum (k c : ℕ) :
    torusSatelliteTrace k c =
      ∑ n ∈ Finset.range (c + 1), claspAlgClaspEigen c n *
        (((claspAlgHalfTwistEigen c n)⁻¹) ^ (2 * (2 * k + 1)) *
          ((RatFunc.X : RatFunc ℚ) ^ (4 * (2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1)) *
            torusOddColor (2 * k + 1) n)) := by
  rw [torusSatelliteTrace, knotTrace_eq_qtr_longKnotOp, torusSatelliteOp_eq_sum_channelIdem,
    Finset.mul_sum, qtr_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Matrix.mul_smul, qtr_smul, qtr_longKnotOp_torusKnot_mul_channelIdem_of_le
    k c n (by have := Finset.mem_range.mp hn; omega), mul_assoc]

/-- The bracket of the band-and-clasp diagram of `Wh⁻₀(T(2, 2k+1))` is
`(-1)^c θ_c^(4k) [c+1] F_{c+1}`. -/
theorem torusSatelliteTrace_eq (k c : ℕ) :
    torusSatelliteTrace k c =
      (-1) ^ c * kinkScalar c ^ (4 * k) * torusWhiteheadFormula (2 * k + 1) ((c : ℤ) + 1) := by
  rw [torusSatelliteTrace_eq_sum, ← claspAlg_sum_claspEigen_mul_torusOddColor, ← mul_assoc,
    kinkScalar_pow_four_mul_torusSatelliteEval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [← mul_assoc (_ ^ (2 * (2 * k + 1))), halfTwistEigen_inv_pow_mul_torus]
  ring

end AJConjecture
