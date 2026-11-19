import Mathlib
import AJTwist.TwDefs
import AJTwist.Quantum.TwQHalfTwistZ
import AJTwist.Quantum.TwQBandRotSlide
import AJHandoff.TorusQuantum.PairQSatellite

/-!
# The band-and-clasp trace with signed twists and either clasp (Unit Q2)

`twSatTrace C k σ c` is the bracket of the band of two bundles of `c` strands following the
`2c`-cable of the closed braid `C`, with projectors on both bundles, `k` signed half twists and
the clasp of sign `σ`. For `k = -2w`, `σ = true` it is the library's `pairQSatTrace C w c`.

* `twSatTrace_eq_knotTrace_jwAt`: for an even number of half twists one projector on one edge
  suffices (as `pairQSatTrace_eq_knotTrace_jwAt`; the clasp enters through
  `jwAt_mul_claspSOp`, `claspSOp_mul_jwAt`).
* `twQ_knotTrace_jwAt_of_isBandClasp`: the interface `IsBandClasp K C (2κ) σ` of
  `AJTwist.TwDefs` gives the bracket of `K` coloured by `f_c` (as
  `pairQ_knotTrace_jwAt_of_longKnotOp`).
-/

noncomputable section

namespace AJConjecture

/-- The band-and-clasp trace over the companion `C` with `k` signed half twists and the clasp of
sign `σ`. -/
def twSatTrace (C : BraidKnot) (k : ℤ) (σ : Bool) (c : ℕ) : RatFunc ℚ :=
  knotTrace C (2 * c)
    (twoBundleProj c * halfTwistZ c k * claspSOp c σ * twoBundleProj c)

/-- For the negative clasp and `2w` negative half twists this is the library's trace. -/
theorem twSatTrace_neg_true (C : BraidKnot) (w c : ℕ) :
    twSatTrace C (-(2 * (w : ℤ))) true c = pairQSatTrace C w c := by
  have hH : halfTwistZ c (-(2 * (w : ℤ))) = halfTwist c false ^ (2 * w) := by
    rw [halfTwistZ]
    split_ifs with h0
    · obtain rfl : w = 0 := by omega
      rfl
    · congr 1
      omega
  rw [twSatTrace, pairQSatTrace, hH, claspSOp_true, bandClaspOp_eq_claspOp]

/-- In a monoid: if `p`, `q` are idempotents commuting with `E` and identified next to `T`, then
`p q E T p q = p E T p`. -/
private theorem mul_mul_mul_compress_twQSatTrace {M : Type*} [Monoid M] (p q E T : M)
    (hpE : p * E = E * p) (hqE : q * E = E * q) (hpT : p * T = q * T) (hTp : T * p = T * q)
    (hpp : p * p = p) (hqq : q * q = q) :
    p * q * E * T * (p * q) = p * E * T * p := by
  have hTpq : T * (p * q) = T * p := by rw [← mul_assoc, hTp, mul_assoc, hqq]
  have hqET : q * E * T = p * E * T := by
    rw [hqE, mul_assoc, ← hpT, ← mul_assoc, ← hpE]
  calc p * q * E * T * (p * q) = p * (q * E) * (T * (p * q)) := by simp only [mul_assoc]
    _ = p * (q * E * T) * p := by rw [hTpq]; simp only [mul_assoc]
    _ = p * p * E * T * p := by rw [hqET]; simp only [mul_assoc]
    _ = p * E * T * p := by rw [hpp]

/-- One projector on one edge of the band is enough. -/
theorem twSatTrace_eq_knotTrace_jwAt (C : BraidKnot) (κ : ℤ) (σ : Bool) (c : ℕ) :
    twSatTrace C (2 * κ) σ c =
      knotTrace C (2 * c) (jwAt (2 * c) 0 c * halfTwistZ c (2 * κ) * claspSOp c σ) := by
  have hop := mul_mul_mul_compress_twQSatTrace (jwAt (2 * c) 0 c) (jwAt (2 * c) c c)
    (halfTwistZ c (2 * κ)) (claspSOp c σ) (jwAt_fst_mul_halfTwistZ_two_mul c κ)
    (jwAt_snd_mul_halfTwistZ_two_mul c κ) (jwAt_mul_claspSOp c σ) (claspSOp_mul_jwAt c σ)
    (jwAt_mul_self _ _ _) (jwAt_mul_self _ _ _)
  rw [twSatTrace, twoBundleProj, hop, knotTrace_eq_qtr_longKnotOp,
    knotTrace_eq_qtr_longKnotOp,
    ← Matrix.mul_assoc (longKnotOp C (2 * c)) _ (jwAt (2 * c) 0 c),
    ← qtr_mul_comm_of_weight (2 * c) (2 * c) (jwAt (2 * c) 0 c) _ (skWeight_mul_jwAt _ _ _),
    ← Matrix.mul_assoc, ← (longKnotOp_commute_jwAt C (2 * c) 0 c).eq]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (jwAt (2 * c) 0 c) (jwAt (2 * c) 0 c), jwAt_mul_self]

/-- The band-and-clasp identity gives the coloured bracket of `K`. -/
theorem twQ_knotTrace_jwAt_of_isBandClasp {K C : BraidKnot} {κ : ℤ} {σ : Bool}
    (h : IsBandClasp K C (2 * κ) σ) (c : ℕ) :
    knotTrace K c (jwAt c 0 c) = twSatTrace C (2 * κ) σ c := by
  have hc : c ≤ 2 * c := by omega
  have hP : jwAt (2 * c) 0 c = skPlace (2 * c) (2 * c) 0 (jwAt c 0 c) :=
    jwAt_eq_skPlace (2 * c) 0 c (by omega)
  have hcomm : longKnotOp C (2 * c) * jwAt (2 * c) 0 c =
      jwAt (2 * c) 0 c * longKnotOp C (2 * c) :=
    (longKnotOp_commute_jwAt C (2 * c) 0 c).eq
  have hL : knotTrace K c (jwAt c 0 c) =
      qtr (2 * c) (longKnotOp C (2 * c) *
        (halfTwistZ c (2 * κ) * claspSOp c σ) * jwAt (2 * c) 0 c) := by
    rw [knotTrace_eq_qtr_longKnotOp, h c, ← ptrTail_mul_skPlace c (2 * c) hc, ← hP,
      ← qtr_eq_qtr_ptrTail c (2 * c) hc]
  have hR : twSatTrace C (2 * κ) σ c =
      qtr (2 * c) (jwAt (2 * c) 0 c *
        (longKnotOp C (2 * c) * (halfTwistZ c (2 * κ) * claspSOp c σ))) := by
    rw [twSatTrace_eq_knotTrace_jwAt, knotTrace_eq_qtr_longKnotOp,
      Matrix.mul_assoc (jwAt (2 * c) 0 c) (halfTwistZ c (2 * κ)) (claspSOp c σ),
      ← Matrix.mul_assoc (longKnotOp C (2 * c)) (jwAt (2 * c) 0 c), hcomm,
      Matrix.mul_assoc]
  rw [hL, hR]
  exact (qtr_mul_comm_of_weight (2 * c) (2 * c) (jwAt (2 * c) 0 c) _
    (skWeight_mul_jwAt (2 * c) 0 c)).symm

end AJConjecture
