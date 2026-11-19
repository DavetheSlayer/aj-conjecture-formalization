import Mathlib
import AJConjecture.SkeinBandClaspBridge
import AJConjecture.SkeinHalfTwistCap
import AJConjecture.SkeinBandRotProj
import AJConjecture.SkeinLongKnotJw
import AJFamily.Skein.TorusSatellite

/-!
# The band-and-clasp trace over an arbitrary companion

`pairQSatTrace C w c` is the bracket of the band of two bundles of `c` strands following the
`2c`-cable of the closed braid `C`, with projectors on both bundles, `2w` negative half twists
and the clasp: the satellite diagram of the untwisted Whitehead double of `C` when `w` is the
writhe of `C`. For `C = torusKnot k` and `w = 2k + 1` it is `torusSatelliteTrace k c`.

* `pairQSatTrace_eq_knotTrace_jwAt`: one projector on one edge suffices (the library's
  `torusSatelliteTrace_eq_knotTrace_jwAt`; its proof uses only that the exponent is even).
* `pairQ_knotTrace_jwAt_of_longKnotOp`: if the long-knot operator of a braid knot `K` is the
  partial trace of the band-and-clasp operator over `C`, the bracket of `K` coloured by `f_c` is
  `pairQSatTrace C w c` (the library's `knotTrace_jwAt_of_longKnotOp_torus`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The band-and-clasp trace over the companion `C` with `2w` negative half twists. -/
def pairQSatTrace (C : BraidKnot) (w c : ℕ) : RatFunc ℚ :=
  knotTrace C (2 * c)
    (twoBundleProj c * halfTwist c false ^ (2 * w) * bandClaspOp c * twoBundleProj c)

theorem pairQSatTrace_torus (k c : ℕ) :
    pairQSatTrace (torusKnot k) (2 * k + 1) c = torusSatelliteTrace k c := rfl

/-- In a monoid: if `p`, `q` are idempotents exchanged by `H` and identified next to `T`, then
`p q H^(2a) T p q = p H^(2a) T p`. -/
private theorem mul_pow_two_mul_mul_compress_pairQSat {M : Type*} [Monoid M]
    (p q H T : M) (a : ℕ)
    (hpH : p * H = H * q) (hqH : q * H = H * p) (hpT : p * T = q * T) (hTp : T * p = T * q)
    (hpp : p * p = p) (hqq : q * q = q) :
    p * q * H ^ (2 * a) * T * (p * q) = p * H ^ (2 * a) * T * p := by
  have hp2 : Commute p (H ^ 2) := by
    show p * H ^ 2 = H ^ 2 * p
    rw [pow_two, ← mul_assoc, hpH, mul_assoc, hqH, mul_assoc]
  have hq2 : Commute q (H ^ 2) := by
    show q * H ^ 2 = H ^ 2 * q
    rw [pow_two, ← mul_assoc, hqH, mul_assoc, hpH, mul_assoc]
  have hp6 : p * H ^ (2 * a) = H ^ (2 * a) * p := by
    rw [pow_mul]
    exact (hp2.pow_right a).eq
  have hq6 : q * H ^ (2 * a) = H ^ (2 * a) * q := by
    rw [pow_mul]
    exact (hq2.pow_right a).eq
  have hTpq : T * (p * q) = T * p := by rw [← mul_assoc, hTp, mul_assoc, hqq]
  have hq6T : q * H ^ (2 * a) * T = p * H ^ (2 * a) * T := by
    rw [hq6, mul_assoc, ← hpT, ← mul_assoc, ← hp6]
  calc p * q * H ^ (2 * a) * T * (p * q) = p * (q * H ^ (2 * a)) * (T * (p * q)) := by
        simp only [mul_assoc]
    _ = p * (q * H ^ (2 * a) * T) * p := by rw [hTpq]; simp only [mul_assoc]
    _ = p * p * H ^ (2 * a) * T * p := by rw [hq6T]; simp only [mul_assoc]
    _ = p * H ^ (2 * a) * T * p := by rw [hpp]

/-- One projector on one edge of the band is enough. -/
theorem pairQSatTrace_eq_knotTrace_jwAt (C : BraidKnot) (w c : ℕ) :
    pairQSatTrace C w c =
      knotTrace C (2 * c) (jwAt (2 * c) 0 c * halfTwist c false ^ (2 * w) * bandClaspOp c) := by
  have hpH : jwAt (2 * c) 0 c * halfTwist c false = halfTwist c false * jwAt (2 * c) c c := by
    have h1 := jwAt_mul_braidMatrix_thickCross_fst (2 * c) c c 0 false (by omega)
    rw [Nat.zero_add] at h1
    rw [halfTwist_eq_braidMatrix_thickCross]
    exact h1
  have hqH : jwAt (2 * c) c c * halfTwist c false = halfTwist c false * jwAt (2 * c) 0 c := by
    have h2 := jwAt_mul_braidMatrix_thickCross_snd (2 * c) c c 0 false (by omega)
    rw [Nat.zero_add] at h2
    rw [halfTwist_eq_braidMatrix_thickCross]
    exact h2
  have hop := mul_pow_two_mul_mul_compress_pairQSat (jwAt (2 * c) 0 c)
    (jwAt (2 * c) c c) (halfTwist c false) (bandClaspOp c) w hpH hqH
    (jwAt_mul_bandClaspOp c) (bandClaspOp_mul_jwAt c) (jwAt_mul_self _ _ _) (jwAt_mul_self _ _ _)
  rw [pairQSatTrace, twoBundleProj, hop, knotTrace_eq_qtr_longKnotOp,
    knotTrace_eq_qtr_longKnotOp,
    ← Matrix.mul_assoc (longKnotOp C (2 * c)) _ (jwAt (2 * c) 0 c),
    ← qtr_mul_comm_of_weight (2 * c) (2 * c) (jwAt (2 * c) 0 c) _ (skWeight_mul_jwAt _ _ _),
    ← Matrix.mul_assoc, ← (longKnotOp_commute_jwAt C (2 * c) 0 c).eq]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (jwAt (2 * c) 0 c) (jwAt (2 * c) 0 c), jwAt_mul_self]

/-- The operator form of the satellite identity gives the coloured bracket of `K`. -/
theorem pairQ_knotTrace_jwAt_of_longKnotOp (K C : BraidKnot) (w c : ℕ)
    (h : longKnotOp K c =
      ptrTail c (2 * c) (longKnotOp C (2 * c) * (halfTwist c false ^ (2 * w) * claspOp c))) :
    knotTrace K c (jwAt c 0 c) = pairQSatTrace C w c := by
  have hc : c ≤ 2 * c := by omega
  have hP : jwAt (2 * c) 0 c = skPlace (2 * c) (2 * c) 0 (jwAt c 0 c) :=
    jwAt_eq_skPlace (2 * c) 0 c (by omega)
  have hcomm : longKnotOp C (2 * c) * jwAt (2 * c) 0 c =
      jwAt (2 * c) 0 c * longKnotOp C (2 * c) :=
    (longKnotOp_commute_jwAt C (2 * c) 0 c).eq
  have hL : knotTrace K c (jwAt c 0 c) =
      qtr (2 * c) (longKnotOp C (2 * c) *
        (halfTwist c false ^ (2 * w) * claspOp c) * jwAt (2 * c) 0 c) := by
    rw [knotTrace_eq_qtr_longKnotOp, h, ← ptrTail_mul_skPlace c (2 * c) hc, ← hP,
      ← qtr_eq_qtr_ptrTail c (2 * c) hc]
  have hR : pairQSatTrace C w c =
      qtr (2 * c) (jwAt (2 * c) 0 c *
        (longKnotOp C (2 * c) * (halfTwist c false ^ (2 * w) * claspOp c))) := by
    rw [pairQSatTrace_eq_knotTrace_jwAt, knotTrace_eq_qtr_longKnotOp,
      bandClaspOp_eq_claspOp,
      Matrix.mul_assoc (jwAt (2 * c) 0 c) (halfTwist c false ^ (2 * w)) (claspOp c),
      ← Matrix.mul_assoc (longKnotOp C (2 * c)) (jwAt (2 * c) 0 c), hcomm,
      Matrix.mul_assoc]
  rw [hL, hR]
  exact (qtr_mul_comm_of_weight (2 * c) (2 * c) (jwAt (2 * c) 0 c) _
    (skWeight_mul_jwAt (2 * c) 0 c)).symm

end AJConjecture
