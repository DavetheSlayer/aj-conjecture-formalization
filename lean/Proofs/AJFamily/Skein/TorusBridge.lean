import Mathlib
import AJConjecture.SkeinBandClaspBridge
import AJFamily.Skein.TorusSatelliteProj

/-!
# From the operator identity to knot traces

If the long-knot operator of a braid knot `K` equals the partial trace of the band-and-clasp
operator built on `T(2, 2k+1)`, then the bracket of `K` coloured by the projector `f_c` is
`torusSatelliteTrace k c`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The operator form of the isotopy lemma for a torus-knot companion gives its form with knot
traces. -/
theorem knotTrace_jwAt_of_longKnotOp_torus (K : BraidKnot) (k c : ℕ)
    (h : longKnotOp K c =
      ptrTail c (2 * c)
        (longKnotOp (torusKnot k) (2 * c) * (halfTwist c false ^ (2 * (2 * k + 1)) * claspOp c))) :
    knotTrace K c (jwAt c 0 c) = torusSatelliteTrace k c := by
  have hc : c ≤ 2 * c := by omega
  have hP : jwAt (2 * c) 0 c = skPlace (2 * c) (2 * c) 0 (jwAt c 0 c) :=
    jwAt_eq_skPlace (2 * c) 0 c (by omega)
  have hcomm : longKnotOp (torusKnot k) (2 * c) * jwAt (2 * c) 0 c =
      jwAt (2 * c) 0 c * longKnotOp (torusKnot k) (2 * c) :=
    (longKnotOp_commute_jwAt (torusKnot k) (2 * c) 0 c).eq
  have hL : knotTrace K c (jwAt c 0 c) =
      qtr (2 * c) (longKnotOp (torusKnot k) (2 * c) *
        (halfTwist c false ^ (2 * (2 * k + 1)) * claspOp c) * jwAt (2 * c) 0 c) := by
    rw [knotTrace_eq_qtr_longKnotOp, h, ← ptrTail_mul_skPlace c (2 * c) hc, ← hP,
      ← qtr_eq_qtr_ptrTail c (2 * c) hc]
  have hR : torusSatelliteTrace k c =
      qtr (2 * c) (jwAt (2 * c) 0 c *
        (longKnotOp (torusKnot k) (2 * c) *
          (halfTwist c false ^ (2 * (2 * k + 1)) * claspOp c))) := by
    rw [torusSatelliteTrace_eq_knotTrace_jwAt, knotTrace_eq_qtr_longKnotOp,
      bandClaspOp_eq_claspOp,
      Matrix.mul_assoc (jwAt (2 * c) 0 c) (halfTwist c false ^ (2 * (2 * k + 1))) (claspOp c),
      ← Matrix.mul_assoc (longKnotOp (torusKnot k) (2 * c)) (jwAt (2 * c) 0 c), hcomm,
      Matrix.mul_assoc]
  rw [hL, hR]
  exact (qtr_mul_comm_of_weight (2 * c) (2 * c) (jwAt (2 * c) 0 c) _
    (skWeight_mul_jwAt (2 * c) 0 c)).symm

end AJConjecture
