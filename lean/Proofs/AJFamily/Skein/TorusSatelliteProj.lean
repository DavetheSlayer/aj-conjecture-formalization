import Mathlib
import AJConjecture.SkeinHalfTwistCap
import AJConjecture.SkeinBandRotProj
import AJConjecture.SkeinLongKnotJw
import AJFamily.Skein.TorusSatellite

/-!
# One projector suffices

`torusSatelliteTrace_eq_knotTrace_jwAt`: in `torusSatelliteTrace` the projectors `f ⊗ f` on both
ends of the band may be replaced by a single projector `f_c` on the first bundle.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- In a monoid: if `p`, `q` are idempotents exchanged by `H` and identified next to `T`, then
`p q H^(2a) T p q = p H^(2a) T p`. -/
private theorem mul_pow_two_mul_mul_compress_torusSatelliteProj {M : Type*} [Monoid M]
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

/-- The torus satellite trace with one projector on one edge of the band. -/
theorem torusSatelliteTrace_eq_knotTrace_jwAt (k c : ℕ) :
    torusSatelliteTrace k c =
      knotTrace (torusKnot k) (2 * c)
        (jwAt (2 * c) 0 c * halfTwist c false ^ (2 * (2 * k + 1)) * bandClaspOp c) := by
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
  have hop := mul_pow_two_mul_mul_compress_torusSatelliteProj (jwAt (2 * c) 0 c)
    (jwAt (2 * c) c c) (halfTwist c false) (bandClaspOp c) (2 * k + 1) hpH hqH
    (jwAt_mul_bandClaspOp c) (bandClaspOp_mul_jwAt c) (jwAt_mul_self _ _ _) (jwAt_mul_self _ _ _)
  rw [torusSatelliteTrace, twoBundleProj, hop, knotTrace_eq_qtr_longKnotOp,
    knotTrace_eq_qtr_longKnotOp,
    ← Matrix.mul_assoc (longKnotOp (torusKnot k) (2 * c)) _ (jwAt (2 * c) 0 c),
    ← qtr_mul_comm_of_weight (2 * c) (2 * c) (jwAt (2 * c) 0 c) _ (skWeight_mul_jwAt _ _ _),
    ← Matrix.mul_assoc, ← (longKnotOp_commute_jwAt (torusKnot k) (2 * c) 0 c).eq]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (jwAt (2 * c) 0 c) (jwAt (2 * c) 0 c), jwAt_mul_self]

end AJConjecture
