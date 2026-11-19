import Mathlib
import AJConjecture.SkeinBandRotBasic
import AJConjecture.SkeinBandRotTurnback
import AJConjecture.SkeinCabledSkein

/-!
# The compressed clasp in the turnback basis and on the channels

`(f ⊗ f) T_c (f ⊗ f) = ∑_k s_k D_{c-k} = ∑_n ξ_{c,n} Q_n`, with `s_k` the coefficients of the
cabled full
twist (`AJConjecture.claspAlgFullTwistCoeff`) and `ξ_{c,n} = ∑_k s_k d_{c-k,n}` the clasp
eigenvalues
(`AJConjecture.claspAlgClaspEigen`). The clasp is the rotation of `Σ_c²`; the compression commutes
with the rotation (`AJConjecture.twoBundleProj_mul_bandRot_mul_twoBundleProj`), `Σ_c²` commutes with
`f ⊗ f` (`AJConjecture.halfTwist_mul_twoBundleProj`), `Σ_c² (f ⊗ f) = ∑_k s_k D_k`
(`AJConjecture.halfTwist_sq_mul_twoBundleProj_eq_sum_turnback`), the rotation is linear
(`AJConjecture.bandRot_sum`, `AJConjecture.bandRot_smul`) and exchanges `D_k` and `D_{c-k}`
(`AJConjecture.bandRot_turnback`). The second form is the first one with
`D_{c-k} = ∑_n d_{c-k,n} Q_n` (`AJConjecture.turnback_eq_sum`) and the two sums exchanged.
-/

namespace AJConjecture

/-- The compressed clasp in the turnback basis. -/
theorem twoBundleProj_mul_bandClaspOp_mul_twoBundleProj (c : ℕ) :
    twoBundleProj c * bandClaspOp c * twoBundleProj c =
      ∑ k ∈ Finset.range (c + 1), claspAlgFullTwistCoeff c k • turnback c (c - k) := by
  have h : twoBundleProj c * (halfTwist c true * halfTwist c true) * twoBundleProj c =
      ∑ k ∈ Finset.range (c + 1), claspAlgFullTwistCoeff c k • turnback c k := by
    rw [Matrix.mul_assoc, halfTwist_sq_mul_twoBundleProj_eq_sum_turnback, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Matrix.mul_smul, twoBundleProj_mul_turnback]
  rw [bandClaspOp, twoBundleProj_mul_bandRot_mul_twoBundleProj, h, bandRot_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [bandRot_smul, bandRot_turnback c k (by have := Finset.mem_range.mp hk; omega)]

/-- The compressed clasp on the channels: the clasp eigenvalues. -/
theorem twoBundleProj_mul_bandClaspOp_mul_twoBundleProj_eq_sum (c : ℕ) :
    twoBundleProj c * bandClaspOp c * twoBundleProj c =
      ∑ n ∈ Finset.range (c + 1), claspAlgClaspEigen c n • channelIdem c n := by
  rw [twoBundleProj_mul_bandClaspOp_mul_twoBundleProj]
  simp only [claspAlgClaspEigen, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [turnback_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [smul_smul]

end AJConjecture
