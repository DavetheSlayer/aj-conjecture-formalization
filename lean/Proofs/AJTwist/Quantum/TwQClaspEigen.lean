import Mathlib
import AJTwist.TwDefs
import AJTwist.Quantum.TwQBarBasic
import AJConjecture.SkeinBandClaspCompress
import AJConjecture.ClaspAlgFullTwistSum

/-!
# The clasp of either sign on the channels (Unit Q2)

Source: revision 5, Section 3 (the negative-clasp kernel `β_{N,n}`, eq. (claspfinite)) and
Section 8.2 (the positive clasp is the mirror image).

`(f ⊗ f) T_c^σ (f ⊗ f) = ∑_n ξ^σ_{c,n} Q_n` with `ξ^true_{c,n} = claspAlgClaspEigen c n` (the
library's `twoBundleProj_mul_bandClaspOp_mul_twoBundleProj_eq_sum`) and
`ξ^false_{c,n} = twQBar ξ^true_{c,n}`. For the positive clasp: the negative cabled full twist is
`∑_n λ_{c,n}^(-2) Q_n` (`halfTwist_mul_channelIdem`); the bar of the scalar identity
`∑_k s_k d_{k,n} = λ_{c,n}²` (`claspAlg_sum_fullTwistCoeff_mul_turnbackEigen`; the turnback
eigenvalues `d_{k,n}` are bar-invariant, `λ_{c,n}` is inverted) gives
`Σ_c^(-2) (f ⊗ f) = ∑_k \bar s_k D_k`, and the rotation exchanges `D_k` and `D_{c-k}`
(`bandRot_turnback`).
-/

noncomputable section

namespace AJConjecture

/-- The eigenvalue of the clasp of sign `σ` on the channel `Q_n`: the library's
`claspAlgClaspEigen c n` for the negative clasp, its bar for the positive clasp. -/
def twClaspEigen (σ : Bool) (c n : ℕ) : RatFunc ℚ :=
  if σ then claspAlgClaspEigen c n else twQBar (claspAlgClaspEigen c n)

/-- The turnback eigenvalues are bar-invariant. -/
theorem twQBar_claspAlgTurnbackEigen (c j n : ℕ) :
    twQBar (claspAlgTurnbackEigen c j n) = claspAlgTurnbackEigen c j n := by
  rw [claspAlgTurnbackEigen, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [map_div₀, map_neg, map_mul, map_pow, twQBar_quantumInt, twQBar_quantumInt,
    twQBar_quantumInt]

/-- The bar of the half-twist eigenvalue is its inverse. -/
theorem twQBar_claspAlgHalfTwistEigen (c n : ℕ) :
    twQBar (claspAlgHalfTwistEigen c n) = (claspAlgHalfTwistEigen c n)⁻¹ := by
  have hsign : ((-1 : RatFunc ℚ) ^ (c + n))⁻¹ = (-1) ^ (c + n) := by
    rw [← inv_pow, inv_neg_one]
  rw [claspAlgHalfTwistEigen, map_mul, map_pow, map_neg, map_one, twQBar_X_zpow, mul_inv, hsign,
    zpow_neg]

/-- The barred turnback expansion of the cabled full twist evaluated on the eigenvalues of the
turnback elements: the bar of identity J1′. -/
private theorem sum_twQBar_fullTwistCoeff_mul_turnbackEigen_twQClaspEigen (c n : ℕ)
    (hn : n ≤ c) :
    ∑ k ∈ Finset.range (c + 1),
        twQBar (claspAlgFullTwistCoeff c k) * claspAlgTurnbackEigen c k n =
      (claspAlgHalfTwistEigen c n)⁻¹ * (claspAlgHalfTwistEigen c n)⁻¹ := by
  have h := congrArg twQBar (claspAlg_sum_fullTwistCoeff_mul_turnbackEigen c n hn)
  rw [map_sum, map_pow, twQBar_claspAlgHalfTwistEigen, sq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, twQBar_claspAlgTurnbackEigen]

/-- A combination of turnback elements in the basis of the channel idempotents. -/
private theorem sum_smul_turnback_twQClaspEigen (c : ℕ) (f : ℕ → RatFunc ℚ) (g : ℕ → ℕ) :
    ∑ k ∈ Finset.range (c + 1), f k • turnback c (g k) =
      ∑ n ∈ Finset.range (c + 1),
        (∑ k ∈ Finset.range (c + 1), f k * claspAlgTurnbackEigen c (g k) n) •
          channelIdem c n := by
  have h : ∀ k ∈ Finset.range (c + 1), f k • turnback c (g k) =
      ∑ n ∈ Finset.range (c + 1),
        (f k * claspAlgTurnbackEigen c (g k) n) • channelIdem c n := by
    intro k _
    rw [turnback_eq_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun n _ ↦ smul_smul _ _ _
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ ↦ (Finset.sum_smul).symm

/-- The negative cabled full twist in the turnback basis. -/
theorem halfTwist_false_sq_mul_twoBundleProj_eq_sum_turnback (c : ℕ) :
    halfTwist c false * halfTwist c false * twoBundleProj c =
      ∑ k ∈ Finset.range (c + 1), twQBar (claspAlgFullTwistCoeff c k) • turnback c k := by
  rw [sum_smul_turnback_twQClaspEigen c _ fun k ↦ k, Matrix.mul_assoc,
    halfTwist_mul_twoBundleProj_eq_sum, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn' : n ≤ c := by
    rw [Finset.mem_range] at hn
    omega
  rw [sum_twQBar_fullTwistCoeff_mul_turnbackEigen_twQClaspEigen c n hn', Matrix.mul_smul,
    halfTwist_mul_channelIdem c n false hn', smul_smul]
  rfl

/-- The compressed clasp of either sign on the channels. -/
theorem twoBundleProj_mul_claspSOp_mul_twoBundleProj_eq_sum (c : ℕ) (σ : Bool) :
    twoBundleProj c * claspSOp c σ * twoBundleProj c =
      ∑ n ∈ Finset.range (c + 1), twClaspEigen σ c n • channelIdem c n := by
  cases σ
  · have h : twoBundleProj c * (halfTwist c false * halfTwist c false) * twoBundleProj c =
        ∑ k ∈ Finset.range (c + 1), twQBar (claspAlgFullTwistCoeff c k) • turnback c k := by
      rw [Matrix.mul_assoc, halfTwist_false_sq_mul_twoBundleProj_eq_sum_turnback,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Matrix.mul_smul, twoBundleProj_mul_turnback]
    have hrot : twoBundleProj c * claspSOp c false * twoBundleProj c =
        ∑ k ∈ Finset.range (c + 1),
          twQBar (claspAlgFullTwistCoeff c k) • turnback c (c - k) := by
      change twoBundleProj c * bandRot c (halfTwist c false * halfTwist c false) *
        twoBundleProj c = _
      rw [twoBundleProj_mul_bandRot_mul_twoBundleProj, h, bandRot_sum]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [bandRot_smul, bandRot_turnback c k (by have := Finset.mem_range.mp hk; omega)]
    rw [hrot, sum_smul_turnback_twQClaspEigen c _ fun k ↦ c - k]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    congr 1
    rw [twClaspEigen, ite_eq_right Bool.false_ne_true, claspAlgClaspEigen, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, twQBar_claspAlgTurnbackEigen]
  · exact twoBundleProj_mul_bandClaspOp_mul_twoBundleProj_eq_sum c

end AJConjecture
