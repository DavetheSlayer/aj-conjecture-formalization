import Mathlib
import AJTwist.TwDefs
import AJConjecture.SkeinHalfTwistSpectral
import AJConjecture.SkeinHalfTwistCap
import AJConjecture.SkeinJwThickCross
import AJConjecture.ClaspAlgScalars

/-!
# Signed powers of the cabled half twist on the channels (Unit Q2)

Source: revision 5, Section 2.1 (`marking.tex`, "The signed full twist": a full twist acts on the
channel of dimension `2n + 1` by `q^(n(n+1))`) and Section 3, eq. (commoninput).

`halfTwistZ c k` (the signed power `Σ_c^k` of `AJTwist.TwDefs`) acts on the channel `Q_n` of two
bundles of `c` strands by `λ_{c,n}^k`, where `λ_{c,n} = claspAlgHalfTwistEigen c n`; an even power
commutes with the projector of each bundle. `twQ_halfTwistEigen_zpow_mul` is the framing
bookkeeping: with `2κ` half twists over a companion whose blackboard framing is `w`, the channel
`n` carries the factor `q^((w + κ) n(n+1))`, up to a scalar that does not depend on `n`.
-/

noncomputable section

namespace AJConjecture

/-- A power of an operator acts on an eigen-operator by the power of the eigenvalue. -/
private theorem pow_mul_eq_pow_smul_twQHalfTwistZ {N : ℕ} (A Q : SkMat N N) (a : RatFunc ℚ)
    (h : A * Q = a • Q) (m : ℕ) : A ^ m * Q = a ^ m • Q := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mul, one_smul]
  | succ m ih => rw [pow_succ, Matrix.mul_assoc, h, Matrix.mul_smul, ih, smul_smul, pow_succ']

/-- The square of the half twist commutes with the projector on the first bundle. -/
private theorem jwAt_fst_mul_halfTwist_sq_twQHalfTwistZ (c : ℕ) (s : Bool) :
    Commute (jwAt (2 * c) 0 c) (halfTwist c s ^ 2) := by
  have h1 := jwAt_mul_braidMatrix_thickCross_fst (2 * c) c c 0 s (by omega)
  have h2 := jwAt_mul_braidMatrix_thickCross_snd (2 * c) c c 0 s (by omega)
  rw [Nat.zero_add, ← halfTwist_eq_braidMatrix_thickCross] at h1 h2
  change jwAt (2 * c) 0 c * halfTwist c s ^ 2 = halfTwist c s ^ 2 * jwAt (2 * c) 0 c
  rw [pow_two, ← Matrix.mul_assoc, h1, Matrix.mul_assoc, h2, Matrix.mul_assoc]

/-- The square of the half twist commutes with the projector on the second bundle. -/
private theorem jwAt_snd_mul_halfTwist_sq_twQHalfTwistZ (c : ℕ) (s : Bool) :
    Commute (jwAt (2 * c) c c) (halfTwist c s ^ 2) := by
  have h1 := jwAt_mul_braidMatrix_thickCross_fst (2 * c) c c 0 s (by omega)
  have h2 := jwAt_mul_braidMatrix_thickCross_snd (2 * c) c c 0 s (by omega)
  rw [Nat.zero_add, ← halfTwist_eq_braidMatrix_thickCross] at h1 h2
  change jwAt (2 * c) c c * halfTwist c s ^ 2 = halfTwist c s ^ 2 * jwAt (2 * c) c c
  rw [pow_two, ← Matrix.mul_assoc, h2, Matrix.mul_assoc, h1, Matrix.mul_assoc]

/-- An even signed power of the half twist is a power of the square of a half twist. -/
private theorem halfTwistZ_two_mul_twQHalfTwistZ (c : ℕ) (κ : ℤ) :
    ∃ (s : Bool) (m : ℕ), halfTwistZ c (2 * κ) = (halfTwist c s ^ 2) ^ m := by
  rcases le_or_gt 0 κ with hκ | hκ
  · refine ⟨true, κ.toNat, ?_⟩
    rw [halfTwistZ, ite_eq_left (by omega), ← pow_mul]
    congr 1
    omega
  · refine ⟨false, (-κ).toNat, ?_⟩
    rw [halfTwistZ, ite_eq_right (by omega), ← pow_mul]
    congr 1
    omega

/-- The signed power of the half twist acts on the channel `Q_n` by `λ_{c,n}^k`. -/
theorem halfTwistZ_mul_channelIdem (c n : ℕ) (k : ℤ) (hn : n ≤ c) :
    halfTwistZ c k * channelIdem c n = (claspAlgHalfTwistEigen c n) ^ k • channelIdem c n := by
  rcases le_or_gt 0 k with hk | hk
  · have h := halfTwist_mul_channelIdem c n true hn
    rw [ite_eq_left rfl] at h
    rw [halfTwistZ, ite_eq_left hk, pow_mul_eq_pow_smul_twQHalfTwistZ _ _ _ h, ← zpow_natCast,
      Int.toNat_of_nonneg hk]
  · have h := halfTwist_mul_channelIdem c n false hn
    rw [ite_eq_right Bool.false_ne_true] at h
    rw [halfTwistZ, ite_eq_right (by omega), pow_mul_eq_pow_smul_twQHalfTwistZ _ _ _ h, inv_pow,
      ← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_neg, neg_neg]

/-- The signed powers of the half twist commute with the projector `f_c ⊗ f_c`. -/
theorem halfTwistZ_commute_twoBundleProj (c : ℕ) (k : ℤ) :
    Commute (halfTwistZ c k) (twoBundleProj c) := by
  rw [halfTwistZ]
  split_ifs
  · exact Commute.pow_left (halfTwist_mul_twoBundleProj c true) _
  · exact Commute.pow_left (halfTwist_mul_twoBundleProj c false) _

/-- An even power of the half twist commutes with the projector on the first bundle. -/
theorem jwAt_fst_mul_halfTwistZ_two_mul (c : ℕ) (κ : ℤ) :
    jwAt (2 * c) 0 c * halfTwistZ c (2 * κ) = halfTwistZ c (2 * κ) * jwAt (2 * c) 0 c := by
  obtain ⟨s, m, h⟩ := halfTwistZ_two_mul_twQHalfTwistZ c κ
  rw [h]
  exact Commute.pow_right (jwAt_fst_mul_halfTwist_sq_twQHalfTwistZ c s) m

/-- An even power of the half twist commutes with the projector on the second bundle. -/
theorem jwAt_snd_mul_halfTwistZ_two_mul (c : ℕ) (κ : ℤ) :
    jwAt (2 * c) c c * halfTwistZ c (2 * κ) = halfTwistZ c (2 * κ) * jwAt (2 * c) c c := by
  obtain ⟨s, m, h⟩ := halfTwistZ_two_mul_twQHalfTwistZ c κ
  rw [h]
  exact Commute.pow_right (jwAt_snd_mul_halfTwist_sq_twQHalfTwistZ c s) m

/-- `λ_{c,n}^(2κ) t^(4 w n(n+1)) = t^(-2κ c(c+2)) q^((w + κ) n(n+1))`: the framing of the band is
`w + κ`, and the remaining scalar does not depend on the channel. -/
theorem twQ_halfTwistEigen_zpow_mul (w κ : ℤ) (c n : ℕ) :
    (claspAlgHalfTwistEigen c n) ^ (2 * κ) *
        (RatFunc.X : RatFunc ℚ) ^ (4 * w * (n : ℤ) * ((n : ℤ) + 1)) =
      (RatFunc.X : RatFunc ℚ) ^ (-(2 * κ) * (c : ℤ) * ((c : ℤ) + 2)) *
        qParam ^ ((w + κ) * (n : ℤ) * ((n : ℤ) + 1)) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hsign : (((-1 : RatFunc ℚ)) ^ (c + n)) ^ (2 * κ) = 1 := by
    rw [zpow_mul, zpow_ofNat, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow, one_zpow]
  rw [claspAlgHalfTwistEigen, mul_zpow, hsign, one_mul, ← zpow_mul, ← zpow_add₀ hX,
    qParam_zpow_eq_ratFuncX_zpow, ← zpow_add₀ hX]
  congr 1
  ring

end AJConjecture
