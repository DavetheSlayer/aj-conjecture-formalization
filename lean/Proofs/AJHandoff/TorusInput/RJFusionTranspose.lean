import Mathlib
import AJHandoff.TorusInput.RJFusionTwistEigen
import AJConjecture.SkeinThickGenReverse
import AJConjecture.SkeinTranspose
import AJConjecture.SkeinJwBasic

/-!
# Transposes: the inclusion is the transposed projection (node RA1.8)

`J_(a,b)` is symmetric; `ι_j = (-t²)^j π_jᵀ`; hence `ι_j J_(a,b) = (θ_(a+b-2j)/(θ_a θ_b)) ι_j`.

Route. `braidMatrix_thickCross_transpose` (`ρ(X_(a,b))ᵀ = ρ(X_(b,a))`) and `Matrix.transpose_mul`
give `Jᵀ = J`. `jwAt_transpose`, `skPlace_transpose`, and `cupThick c = (-t²)^c (capThick c)ᵀ`
(entrywise: `cupEntry = -t² capEntry`; compare `cupAt_eq_smul_transpose_capAt`). Then transpose
`rj_fullTwist_mul_fusionProj`. Estimate 60–100 lines.
-/

noncomputable section

namespace AJConjecture

/-- The full twist of two bundles is a symmetric matrix. -/
theorem rj_fullTwist_transpose (a b : ℕ) : (rjFullTwist a b).transpose = rjFullTwist a b := by
  rw [rjFullTwist, braidMatrix_append, Matrix.transpose_mul,
    braidMatrix_thickCross_transpose (a + b) b a 0 true,
    braidMatrix_thickCross_transpose (a + b) a b 0 true]

/-- The entries of the cup are `-t²` times the entries of the cap. -/
private theorem rj_cupEntry_eq_mul_capEntry_transpose (a b : Bool) :
    cupEntry a b = -(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) * capEntry a b := by
  cases a <;> cases b
  · simp only [cupEntry, capEntry, mul_zero]
  · simp only [cupEntry, capEntry, mul_one]
  · simp only [cupEntry, capEntry]
    rw [neg_mul_neg, ← zpow_add₀ RatFunc.X_ne_zero]
    norm_num
  · simp only [cupEntry, capEntry, mul_zero]

/-- The thick cup is a multiple of the transpose of the thick cap. -/
private theorem rj_cupThick_eq_smul_transpose_transpose (m : ℕ) :
    cupThick m = (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ)) ^ m • (capThick m).transpose := by
  ext a b
  simp only [cupThick, capThick, Matrix.of_apply, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul, rj_cupEntry_eq_mul_capEntry_transpose, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `f_a ⊗ f_b` is a symmetric matrix. -/
private theorem rj_bundleProj_transpose (a b : ℕ) :
    (rjBundleProj a b).transpose = rjBundleProj a b := by
  rw [rjBundleProj, Matrix.transpose_mul, jwAt_transpose, jwAt_transpose]
  exact jwAt_mul_eq_mul_jwAt _ _ a a (jwAt (a + b) 0 a) b fun l _ ↦
    (jwAt_commute_tlGenF _ 0 a (a + l) (Or.inr (by omega))).eq.symm

/-- The fusion inclusion is `(-t²)^j` times the transposed fusion map. -/
theorem rj_fusionIncl_eq_transpose (a b j : ℕ) :
    rjFusionIncl a b j =
      (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ)) ^ j • (rjFusionProj a b j).transpose := by
  rw [rjFusionIncl, rjFusionProj, Matrix.transpose_mul, Matrix.transpose_mul, jwAt_transpose,
    rj_bundleProj_transpose, skPlace_transpose, rj_cupThick_eq_smul_transpose_transpose,
    skPlace_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- The full twist acts on the fusion inclusion of the channel `j` by `θ_(a+b-2j)/(θ_a θ_b)`. -/
theorem rj_fusionIncl_mul_fullTwist (a b j : ℕ) (hj : j ≤ min a b) :
    rjFusionIncl a b j * rjFullTwist a b = rjTwistRatio a b j • rjFusionIncl a b j := by
  rw [rj_fusionIncl_eq_transpose, Matrix.smul_mul, ← rj_fullTwist_transpose,
    ← Matrix.transpose_mul, rj_fullTwist_mul_fusionProj a b j hj, Matrix.transpose_smul,
    smul_comm]

end AJConjecture
