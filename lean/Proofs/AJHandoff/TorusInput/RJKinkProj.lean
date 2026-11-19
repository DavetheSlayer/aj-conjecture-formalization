import Mathlib
import AJHandoff.TorusInput.RJDefs
import AJConjecture.SkeinKinkRecursion
import AJConjecture.SkeinJwAbsorb
import AJConjecture.SkeinJwBasic
import AJConjecture.SkeinHalfTwistFusion

/-!
# A kink on a projector (node RA5.ii.5)

`f_c kink⁺_c f_c = θ_c f_c`, `θ_c = (-1)^c t^(c(c+2))` (Remark "The twist" of the manuscript; not a
theorem of the library).

Route. Induction on `c` with `kinkOp_succ`:
`kink_(c+1) = -t³ ρ(X_(c,1)(0)) (1 ⊗ kink_c) ρ(X_(1,c)(0))`. With `f_(c+1)` on both sides, the
`2c` crossings lie inside its block (`jwAt_mul_braidMatrix_of_inside`,
`braidMatrix_mul_jwAt_of_inside`: `t^c` each), and `f_(c+1) = f_(c+1) (1 ⊗ f_c)`
(`jwAt_mul_jwAt_of_ge`, `jwAt_eq_skPlace`), so the middle is `f_(c+1) (1 ⊗ f_c kink_c f_c) f_(c+1)
= θ_c f_(c+1)`; and `-t³ t^(2c) θ_c = θ_(c+1)`. Base: `kink_0 = 1 = θ_0`. Estimate 60–100 lines.
-/

noncomputable section

namespace AJConjecture

/-- The kink of the empty bundle is the identity. -/
private theorem rj_kinkOp_zero_kinkProj : kinkOp 0 true = 1 := by
  rw [kinkOp, halfTwist]
  change ptrTail 0 0 (braidMatrix 0 (cableGen 0 (0, true))) = 1
  rw [ptrTail_self]
  simp [cableGen, braidMatrix]

/-- The writhe of a positive thick crossing. -/
private theorem rj_writhe_thickCross_true_kinkProj (a b off : ℕ) :
    writhe (thickCross a b off true) = ((a * b : ℕ) : ℤ) := by
  rw [writhe_eq_of_forall_sign _ true fun g hg ↦ (mem_thickCross hg).2.2, length_thickCross]
  simp only [↓reduceIte, one_mul]

/-- The kink scalars satisfy `θ_(c+1) = -t³ t^c t^c θ_c`. -/
private theorem rj_kinkScalar_succ_kinkProj (c : ℕ) :
    -(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ) * ((RatFunc.X : RatFunc ℚ) ^ (((c * 1 : ℕ) : ℤ)) *
        (RatFunc.X : RatFunc ℚ) ^ (((1 * c : ℕ) : ℤ))) * kinkScalar c = kinkScalar (c + 1) := by
  have e1 : ((c + 1 : ℕ) : ℤ) * (((c + 1 : ℕ) : ℤ) + 2) = (((c + 1) * (c + 3) : ℕ) : ℤ) := by
    push_cast; ring
  have e2 : (c : ℤ) * ((c : ℤ) + 2) = ((c * (c + 2) : ℕ) : ℤ) := by push_cast; ring
  simp only [kinkScalar]
  rw [e1, e2]
  simp only [zpow_natCast, zpow_ofNat]
  rw [show (c + 1) * (c + 3) = 3 + (c * 1 + 1 * c) + c * (c + 2) by ring, pow_add, pow_add,
    pow_add]
  ring

/-- A positive kink on a bundle with projectors at both ends is the scalar `θ_c`. -/
theorem rj_jwAt_mul_kinkOp_mul_jwAt (c : ℕ) :
    jwAt c 0 c * kinkOp c true * jwAt c 0 c = kinkScalar c • jwAt c 0 c := by
  induction c with
  | zero =>
    rw [rj_kinkOp_zero_kinkProj, Matrix.mul_one, jwAt, Matrix.mul_one, kinkScalar]
    simp
  | succ c ih =>
    set f := jwAt (c + 1) 0 (c + 1) with hf
    set g := skPlace (c + 1) (c + 1) 1 (jwAt c 0 c) with hg
    have hfg : f * g = f := by
      rw [hg, ← jwAt_eq_skPlace (c + 1) 1 c (by omega)]
      exact jwAt_mul_jwAt_of_le _ _ _ _ _ (by omega) (by omega)
    have hgf : g * f = f := by
      rw [hg, ← jwAt_eq_skPlace (c + 1) 1 c (by omega)]
      exact jwAt_mul_jwAt_of_ge _ _ _ _ _ (by omega) (by omega)
    have h1 : f * braidMatrix (c + 1) (thickCross c 1 0 true) =
        (RatFunc.X : RatFunc ℚ) ^ (((c * 1 : ℕ) : ℤ)) • f := by
      rw [hf, jwAt_mul_braidMatrix_of_inside _ _ _ _ fun g hg ↦ by
        have := mem_thickCross hg
        omega, rj_writhe_thickCross_true_kinkProj]
    have h2 : braidMatrix (c + 1) (thickCross 1 c 0 true) * f =
        (RatFunc.X : RatFunc ℚ) ^ (((1 * c : ℕ) : ℤ)) • f := by
      rw [hf, braidMatrix_mul_jwAt_of_inside _ _ _ _ fun g hg ↦ by
        have := mem_thickCross hg
        omega, rj_writhe_thickCross_true_kinkProj]
    have hmid : f * skPlace (c + 1) (c + 1) 1 (kinkOp c true) * f = kinkScalar c • f := by
      calc f * skPlace (c + 1) (c + 1) 1 (kinkOp c true) * f
          = f * g * skPlace (c + 1) (c + 1) 1 (kinkOp c true) * (g * f) := by rw [hfg, hgf]
        _ = f * skPlace (c + 1) (c + 1) 1 (jwAt c 0 c * kinkOp c true * jwAt c 0 c) * f := by
          rw [skPlace_mul (c + 1) (c + 1) (c + 1) 1 _ _ (by omega) (by omega) (by omega),
            skPlace_mul (c + 1) (c + 1) (c + 1) 1 _ _ (by omega) (by omega) (by omega), ← hg]
          simp only [Matrix.mul_assoc]
        _ = kinkScalar c • f := by
          rw [ih, skPlace_smul, Matrix.mul_smul, Matrix.smul_mul, ← hg, hfg, hf,
            jwAt_mul_self]
    rw [kinkOp_succ, Matrix.mul_smul, Matrix.smul_mul]
    simp only [↓reduceIte]
    calc (-(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ)) • (f * (braidMatrix (c + 1) (thickCross c 1 0 true) *
            skPlace (c + 1) (c + 1) 1 (kinkOp c true) *
            braidMatrix (c + 1) (thickCross 1 c 0 true)) * f)
        = (-(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ)) •
            (f * braidMatrix (c + 1) (thickCross c 1 0 true) *
              skPlace (c + 1) (c + 1) 1 (kinkOp c true) *
              (braidMatrix (c + 1) (thickCross 1 c 0 true) * f)) := by
          simp only [Matrix.mul_assoc]
      _ = kinkScalar (c + 1) • f := by
          rw [h1, h2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hmid, smul_smul,
            smul_smul, smul_smul, ← rj_kinkScalar_succ_kinkProj c]
          ring_nf

end AJConjecture
