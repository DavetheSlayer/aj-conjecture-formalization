import Mathlib
import AJHandoff.TorusInput.RJLoopParallel
import AJHandoff.TorusInput.RJLoopCap
import AJConjecture.SkeinJwCupCap
import AJConjecture.SkeinJwThickCross
import AJConjecture.SkeinTlGenPlace

/-!
# The Hopf scalar (node RA5.i, crux-adjacent)

`Ω_k f_N = rjHopf N k · f_N`, `rjHopf N k = (-1)^k [(N+1)(k+1)] / [N+1]`: a loop coloured `f_k`
around `f_N`.

Route. Put `h_k = ` the scalar of `f_N ω_k(f_k)`. `k = 0`: `ω_0 = 1`. `k = 1`:
`rj_axisLoop_one_mul_jwAt`. Step (the Chebyshev recursion in the colour of the loop, as in
`knotTrace_jwAt_succ_succ`): Wenzl's recursion
`f_(k+2) = (f_(k+1) ⊗ 1) + ([k+1]/[k+2]) (f_(k+1) ⊗ 1) e_k (f_(k+1) ⊗ 1)`; the first term gives
`λ_N h_(k+1)` (`rj_jwAt_mul_loopWith_succ`); in the second, move one projector cyclically
(`rj_loopWith_mul_comm`; projectors on the loop strands slide through the twist by
`jwAt_mul_braidMatrix_thickCross_snd` twice), write `e_k = cap_k cup_k` (`capAt_mul_cupAt`), move
the cap around the loop (`rj_loopWith_capAt_mul`) and close it on the projector
(`cupAt_mul_jwAt_mul_capAt`: `-[k+2]/[k+1] f_k`). Hence `h_(k+2) = λ_N h_(k+1) - h_k`, and the
closed form follows by induction (`[(N+1)(k+3)] + [(N+1)(k+1)] = (t^(2N+2) + t^(-2N-2))
[(N+1)(k+2)]`, from `quantumInt_mul_shift_sub`). `Ω_k` commutes with `f_N` (`rjNat_jwAt`,
`rjAxisLoop_mul_of_rjNat`). Numerically checked (design notes). Estimate 120–180 lines.
-/

noncomputable section

namespace AJConjecture

/-- The Chebyshev recursion of the Hopf scalars in the colour of the loop. -/
private theorem rjHopf_succ_succ_loopHopf (N k : ℕ) :
    rjHopf N 1 * rjHopf N (k + 1) +
        quantumInt ((k : ℤ) + 1) / quantumInt ((k : ℤ) + 2) *
          -(quantumInt ((k : ℤ) + 2) / quantumInt ((k : ℤ) + 1)) * rjHopf N k =
      rjHopf N (k + 2) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hD := claspAlg_ratFuncX_sq_sub_ne_zero
  have h1 : quantumInt ((k : ℤ) + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have h2 : quantumInt ((k : ℤ) + 2) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have hA : quantumInt ((N : ℤ) + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have hc : quantumInt ((k : ℤ) + 1) / quantumInt ((k : ℤ) + 2) *
      -(quantumInt ((k : ℤ) + 2) / quantumInt ((k : ℤ) + 1)) = -1 := by
    field_simp
  rw [hc]
  set A : ℤ := (N : ℤ) + 1 with hAdef
  set u : RatFunc ℚ := RatFunc.X ^ (2 * A) with hu
  have hu0 : u ≠ 0 := zpow_ne_zero _ hX
  have hq : ∀ m : ℤ, quantumInt (A * m) = (u ^ m - u ^ (-m)) /
      ((RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) := fun m ↦ by
    rw [quantumInt, hu, ← zpow_mul, ← zpow_mul, show 2 * A * -m = -(2 * (A * m)) by ring,
      mul_assoc]
  have hq1 : quantumInt A = (u - u⁻¹) /
      ((RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) := by
    rw [← mul_one A, hq, zpow_one, zpow_neg, zpow_one]
  simp only [rjHopf]
  push_cast
  rw [hq, hq, hq, hq, hq1]
  rw [hq1] at hA
  have hA1 : u - u⁻¹ ≠ 0 := fun h ↦ hA (by rw [h, zero_div])
  have hA2 : u ^ 2 - 1 ≠ 0 := fun h ↦ hA1 (by
    rw [show u - u⁻¹ = (u ^ 2 - 1) / u by field_simp, h, zero_div])
  simp only [neg_add, zpow_add₀ hu0, zpow_neg, zpow_one, zpow_natCast]
  field_simp
  ring

/-- A Temperley–Lieb generator inside the loop bundle slides through the full twist. -/
private theorem tlGenF_mul_rjFullTwist_loopHopf (N m l : ℕ) (hl : l + 1 < m) :
    tlGenF (N + m) (N + l) * rjFullTwist N m = rjFullTwist N m * tlGenF (N + m) (N + l) := by
  have h1 := tlGenF_mul_braidMatrix_thickCross_snd (N + m) N m 0 l true (by omega) hl
  have h2 := tlGenF_mul_braidMatrix_thickCross_fst (N + m) m N 0 l true (by omega) hl
  simp only [zero_add] at h1 h2
  rw [rjFullTwist, braidMatrix_append, ← Matrix.mul_assoc, h1, Matrix.mul_assoc, h2,
    Matrix.mul_assoc]

/-- A projector on the first strands of the loop bundle slides through the full twist. -/
private theorem rjFullTwist_mul_jwAt_loopHopf (N m l : ℕ) (hl : l ≤ m) :
    rjFullTwist N m * skPlace (N + m) (N + m) N (jwAt m 0 l) =
      skPlace (N + m) (N + m) N (jwAt m 0 l) * rjFullTwist N m := by
  rw [jwAt_eq_skPlace m 0 l (by omega), skPlace_skPlace _ _ N 0 _ (by omega) (by omega)
    (by omega) (by omega), add_zero, ← jwAt_eq_skPlace (N + m) N l (by omega)]
  exact (jwAt_mul_eq_mul_jwAt (N + m) (N + m) N N _ l fun l' hl' ↦
    tlGenF_mul_rjFullTwist_loopHopf N m l' (by omega)).symm

/-- The loop operator is additive in the operator on the loop strands. -/
private theorem rjLoopWith_add_loopHopf (N k : ℕ) (A B : SkMat k k) :
    rjLoopWith N k (A + B) = rjLoopWith N k A + rjLoopWith N k B := by
  rw [rjLoopWith, skPlace_add, Matrix.mul_add, ptrTail_add, rjLoopWith, rjLoopWith]

/-- The loop operator commutes with scalars. -/
private theorem rjLoopWith_smul_loopHopf (N k : ℕ) (x : RatFunc ℚ) (A : SkMat k k) :
    rjLoopWith N k (x • A) = x • rjLoopWith N k A := by
  rw [rjLoopWith, skPlace_smul, Matrix.mul_smul, ptrTail_smul, rjLoopWith]

/-- The Hopf scalar of a loop coloured `f_k`, with the projector `f_N` on the left. -/
private theorem jwAt_mul_loopWith_jwAt_loopHopf (N k : ℕ) :
    jwAt N 0 N * rjLoopWith N k (jwAt k 0 k) = rjHopf N k • jwAt N 0 N := by
  induction k using Nat.twoStepInduction with
  | zero =>
    have h0 : thickGen N 0 0 true = [] := List.flatMap_eq_nil_iff.mpr fun _ _ ↦ rfl
    have hA : quantumInt ((N : ℤ) + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
    have hL : rjLoopWith N 0 (jwAt 0 0 0) = 1 := by
      rw [rjLoopWith, show jwAt 0 0 0 = 1 from rfl, skPlace_one _ _ _ (by omega),
        Matrix.mul_one, rjFullTwist]
      simp only [thickCross, ite_true, h0]
      exact ptrTail_self N 1
    rw [hL, Matrix.mul_one, rjHopf]
    simp [hA]
  | one =>
    rw [← rjAxisLoop, ← rjAxisLoop_mul_of_rjNat 1 (rjNat_jwAt N 0 N (by omega))]
    exact rj_axisLoop_one_mul_jwAt N
  | more k ih0 ih1 =>
    have hW : jwAt (k + 2) 0 (k + 2) = jwAt (k + 2) 0 (k + 1) +
        (quantumInt ((k : ℤ) + 1) / quantumInt ((k : ℤ) + 2)) •
          (jwAt (k + 2) 0 (k + 1) * tlGenF (k + 2) k * jwAt (k + 2) 0 (k + 1)) := by
      rw [jwAt, zero_add]
    have hF : jwAt (k + 2) 0 (k + 1) = skPlace (k + 1 + 1) (k + 1 + 1) 0 (jwAt (k + 1) 0 (k + 1)) :=
      jwAt_eq_skPlace _ 0 _ (by omega)
    have t1 : jwAt N 0 N * rjLoopWith N (k + 2) (jwAt (k + 2) 0 (k + 1)) =
        (rjHopf N 1 * rjHopf N (k + 1)) • jwAt N 0 N := by
      rw [hF, rj_jwAt_mul_loopWith_succ N (k + 1), ih1, smul_smul]
    have t2 : rjLoopWith N (k + 2)
        (jwAt (k + 2) 0 (k + 1) * tlGenF (k + 2) k * jwAt (k + 2) 0 (k + 1)) =
        (-(quantumInt ((k : ℤ) + 2) / quantumInt ((k : ℤ) + 1))) •
          rjLoopWith N k (jwAt k 0 k) := by
      rw [Matrix.mul_assoc, rj_loopWith_mul_comm N (k + 2) _ _
        (rjFullTwist_mul_jwAt_loopHopf N (k + 2) (k + 1) (by omega)) (skWeight_mul_jwAt _ _ _),
        Matrix.mul_assoc, jwAt_mul_self, ← capAt_mul_cupAt k k le_rfl, Matrix.mul_assoc,
        rj_loopWith_capAt_mul N k k le_rfl, cupAt_mul_jwAt_mul_capAt k k le_rfl,
        rjLoopWith_smul_loopHopf]
    rw [hW, rjLoopWith_add_loopHopf, rjLoopWith_smul_loopHopf, Matrix.mul_add, Matrix.mul_smul,
      t1, t2, Matrix.mul_smul, ih0, ← rjHopf_succ_succ_loopHopf, add_smul, smul_smul, smul_smul,
      mul_assoc]

/-- The axis loop coloured `f_k` acts on `f_N` by the Hopf scalar. -/
theorem rj_axisLoop_mul_jwAt (N k : ℕ) :
    rjAxisLoop N k * jwAt N 0 N = rjHopf N k • jwAt N 0 N := by
  rw [rjAxisLoop_mul_of_rjNat k (rjNat_jwAt N 0 N (by omega)), rjAxisLoop,
    jwAt_mul_loopWith_jwAt_loopHopf]

end AJConjecture
