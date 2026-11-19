import Mathlib
import AJConjecture.SkeinBraidMatrixBasic
import AJConjecture.SkeinTlGenPlace
import AJConjecture.SkeinZigzag

/-!
# A cap slides across a single strand

The cap on the strands `i`, `i + 1` is the cap on `i + 1`, `i + 2` preceded by the third strand
crossing both of them, with either sign; and symmetrically. With `σ^{±1} = t^{±1} + t^{∓1} e` and
`capAt_{i+1} e_i = capAt_i` (zig-zag) the four products reduce to
`(t² + t⁻² + δ) capAt + capAt = capAt`. A kink on a cap is the scalar `-t^{∓3}`.
-/

namespace AJConjecture

/-- `e_i` absorbs the cap on its own strands with the loop value. -/
private theorem tlGenF_mul_capAt_self_capSlideThin (n i : ℕ) (h : i ≤ n) :
    tlGenF (n + 2) i * capAt n i =
      (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) • capAt n i := by
  rw [← capAt_mul_cupAt n i h, Matrix.mul_assoc, cupAt_mul_capAt n i h, Matrix.mul_smul,
    Matrix.mul_one]

/-- `e_i` turns the cap on the strands `i + 1`, `i + 2` into the cap on `i`, `i + 1`. -/
private theorem tlGenF_mul_capAt_succ_capSlideThin (n i : ℕ) (h : i < n) :
    tlGenF (n + 2) i * capAt n (i + 1) = capAt n i := by
  rw [← capAt_mul_cupAt n i h.le, Matrix.mul_assoc, cupAt_mul_capAt_succ n i h, Matrix.mul_one]

/-- `e_{i+1}` turns the cap on the strands `i`, `i + 1` into the cap on `i + 1`, `i + 2`. -/
private theorem tlGenF_succ_mul_capAt_capSlideThin (n i : ℕ) (h : i < n) :
    tlGenF (n + 2) (i + 1) * capAt n i = capAt n (i + 1) := by
  rw [← capAt_mul_cupAt n (i + 1) h, Matrix.mul_assoc, cupAt_succ_mul_capAt n i h, Matrix.mul_one]

/-- The linear identity behind the slide, in an abstract module. -/
private theorem slide_linear_identity_capSlideThin {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] (a b δ : K) (C D : M) :
    a • (a • C + b • δ • C) + b • (a • D + b • C) =
      (a * a + a * b * δ + b * b) • C + (a * b) • D := by
  module

/-- The slide in abstract form: if `e C = D`, `f C = δ C`, `f D = C`, `a b = 1` and
`a² + b² + δ = 0`, then `(a + b f) (a + b e) C = D`. -/
private theorem slide_of_relations_capSlideThin {N n : ℕ} (e f : SkMat N N) (C D : SkMat N n)
    (a b δ : RatFunc ℚ) (hab : a * b = 1) (hδ : a * a + b * b + δ = 0) (heC : e * C = D)
    (hfC : f * C = δ • C) (hfD : f * D = C) :
    (a • (1 : SkMat N N) + b • f) * (a • (1 : SkMat N N) + b • e) * C = D := by
  have hc : a * a + a * b * δ + b * b = 0 := by rw [hab]; linear_combination hδ
  have hL : (a • (1 : SkMat N N) + b • f) * (a • (1 : SkMat N N) + b • e) * C =
      (a * a + a * b * δ + b * b) • C + (a * b) • D := by
    simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, heC, hfC, hfD]
    exact slide_linear_identity_capSlideThin a b δ C D
  rw [hL, hc, hab, zero_smul, zero_add, one_smul]

/-- `t t⁻¹ = 1` in `ℚ(t)`. -/
theorem ratFuncX_mul_inv :
    (RatFunc.X : RatFunc ℚ) * (RatFunc.X : RatFunc ℚ)⁻¹ = 1 :=
  mul_inv_cancel₀ RatFunc.X_ne_zero

/-- `t² + t⁻² + δ = 0` in `ℚ(t)`. -/
theorem ratFuncX_sq_add_loop :
    (RatFunc.X : RatFunc ℚ) * RatFunc.X + (RatFunc.X : RatFunc ℚ)⁻¹ * (RatFunc.X : RatFunc ℚ)⁻¹ +
      (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) = 0 := by
  rw [zpow_neg, zpow_ofNat]
  ring

/-- `t⁻² + t² + δ = 0` in `ℚ(t)`. -/
theorem ratFuncX_inv_sq_add_loop :
    (RatFunc.X : RatFunc ℚ)⁻¹ * (RatFunc.X : RatFunc ℚ)⁻¹ + (RatFunc.X : RatFunc ℚ) * RatFunc.X +
      (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) = 0 := by
  rw [zpow_neg, zpow_ofNat]
  ring

/-- The strand on the right of a cap crosses its two strands and the cap moves to the right. -/
theorem crossingF_mul_crossingF_mul_capAt_succ (n i : ℕ) (s : Bool) (h : i + 1 ≤ n) :
    crossingF (n + 2) (i + 1, s) * crossingF (n + 2) (i, s) * capAt n (i + 1) = capAt n i := by
  cases s
  · rw [crossingF_neg, crossingF_neg]
    exact slide_of_relations_capSlideThin _ _ _ _ _ _ _
      ((mul_comm _ _).trans ratFuncX_mul_inv) ratFuncX_inv_sq_add_loop
      (tlGenF_mul_capAt_succ_capSlideThin n i h) (tlGenF_mul_capAt_self_capSlideThin n (i + 1) h)
      (tlGenF_succ_mul_capAt_capSlideThin n i h)
  · rw [crossingF_pos, crossingF_pos]
    exact slide_of_relations_capSlideThin _ _ _ _ _ _ _
      ratFuncX_mul_inv ratFuncX_sq_add_loop
      (tlGenF_mul_capAt_succ_capSlideThin n i h) (tlGenF_mul_capAt_self_capSlideThin n (i + 1) h)
      (tlGenF_succ_mul_capAt_capSlideThin n i h)

/-- The strand on the left of a cap crosses its two strands and the cap moves to the left. -/
theorem crossingF_mul_crossingF_mul_capAt (n i : ℕ) (s : Bool) (h : i + 1 ≤ n) :
    crossingF (n + 2) (i, s) * crossingF (n + 2) (i + 1, s) * capAt n i = capAt n (i + 1) := by
  cases s
  · rw [crossingF_neg, crossingF_neg]
    exact slide_of_relations_capSlideThin _ _ _ _ _ _ _
      ((mul_comm _ _).trans ratFuncX_mul_inv) ratFuncX_inv_sq_add_loop
      (tlGenF_succ_mul_capAt_capSlideThin n i h)
      (tlGenF_mul_capAt_self_capSlideThin n i (by omega))
      (tlGenF_mul_capAt_succ_capSlideThin n i h)
  · rw [crossingF_pos, crossingF_pos]
    exact slide_of_relations_capSlideThin _ _ _ _ _ _ _
      ratFuncX_mul_inv ratFuncX_sq_add_loop
      (tlGenF_succ_mul_capAt_capSlideThin n i h)
      (tlGenF_mul_capAt_self_capSlideThin n i (by omega))
      (tlGenF_mul_capAt_succ_capSlideThin n i h)

/-- A crossing of the two strands of a cap is a kink: the scalar `-t⁻³` (positive crossing) or
`-t³` (negative crossing). -/
theorem crossingF_mul_capAt (n i : ℕ) (s : Bool) (h : i ≤ n) :
    crossingF (n + 2) (i, s) * capAt n i =
      (if s then -(RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ) else -(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ)) •
        capAt n i := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  cases s
  · rw [crossingF_neg, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
      tlGenF_mul_capAt_self_capSlideThin n i h, smul_smul, ← add_smul]
    congr 1
    simp only [Bool.false_eq_true, ↓reduceIte, zpow_neg, zpow_ofNat]
    field_simp
    ring
  · rw [crossingF_pos, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
      tlGenF_mul_capAt_self_capSlideThin n i h, smul_smul, ← add_smul]
    congr 1
    simp only [↓reduceIte, zpow_neg, zpow_ofNat]
    field_simp
    ring

end AJConjecture
