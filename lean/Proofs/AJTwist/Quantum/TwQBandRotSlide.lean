import Mathlib
import AJTwist.TwDefs
import AJConjecture.SkeinBandRotProj

/-!
# A projector slides through the clasp of either sign (Unit Q2)

The clasp of sign `σ` is the quarter-turn rotation `bandRot c (Σ_c^{±2})` of the cabled full
twist. A Jones–Wenzl projector on one edge of the band passes through the rotation of any
operator that commutes with it: the two edges of the band are joined by the thick cup and the
thick cap of the rotation. For the negative clasp (`σ = true`) these are the library's
`jwAt_mul_bandClaspOp`, `bandClaspOp_mul_jwAt`; their proofs
(`AJConjecture/SkeinBandRotProj.lean`) use the twist only through its commutation with the
projectors, which holds for both signs (`jwAt_mul_braidMatrix_thickCross_fst`, `_snd`).

This is what makes one projector on one edge of the band sufficient for the positive clasp.
-/

noncomputable section

namespace AJConjecture

/-- The clasp of sign `σ` is the rotation of the cabled full twist of sign `σ`. -/
theorem claspSOp_eq_bandRot (c : ℕ) (σ : Bool) :
    claspSOp c σ = bandRot c (halfTwist c σ * halfTwist c σ) := rfl

/-- A projector on the right of a placed matrix commutes with it; its position `i` becomes
`i'`. -/
private theorem jwAt_mul_skPlace_of_ge_twQBandRotSlide (n n' i i' k j : ℕ) {p q : ℕ}
    (X : SkMat p q) (h : j + p ≤ i) (hi : i + k ≤ n) (hn : n + q = n' + p)
    (hi' : i' + p = i + q) :
    jwAt n i k * skPlace n n' j X = skPlace n n' j X * jwAt n' i' k :=
  jwAt_mul_eq_mul_jwAt n n' i i' _ k fun l _ ↦ by
    rw [tlGenF_mul_skPlace_of_ge n n' (i + l) j X (by omega) (by omega) hn,
      show i + l + q - p = i' + l from by omega]

/-- A placed projector is a projector. -/
private theorem skPlace_jwAt_twQBandRotSlide (n m i j k s : ℕ) (hj : j + k ≤ m) (hi : i + m ≤ n)
    (hs : s = i + j) : skPlace n n i (jwAt m j k) = jwAt n s k := by
  subst hs
  rw [jwAt_eq_skPlace m j k hj, skPlace_skPlace n n i j _ hj rfl hi rfl,
    ← jwAt_eq_skPlace n (i + j) k (by omega)]

/-- The projector on the first input bundle passes through the cups of the rotation. -/
private theorem jwAt_fst_mul_cupPlace_twQBandRotSlide (c : ℕ) :
    jwAt (2 * c) 0 c * skPlace (2 * c) (4 * c) (2 * c) (cupThick c) =
      skPlace (2 * c) (4 * c) (2 * c) (cupThick c) * jwAt (4 * c) 0 c :=
  jwAt_mul_skPlace_of_le (2 * c) (4 * c) 0 c (2 * c) (cupThick c) (by omega)
    (by omega) (by omega)

/-- The projector on the second input bundle passes through the cups of the rotation. -/
private theorem jwAt_snd_mul_cupPlace_twQBandRotSlide (c : ℕ) :
    jwAt (2 * c) c c * skPlace (2 * c) (4 * c) (2 * c) (cupThick c) =
      skPlace (2 * c) (4 * c) (2 * c) (cupThick c) * jwAt (4 * c) c c :=
  jwAt_mul_skPlace_of_le (2 * c) (4 * c) c c (2 * c) (cupThick c) (by omega)
    (by omega) (by omega)

/-- The projector on the first output bundle passes through the caps of the rotation. -/
private theorem jwAt_mul_capPlace_fst_twQBandRotSlide (c : ℕ) :
    jwAt (4 * c) (2 * c) c * skPlace (4 * c) (2 * c) 0 (capThick c) =
      skPlace (4 * c) (2 * c) 0 (capThick c) * jwAt (2 * c) 0 c :=
  jwAt_mul_skPlace_of_ge_twQBandRotSlide (4 * c) (2 * c) (2 * c) 0 c 0 (capThick c) (by omega)
    (by omega) (by omega) (by omega)

/-- The projector on the second output bundle passes through the caps of the rotation. -/
private theorem jwAt_mul_capPlace_snd_twQBandRotSlide (c : ℕ) :
    jwAt (4 * c) (3 * c) c * skPlace (4 * c) (2 * c) 0 (capThick c) =
      skPlace (4 * c) (2 * c) 0 (capThick c) * jwAt (2 * c) c c :=
  jwAt_mul_skPlace_of_ge_twQBandRotSlide (4 * c) (2 * c) (3 * c) c c 0 (capThick c) (by omega)
    (by omega) (by omega) (by omega)

/-- A projector passes to the other leg of the caps of the rotation. -/
private theorem jwAt_mul_capPlace_leg_twQBandRotSlide (c : ℕ) :
    jwAt (4 * c) 0 c * skPlace (4 * c) (2 * c) 0 (capThick c) =
      jwAt (4 * c) c c * skPlace (4 * c) (2 * c) 0 (capThick c) := by
  have h := congrArg (skPlace (4 * c) (2 * c) 0) (jwAt_mul_capThick c)
  rw [skPlace_mul (4 * c) (4 * c) (2 * c) 0 _ _ (by omega) (by omega) (by omega),
    skPlace_mul (4 * c) (4 * c) (2 * c) 0 _ _ (by omega) (by omega) (by omega),
    skPlace_jwAt_twQBandRotSlide (4 * c) (2 * c) 0 0 c 0 (by omega) (by omega) (by omega),
    skPlace_jwAt_twQBandRotSlide (4 * c) (2 * c) 0 c c c (by omega) (by omega) (by omega)] at h
  exact h

/-- A projector passes to the other leg of the cups of the rotation. -/
private theorem cupPlace_mul_jwAt_leg_twQBandRotSlide (c : ℕ) :
    skPlace (2 * c) (4 * c) (2 * c) (cupThick c) * jwAt (4 * c) (3 * c) c =
      skPlace (2 * c) (4 * c) (2 * c) (cupThick c) * jwAt (4 * c) (2 * c) c := by
  have h := congrArg (skPlace (2 * c) (4 * c) (2 * c)) (cupThick_mul_jwAt c)
  rw [skPlace_mul (2 * c) (4 * c) (4 * c) (2 * c) _ _ (by omega) (by omega) (by omega),
    skPlace_mul (2 * c) (4 * c) (4 * c) (2 * c) _ _ (by omega) (by omega) (by omega),
    skPlace_jwAt_twQBandRotSlide (4 * c) (2 * c) (2 * c) 0 c (2 * c) (by omega) (by omega)
      (by omega),
    skPlace_jwAt_twQBandRotSlide (4 * c) (2 * c) (2 * c) c c (3 * c) (by omega) (by omega)
      (by omega)] at h
  exact h.symm

/-- The projector on the first of four bundles commutes with a matrix on the two middle
bundles. -/
private theorem jwAt_zero_mul_midPlace_twQBandRotSlide (c : ℕ) (A : SkMat (2 * c) (2 * c)) :
    jwAt (4 * c) 0 c * skPlace (4 * c) (4 * c) c A =
      skPlace (4 * c) (4 * c) c A * jwAt (4 * c) 0 c :=
  jwAt_mul_skPlace_of_le (4 * c) (4 * c) 0 c c A (by omega) (by omega) (by omega)

/-- The projector on the last of four bundles commutes with a matrix on the two middle
bundles. -/
private theorem jwAt_last_mul_midPlace_twQBandRotSlide (c : ℕ) (A : SkMat (2 * c) (2 * c)) :
    jwAt (4 * c) (3 * c) c * skPlace (4 * c) (4 * c) c A =
      skPlace (4 * c) (4 * c) c A * jwAt (4 * c) (3 * c) c :=
  jwAt_mul_skPlace_of_ge_twQBandRotSlide (4 * c) (4 * c) (3 * c) (3 * c) c c A (by omega)
    (by omega) (by omega) (by omega)

/-- A projector on one of the two middle bundles commutes with a placed matrix that commutes
with the projector on the corresponding bundle. -/
private theorem jwAt_mul_midPlace_twQBandRotSlide (c j s : ℕ) (A : SkMat (2 * c) (2 * c))
    (hs : s = c + j) (hj : j + c ≤ 2 * c)
    (h : jwAt (2 * c) j c * A = A * jwAt (2 * c) j c) :
    jwAt (4 * c) s c * skPlace (4 * c) (4 * c) c A =
      skPlace (4 * c) (4 * c) c A * jwAt (4 * c) s c := by
  rw [← skPlace_jwAt_twQBandRotSlide (4 * c) (2 * c) c j c s hj (by omega) hs,
    ← skPlace_mul (4 * c) (4 * c) (4 * c) c _ _ (by omega) (by omega) (by omega),
    ← skPlace_mul (4 * c) (4 * c) (4 * c) c _ _ (by omega) (by omega) (by omega), h]

/-- The chain of rewritings for a projector before the rotation. -/
private theorem rot_in_chain_twQBandRotSlide {m n : ℕ} (j0 j1 : SkMat m m) (U : SkMat m n)
    (W : SkMat n m) (T J0 J1 : SkMat n n) (ha : j0 * U = U * J0) (hb : j1 * U = U * J1)
    (he : J0 * W = J1 * W) (h0 : J0 * T = T * J0) (h1 : J1 * T = T * J1) :
    j0 * (U * T * W) = j1 * (U * T * W) := by
  calc j0 * (U * T * W) = j0 * U * T * W := by simp only [Matrix.mul_assoc]
    _ = U * (J0 * T) * W := by rw [ha]; simp only [Matrix.mul_assoc]
    _ = U * T * (J0 * W) := by rw [h0]; simp only [Matrix.mul_assoc]
    _ = U * (T * J1) * W := by rw [he]; simp only [Matrix.mul_assoc]
    _ = U * J1 * T * W := by rw [← h1]; simp only [Matrix.mul_assoc]
    _ = j1 * (U * T * W) := by rw [← hb]; simp only [Matrix.mul_assoc]

/-- The chain of rewritings for a projector after the rotation. -/
private theorem rot_out_chain_twQBandRotSlide {m n : ℕ} (j0 j1 : SkMat m m) (U : SkMat m n)
    (W : SkMat n m) (T J2 J3 : SkMat n n) (hc : J2 * W = W * j0) (hd : J3 * W = W * j1)
    (hf : U * J3 = U * J2) (h2 : J2 * T = T * J2) (h3 : J3 * T = T * J3) :
    U * T * W * j0 = U * T * W * j1 := by
  calc U * T * W * j0 = U * T * (W * j0) := by simp only [Matrix.mul_assoc]
    _ = U * (T * J2) * W := by rw [← hc]; simp only [Matrix.mul_assoc]
    _ = U * J2 * T * W := by rw [← h2]; simp only [Matrix.mul_assoc]
    _ = U * (J3 * T) * W := by rw [← hf]; simp only [Matrix.mul_assoc]
    _ = U * T * (J3 * W) := by rw [h3]; simp only [Matrix.mul_assoc]
    _ = U * T * W * j1 := by rw [hd]; simp only [Matrix.mul_assoc]

/-- The full twist of either sign commutes with the projector on the first bundle. -/
private theorem jwAt_fst_mul_fullTwist_twQBandRotSlide (c : ℕ) (σ : Bool) :
    jwAt (2 * c) 0 c * (halfTwist c σ * halfTwist c σ) =
      halfTwist c σ * halfTwist c σ * jwAt (2 * c) 0 c := by
  have h1 := jwAt_mul_braidMatrix_thickCross_fst (2 * c) c c 0 σ (by omega)
  have h2 := jwAt_mul_braidMatrix_thickCross_snd (2 * c) c c 0 σ (by omega)
  rw [Nat.zero_add, ← halfTwist_eq_braidMatrix_thickCross] at h1 h2
  rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, h2, Matrix.mul_assoc]

/-- The full twist of either sign commutes with the projector on the second bundle. -/
private theorem jwAt_snd_mul_fullTwist_twQBandRotSlide (c : ℕ) (σ : Bool) :
    jwAt (2 * c) c c * (halfTwist c σ * halfTwist c σ) =
      halfTwist c σ * halfTwist c σ * jwAt (2 * c) c c := by
  have h1 := jwAt_mul_braidMatrix_thickCross_fst (2 * c) c c 0 σ (by omega)
  have h2 := jwAt_mul_braidMatrix_thickCross_snd (2 * c) c c 0 σ (by omega)
  rw [Nat.zero_add, ← halfTwist_eq_braidMatrix_thickCross] at h1 h2
  rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc, h1, Matrix.mul_assoc]

/-- A projector before the rotation of `A` passes to the other edge, if `A` commutes with the
projector on its first bundle. -/
theorem jwAt_mul_bandRot (c : ℕ) (A : SkMat (2 * c) (2 * c))
    (hA : jwAt (2 * c) 0 c * A = A * jwAt (2 * c) 0 c) :
    jwAt (2 * c) 0 c * bandRot c A = jwAt (2 * c) c c * bandRot c A := by
  rw [bandRot]
  exact rot_in_chain_twQBandRotSlide _ _ _ _ _ _ _
    (jwAt_fst_mul_cupPlace_twQBandRotSlide c) (jwAt_snd_mul_cupPlace_twQBandRotSlide c)
    (jwAt_mul_capPlace_leg_twQBandRotSlide c) (jwAt_zero_mul_midPlace_twQBandRotSlide c _)
    (jwAt_mul_midPlace_twQBandRotSlide c 0 c A (by omega) (by omega) hA)

/-- A projector after the rotation of `A` passes to the other edge, if `A` commutes with the
projector on its second bundle. -/
theorem bandRot_mul_jwAt (c : ℕ) (A : SkMat (2 * c) (2 * c))
    (hA : jwAt (2 * c) c c * A = A * jwAt (2 * c) c c) :
    bandRot c A * jwAt (2 * c) 0 c = bandRot c A * jwAt (2 * c) c c := by
  rw [bandRot]
  exact rot_out_chain_twQBandRotSlide _ _ _ _ _ _ _
    (jwAt_mul_capPlace_fst_twQBandRotSlide c) (jwAt_mul_capPlace_snd_twQBandRotSlide c)
    (cupPlace_mul_jwAt_leg_twQBandRotSlide c)
    (jwAt_mul_midPlace_twQBandRotSlide c c (2 * c) A (by omega) (by omega) hA)
    (jwAt_last_mul_midPlace_twQBandRotSlide c _)

/-- A projector before the clasp of either sign passes to the other edge. -/
theorem jwAt_mul_claspSOp (c : ℕ) (σ : Bool) :
    jwAt (2 * c) 0 c * claspSOp c σ = jwAt (2 * c) c c * claspSOp c σ := by
  rw [claspSOp_eq_bandRot]
  exact jwAt_mul_bandRot c _ (jwAt_fst_mul_fullTwist_twQBandRotSlide c σ)

/-- A projector after the clasp of either sign passes to the other edge. -/
theorem claspSOp_mul_jwAt (c : ℕ) (σ : Bool) :
    claspSOp c σ * jwAt (2 * c) 0 c = claspSOp c σ * jwAt (2 * c) c c := by
  rw [claspSOp_eq_bandRot]
  exact bandRot_mul_jwAt c _ (jwAt_snd_mul_fullTwist_twQBandRotSlide c σ)

end AJConjecture
