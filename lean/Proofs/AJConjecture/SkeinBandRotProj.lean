import Mathlib
import AJConjecture.SkeinTurnbackBasic
import AJConjecture.SkeinHalfTwistCap
import AJConjecture.SkeinBandClasp
import AJConjecture.SkeinJwCapThick
import AJConjecture.SkeinJwThickCross

/-!
# Projectors and the rotation

The rotation commutes with the compression by `f ⊗ f`: `(f ⊗ f) · rot(X) · (f ⊗ f) = rot((f ⊗ f) X
(f ⊗ f))`.
The projector on the first input bundle commutes with the cups and with `X` (disjoint windows,
`AJConjecture.jwAt_eq_skPlace` and `AJConjecture.skPlace_mul_skPlace_comm`), passes to the other leg
of the nest of caps (`AJConjecture.jwAt_mul_capThick`) and so acts on the first output bundle of
`X`; the projector on the second input bundle acts on the first input bundle of `X`; and
symmetrically the two output projectors act on the second bundle of `X` on both sides
(`AJConjecture.cupThick_mul_jwAt`).

For the clasp, a projector on one edge passes to the other edge: on the input side it goes
around the nest of caps, and then commutes with the full twist `Σ_c²`
(`AJConjecture.jwAt_mul_braidMatrix_thickCross_fst` and
`AJConjecture.jwAt_mul_braidMatrix_thickCross_snd`,
twice) and with the cups; symmetrically on the output side.
-/

namespace AJConjecture

/-- A projector on the right of a placed matrix commutes with it; its position `i` becomes
`i'`. -/
private theorem jwAt_mul_skPlace_of_ge_bandRotProj (n n' i i' k j : ℕ) {p q : ℕ} (X : SkMat p q)
    (h : j + p ≤ i) (hi : i + k ≤ n) (hn : n + q = n' + p) (hi' : i' + p = i + q) :
    jwAt n i k * skPlace n n' j X = skPlace n n' j X * jwAt n' i' k :=
  jwAt_mul_eq_mul_jwAt n n' i i' _ k fun l _ ↦ by
    rw [tlGenF_mul_skPlace_of_ge n n' (i + l) j X (by omega) (by omega) hn,
      show i + l + q - p = i' + l from by omega]

/-- Two projectors on disjoint blocks commute. -/
private theorem jwAt_mul_jwAt_comm_bandRotProj (n i k i' k' : ℕ) (h : i + k ≤ i') :
    jwAt n i k * jwAt n i' k' = jwAt n i' k' * jwAt n i k :=
  (jwAt_mul_eq_mul_jwAt n n i' i' (jwAt n i k) k' fun l _ ↦
    (jwAt_commute_tlGenF n i k (i' + l) (Or.inr (by omega))).eq.symm).symm

/-- A placed projector is a projector. -/
private theorem skPlace_jwAt_bandRotProj (n m i j k s : ℕ) (hj : j + k ≤ m) (hi : i + m ≤ n)
    (hs : s = i + j) : skPlace n n i (jwAt m j k) = jwAt n s k := by
  subst hs
  rw [jwAt_eq_skPlace m j k hj, skPlace_skPlace n n i j _ hj rfl hi rfl,
    ← jwAt_eq_skPlace n (i + j) k (by omega)]

/-- The projector on the first input bundle passes through the cups of the rotation. -/
private theorem jwAt_fst_mul_cupPlace_bandRotProj (c : ℕ) :
    jwAt (2 * c) 0 c * skPlace (2 * c) (4 * c) (2 * c) (cupThick c) =
      skPlace (2 * c) (4 * c) (2 * c) (cupThick c) * jwAt (4 * c) 0 c :=
  jwAt_mul_skPlace_of_le (2 * c) (4 * c) 0 c (2 * c) (cupThick c) (by omega)
    (by omega) (by omega)

/-- The projector on the second input bundle passes through the cups of the rotation. -/
private theorem jwAt_snd_mul_cupPlace_bandRotProj (c : ℕ) :
    jwAt (2 * c) c c * skPlace (2 * c) (4 * c) (2 * c) (cupThick c) =
      skPlace (2 * c) (4 * c) (2 * c) (cupThick c) * jwAt (4 * c) c c :=
  jwAt_mul_skPlace_of_le (2 * c) (4 * c) c c (2 * c) (cupThick c) (by omega)
    (by omega) (by omega)

/-- The projector on the first output bundle passes through the caps of the rotation. -/
private theorem jwAt_mul_capPlace_fst_bandRotProj (c : ℕ) :
    jwAt (4 * c) (2 * c) c * skPlace (4 * c) (2 * c) 0 (capThick c) =
      skPlace (4 * c) (2 * c) 0 (capThick c) * jwAt (2 * c) 0 c :=
  jwAt_mul_skPlace_of_ge_bandRotProj (4 * c) (2 * c) (2 * c) 0 c 0 (capThick c) (by omega)
    (by omega) (by omega) (by omega)

/-- The projector on the second output bundle passes through the caps of the rotation. -/
private theorem jwAt_mul_capPlace_snd_bandRotProj (c : ℕ) :
    jwAt (4 * c) (3 * c) c * skPlace (4 * c) (2 * c) 0 (capThick c) =
      skPlace (4 * c) (2 * c) 0 (capThick c) * jwAt (2 * c) c c :=
  jwAt_mul_skPlace_of_ge_bandRotProj (4 * c) (2 * c) (3 * c) c c 0 (capThick c) (by omega)
    (by omega) (by omega) (by omega)

/-- A projector passes to the other leg of the caps of the rotation. -/
private theorem jwAt_mul_capPlace_leg_bandRotProj (c : ℕ) :
    jwAt (4 * c) 0 c * skPlace (4 * c) (2 * c) 0 (capThick c) =
      jwAt (4 * c) c c * skPlace (4 * c) (2 * c) 0 (capThick c) := by
  have h := congrArg (skPlace (4 * c) (2 * c) 0) (jwAt_mul_capThick c)
  rw [skPlace_mul (4 * c) (4 * c) (2 * c) 0 _ _ (by omega) (by omega) (by omega),
    skPlace_mul (4 * c) (4 * c) (2 * c) 0 _ _ (by omega) (by omega) (by omega),
    skPlace_jwAt_bandRotProj (4 * c) (2 * c) 0 0 c 0 (by omega) (by omega) (by omega),
    skPlace_jwAt_bandRotProj (4 * c) (2 * c) 0 c c c (by omega) (by omega) (by omega)] at h
  exact h

/-- A projector passes to the other leg of the cups of the rotation. -/
private theorem cupPlace_mul_jwAt_leg_bandRotProj (c : ℕ) :
    skPlace (2 * c) (4 * c) (2 * c) (cupThick c) * jwAt (4 * c) (3 * c) c =
      skPlace (2 * c) (4 * c) (2 * c) (cupThick c) * jwAt (4 * c) (2 * c) c := by
  have h := congrArg (skPlace (2 * c) (4 * c) (2 * c)) (cupThick_mul_jwAt c)
  rw [skPlace_mul (2 * c) (4 * c) (4 * c) (2 * c) _ _ (by omega) (by omega) (by omega),
    skPlace_mul (2 * c) (4 * c) (4 * c) (2 * c) _ _ (by omega) (by omega) (by omega),
    skPlace_jwAt_bandRotProj (4 * c) (2 * c) (2 * c) 0 c (2 * c) (by omega) (by omega) (by omega),
    skPlace_jwAt_bandRotProj (4 * c) (2 * c) (2 * c) c c (3 * c) (by omega) (by omega)
      (by omega)] at h
  exact h.symm

/-- The projector on the first of four bundles commutes with a matrix on the two middle
bundles. -/
private theorem jwAt_zero_mul_midPlace_bandRotProj (c : ℕ) (A : SkMat (2 * c) (2 * c)) :
    jwAt (4 * c) 0 c * skPlace (4 * c) (4 * c) c A =
      skPlace (4 * c) (4 * c) c A * jwAt (4 * c) 0 c :=
  jwAt_mul_skPlace_of_le (4 * c) (4 * c) 0 c c A (by omega) (by omega) (by omega)

/-- The projector on the last of four bundles commutes with a matrix on the two middle
bundles. -/
private theorem jwAt_last_mul_midPlace_bandRotProj (c : ℕ) (A : SkMat (2 * c) (2 * c)) :
    jwAt (4 * c) (3 * c) c * skPlace (4 * c) (4 * c) c A =
      skPlace (4 * c) (4 * c) c A * jwAt (4 * c) (3 * c) c :=
  jwAt_mul_skPlace_of_ge_bandRotProj (4 * c) (4 * c) (3 * c) (3 * c) c c A (by omega) (by omega)
    (by omega) (by omega)

/-- Moving the first and the last of five elements to the other end. -/
private theorem mul_comm_chain_bandRotProj {M : Type*} [Monoid M] (a b x p q : M)
    (hab : a * b = b * a) (hax : a * x = x * a) (hap : a * p = p * a) (haq : a * q = q * a)
    (hqb : q * b = b * q) (hqx : q * x = x * q) (hqp : q * p = p * q) :
    a * b * x * p * q = q * (b * x * p) * a := by
  calc a * b * x * p * q = b * (a * x) * p * q := by rw [hab]; simp only [mul_assoc]
    _ = b * x * (a * p) * q := by rw [hax]; simp only [mul_assoc]
    _ = b * x * p * (a * q) := by rw [hap]; simp only [mul_assoc]
    _ = b * x * (p * q) * a := by rw [haq]; simp only [mul_assoc]
    _ = b * (x * q) * p * a := by rw [← hqp]; simp only [mul_assoc]
    _ = b * q * x * p * a := by rw [← hqx]; simp only [mul_assoc]
    _ = q * (b * x * p) * a := by rw [← hqb]; simp only [mul_assoc]

/-- The chain of rewritings for the compression of a rotation. -/
private theorem bandRot_compress_chain_bandRotProj {m n : ℕ} (j0 j1 : SkMat m m) (U : SkMat m n)
    (W : SkMat n m) (X J0 J1 J2 J3 : SkMat n n) (ha : j0 * U = U * J0) (hb : j1 * U = U * J1)
    (hc : J2 * W = W * j0) (hd : J3 * W = W * j1) (he : J0 * W = J1 * W) (hf : U * J3 = U * J2)
    (h01 : J0 * J1 = J1 * J0) (h0X : J0 * X = X * J0) (h02 : J0 * J2 = J2 * J0)
    (h03 : J0 * J3 = J3 * J0) (h31 : J3 * J1 = J1 * J3) (h3X : J3 * X = X * J3)
    (h32 : J3 * J2 = J2 * J3) (h12 : J1 * J2 = J2 * J1) :
    j0 * j1 * (U * X * W) * (j0 * j1) = U * (J1 * J2 * X * (J1 * J2)) * W := by
  have hm : J0 * J1 * X * J2 * J3 = J3 * (J1 * X * J2) * J0 :=
    mul_comm_chain_bandRotProj J0 J1 X J2 J3 h01 h0X h02 h03 h31 h3X h32
  calc j0 * j1 * (U * X * W) * (j0 * j1) = j0 * (j1 * U) * X * (W * j0) * j1 := by
        simp only [Matrix.mul_assoc]
    _ = j0 * U * J1 * X * J2 * (W * j1) := by rw [hb, ← hc]; simp only [Matrix.mul_assoc]
    _ = U * (J0 * J1 * X * J2 * J3) * W := by rw [ha, ← hd]; simp only [Matrix.mul_assoc]
    _ = U * J3 * (J1 * X * J2) * (J0 * W) := by rw [hm]; simp only [Matrix.mul_assoc]
    _ = U * (J2 * J1) * X * (J2 * J1) * W := by rw [hf, he]; simp only [Matrix.mul_assoc]
    _ = U * (J1 * J2 * X * (J1 * J2)) * W := by rw [← h12]; simp only [Matrix.mul_assoc]

/-- The rotation commutes with the compression by `f ⊗ f`. -/
theorem twoBundleProj_mul_bandRot_mul_twoBundleProj (c : ℕ) (A : SkMat (2 * c) (2 * c)) :
    twoBundleProj c * bandRot c A * twoBundleProj c =
      bandRot c (twoBundleProj c * A * twoBundleProj c) := by
  have hPl : skPlace (4 * c) (4 * c) c (jwAt (2 * c) 0 c * jwAt (2 * c) c c * A *
      (jwAt (2 * c) 0 c * jwAt (2 * c) c c)) =
      jwAt (4 * c) c c * jwAt (4 * c) (2 * c) c * skPlace (4 * c) (4 * c) c A *
        (jwAt (4 * c) c c * jwAt (4 * c) (2 * c) c) := by
    rw [skPlace_mul (4 * c) (4 * c) (4 * c) c _ _ (by omega) (by omega) (by omega),
      skPlace_mul (4 * c) (4 * c) (4 * c) c _ _ (by omega) (by omega) (by omega),
      skPlace_mul (4 * c) (4 * c) (4 * c) c _ _ (by omega) (by omega) (by omega),
      skPlace_jwAt_bandRotProj (4 * c) (2 * c) c 0 c c (by omega) (by omega) (by omega),
      skPlace_jwAt_bandRotProj (4 * c) (2 * c) c c c (2 * c) (by omega) (by omega) (by omega)]
  rw [twoBundleProj, bandRot, bandRot, hPl]
  exact bandRot_compress_chain_bandRotProj _ _ _ _ _ _ _ _ _
    (jwAt_fst_mul_cupPlace_bandRotProj c) (jwAt_snd_mul_cupPlace_bandRotProj c)
    (jwAt_mul_capPlace_fst_bandRotProj c) (jwAt_mul_capPlace_snd_bandRotProj c)
    (jwAt_mul_capPlace_leg_bandRotProj c) (cupPlace_mul_jwAt_leg_bandRotProj c)
    (jwAt_mul_jwAt_comm_bandRotProj _ _ _ _ _ (by omega))
    (jwAt_zero_mul_midPlace_bandRotProj c A)
    (jwAt_mul_jwAt_comm_bandRotProj _ _ _ _ _ (by omega))
    (jwAt_mul_jwAt_comm_bandRotProj _ _ _ _ _ (by omega))
    (jwAt_mul_jwAt_comm_bandRotProj _ _ _ _ _ (by omega)).symm
    (jwAt_last_mul_midPlace_bandRotProj c A)
    (jwAt_mul_jwAt_comm_bandRotProj _ _ _ _ _ (by omega)).symm
    (jwAt_mul_jwAt_comm_bandRotProj _ _ _ _ _ (by omega))

/-- The full twist commutes with the projector on the first bundle. -/
private theorem jwAt_fst_mul_fullTwist_bandRotProj (c : ℕ) :
    jwAt (2 * c) 0 c * (halfTwist c true * halfTwist c true) =
      halfTwist c true * halfTwist c true * jwAt (2 * c) 0 c := by
  have h1 := jwAt_mul_braidMatrix_thickCross_fst (2 * c) c c 0 true (by omega)
  have h2 := jwAt_mul_braidMatrix_thickCross_snd (2 * c) c c 0 true (by omega)
  rw [Nat.zero_add, ← halfTwist_eq_braidMatrix_thickCross] at h1 h2
  rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, h2, Matrix.mul_assoc]

/-- The full twist commutes with the projector on the second bundle. -/
private theorem jwAt_snd_mul_fullTwist_bandRotProj (c : ℕ) :
    jwAt (2 * c) c c * (halfTwist c true * halfTwist c true) =
      halfTwist c true * halfTwist c true * jwAt (2 * c) c c := by
  have h1 := jwAt_mul_braidMatrix_thickCross_fst (2 * c) c c 0 true (by omega)
  have h2 := jwAt_mul_braidMatrix_thickCross_snd (2 * c) c c 0 true (by omega)
  rw [Nat.zero_add, ← halfTwist_eq_braidMatrix_thickCross] at h1 h2
  rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc, h1, Matrix.mul_assoc]

/-- A projector on one of the two middle bundles commutes with the placed full twist. -/
private theorem jwAt_mul_midPlace_fullTwist_bandRotProj (c j s : ℕ) (hs : s = c + j)
    (hj : j + c ≤ 2 * c)
    (h : jwAt (2 * c) j c * (halfTwist c true * halfTwist c true) =
      halfTwist c true * halfTwist c true * jwAt (2 * c) j c) :
    jwAt (4 * c) s c * skPlace (4 * c) (4 * c) c (halfTwist c true * halfTwist c true) =
      skPlace (4 * c) (4 * c) c (halfTwist c true * halfTwist c true) * jwAt (4 * c) s c := by
  rw [← skPlace_jwAt_bandRotProj (4 * c) (2 * c) c j c s hj (by omega) hs,
    ← skPlace_mul (4 * c) (4 * c) (4 * c) c _ _ (by omega) (by omega) (by omega),
    ← skPlace_mul (4 * c) (4 * c) (4 * c) c _ _ (by omega) (by omega) (by omega), h]

/-- The chain of rewritings for a projector before the clasp. -/
private theorem clasp_in_chain_bandRotProj {m n : ℕ} (j0 j1 : SkMat m m) (U : SkMat m n)
    (W : SkMat n m) (T J0 J1 : SkMat n n) (ha : j0 * U = U * J0) (hb : j1 * U = U * J1)
    (he : J0 * W = J1 * W) (h0 : J0 * T = T * J0) (h1 : J1 * T = T * J1) :
    j0 * (U * T * W) = j1 * (U * T * W) := by
  calc j0 * (U * T * W) = j0 * U * T * W := by simp only [Matrix.mul_assoc]
    _ = U * (J0 * T) * W := by rw [ha]; simp only [Matrix.mul_assoc]
    _ = U * T * (J0 * W) := by rw [h0]; simp only [Matrix.mul_assoc]
    _ = U * (T * J1) * W := by rw [he]; simp only [Matrix.mul_assoc]
    _ = U * J1 * T * W := by rw [← h1]; simp only [Matrix.mul_assoc]
    _ = j1 * (U * T * W) := by rw [← hb]; simp only [Matrix.mul_assoc]

/-- The chain of rewritings for a projector after the clasp. -/
private theorem clasp_out_chain_bandRotProj {m n : ℕ} (j0 j1 : SkMat m m) (U : SkMat m n)
    (W : SkMat n m) (T J2 J3 : SkMat n n) (hc : J2 * W = W * j0) (hd : J3 * W = W * j1)
    (hf : U * J3 = U * J2) (h2 : J2 * T = T * J2) (h3 : J3 * T = T * J3) :
    U * T * W * j0 = U * T * W * j1 := by
  calc U * T * W * j0 = U * T * (W * j0) := by simp only [Matrix.mul_assoc]
    _ = U * (T * J2) * W := by rw [← hc]; simp only [Matrix.mul_assoc]
    _ = U * J2 * T * W := by rw [← h2]; simp only [Matrix.mul_assoc]
    _ = U * (J3 * T) * W := by rw [← hf]; simp only [Matrix.mul_assoc]
    _ = U * T * (J3 * W) := by rw [h3]; simp only [Matrix.mul_assoc]
    _ = U * T * W * j1 := by rw [hd]; simp only [Matrix.mul_assoc]

/-- A projector before the clasp passes to the other edge. -/
theorem jwAt_mul_bandClaspOp (c : ℕ) :
    jwAt (2 * c) 0 c * bandClaspOp c = jwAt (2 * c) c c * bandClaspOp c := by
  rw [bandClaspOp, bandRot]
  exact clasp_in_chain_bandRotProj _ _ _ _ _ _ _
    (jwAt_fst_mul_cupPlace_bandRotProj c) (jwAt_snd_mul_cupPlace_bandRotProj c)
    (jwAt_mul_capPlace_leg_bandRotProj c) (jwAt_zero_mul_midPlace_bandRotProj c _)
    (jwAt_mul_midPlace_fullTwist_bandRotProj c 0 c (by omega) (by omega)
      (jwAt_fst_mul_fullTwist_bandRotProj c))

/-- A projector after the clasp passes to the other edge. -/
theorem bandClaspOp_mul_jwAt (c : ℕ) :
    bandClaspOp c * jwAt (2 * c) 0 c = bandClaspOp c * jwAt (2 * c) c c := by
  rw [bandClaspOp, bandRot]
  exact clasp_out_chain_bandRotProj _ _ _ _ _ _ _
    (jwAt_mul_capPlace_fst_bandRotProj c) (jwAt_mul_capPlace_snd_bandRotProj c)
    (cupPlace_mul_jwAt_leg_bandRotProj c)
    (jwAt_mul_midPlace_fullTwist_bandRotProj c c (2 * c) (by omega) (by omega)
      (jwAt_snd_mul_fullTwist_bandRotProj c))
    (jwAt_last_mul_midPlace_bandRotProj c _)

end AJConjecture
