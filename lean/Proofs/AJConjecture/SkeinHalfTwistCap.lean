import Mathlib
import AJConjecture.SkeinBubble
import AJConjecture.SkeinCapAtComm
import AJConjecture.SkeinCapLegTransfer
import AJConjecture.SkeinHalfTwist
import AJConjecture.SkeinJwAbsorb
import AJConjecture.SkeinJwThickCross
import AJConjecture.SkeinProfileBasic
import AJConjecture.SkeinThickCrossBraid

/-!
# The cabled half twist against a cap between the two bundles

For two bundles of `a + 1` strands, the half twist followed by the cap that joins the two
bundles is the kink `-t^{∓3}` of the capped strands, the two capped strands crossing the other
strands of their own bundles backwards, the cap, and the half twist of the remaining bundles of
`a` strands.

Route (positive sign). Write the bundles as `(x, A')` and `(B', y)`. By
`AJConjecture.cableGen_eq_thickCross`, `AJConjecture.thickGen_add_left` and the form
`σ_0 ⋯ σ_a` of `thickGen 1 (a+1) 0 true`, the half twist is `X(A', B)_1 · X(x, B')_0 · σ_a`. The
last crossing is a kink on the cap (`AJConjecture.crossingF_mul_capAt`); the crossing of `x`
with `B'` moves to the other leg (`AJConjecture.braidMatrix_thickCross_mul_capAt_leg`): `y` crosses
`B'` backwards and the cap is at the position `0`; this braid inside the bundle `B` slides through
`X(A', B)` (`AJConjecture.braidMatrix_mul_thickCross_snd`) and becomes the word
`thickCross a 1 (a+1) false`; then `X(A', B)_1 = X(A', y)_1 · X(A', B')_2`
(`AJConjecture.braidMatrix_thickGen_add_right`), the second factor commutes with the cap and
becomes the half twist of the smaller bundles (`AJConjecture.capAt_mul_braidMatrix_of_le`,
`AJConjecture.thickCross_add_off`), and the first factor moves to the other leg once more: `x`
crosses `A'` backwards and the cap is in the middle. The negative sign is the same computation
with the inverse words.

In the presence of `f ⊗ f` the two backward crossings are absorbed as `t^{∓a}` each
(`AJConjecture.jwAt_mul_braidMatrix_of_inside`), which gives the scalar `-t^{∓(2a+3)}`; and the half
twist commutes with `f ⊗ f` (`AJConjecture.jwAt_mul_braidMatrix_thickCross_fst`,
`AJConjecture.jwAt_mul_braidMatrix_thickCross_snd`).
-/

namespace AJConjecture

/-- The letters of a thick crossing act on the strands of its two bundles. -/
theorem mem_thickCross {a b off : ℕ} {s : Bool} {g : ℕ × Bool}
    (hg : g ∈ thickCross a b off s) : off ≤ g.1 ∧ g.1 + 2 ≤ off + a + b ∧ g.2 = s := by
  cases s
  · simp only [thickCross, thickGen, Bool.false_eq_true, ite_false, List.mem_flatMap,
      List.mem_reverse, List.mem_range, List.mem_map] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    exact ⟨by omega, by omega, rfl⟩
  · simp only [thickCross, thickGen, ite_true, List.mem_flatMap, List.mem_reverse,
      List.mem_range, List.mem_map] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    exact ⟨by omega, by omega, rfl⟩

/-- The number of crossings of a thick crossing. -/
theorem length_thickCross (a b off : ℕ) (s : Bool) :
    (thickCross a b off s).length = a * b := by
  cases s <;> simp [thickCross, thickGen, List.length_flatMap, mul_comm]

/-- The writhe of a word whose letters all have the sign `s`. -/
theorem writhe_eq_of_forall_sign (w : BraidWord) (s : Bool)
    (h : ∀ g ∈ w, g.2 = s) : writhe w = (if s then 1 else -1) * (w.length : ℤ) := by
  induction w with
  | nil => simp [writhe]
  | cons g w ih =>
    have ih' := ih fun g' hg' ↦ h g' (List.mem_cons_of_mem _ hg')
    rw [writhe] at ih' ⊢
    rw [List.map_cons, List.sum_cons, ih', h g List.mem_cons_self, List.length_cons]
    push_cast
    ring

/-- The writhe of a thick crossing. -/
private theorem writhe_thickCross_halfTwistCap (a b off : ℕ) (s : Bool) :
    writhe (thickCross a b off s) = (if s then 1 else -1) * ((a * b : ℕ) : ℤ) := by
  rw [writhe_eq_of_forall_sign _ s fun g hg ↦ (mem_thickCross hg).2.2,
    length_thickCross]

/-- The projectors of the two bundles commute. -/
private theorem commute_jwAt_jwAt_halfTwistCap (c : ℕ) :
    Commute (jwAt (2 * c) 0 c) (jwAt (2 * c) c c) :=
  commute_jwAt_of_commute_tlGenF (2 * c) c _ c fun l _ ↦
    jwAt_commute_tlGenF (2 * c) 0 c (c + l) (Or.inr (by omega))

/-- The half twist is the matrix of the thick crossing of the two bundles. -/
theorem halfTwist_eq_braidMatrix_thickCross (c : ℕ) (s : Bool) :
    halfTwist c s = braidMatrix (2 * c) (thickCross c c 0 s) := by
  rw [halfTwist, cableGen_eq_thickCross]
  rfl

/-- The chain of rewritings of the half twist against a cap, from its eight steps. -/
private theorem halfTwist_cap_chain_halfTwistCap {N n : ℕ} (κ : RatFunc ℚ)
    (S P U σ V V' P₁ P₂ U' : SkMat N N) (Ca C₀ : SkMat N n) (T : SkMat n n)
    (e1 : S = P * (U * σ)) (e2 : σ * Ca = κ • Ca) (e3 : U * Ca = V * C₀)
    (e4 : P * V = V' * P) (e5 : P = P₁ * P₂) (e6 : P₂ * C₀ = C₀ * T)
    (e7 : P₁ * C₀ = U' * Ca) (e8 : V' * U' = U' * V') :
    S * Ca = κ • (U' * V' * Ca * T) := by
  calc S * Ca = P * (U * (σ * Ca)) := by rw [e1]; simp only [Matrix.mul_assoc]
    _ = κ • (P * (U * Ca)) := by rw [e2]; simp only [Matrix.mul_smul]
    _ = κ • (P * V * C₀) := by rw [e3, Matrix.mul_assoc]
    _ = κ • (V' * P * C₀) := by rw [e4]
    _ = κ • (V' * (P₁ * (P₂ * C₀))) := by rw [e5]; simp only [Matrix.mul_assoc]
    _ = κ • (V' * (P₁ * C₀) * T) := by rw [e6]; simp only [Matrix.mul_assoc]
    _ = κ • (V' * U' * Ca * T) := by rw [e7]; simp only [Matrix.mul_assoc]
    _ = κ • (U' * V' * Ca * T) := by rw [e8]

/-- The positive half twist against the cap, in terms of words. -/
private theorem thickGen_mul_capAt_pos_halfTwistCap (a : ℕ) :
    braidMatrix (2 * a + 2) (thickGen (a + 1) (a + 1) 0 true) * capAt (2 * a) a =
      (-(RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ)) •
        (braidMatrix (2 * a + 2) (thickCross 1 a 0 false) *
          braidMatrix (2 * a + 2) (thickCross a 1 (a + 1) false) * capAt (2 * a) a *
            braidMatrix (2 * a) (thickGen a a 0 true)) := by
  refine halfTwist_cap_chain_halfTwistCap _ _ (braidMatrix _ (thickGen a (a + 1) 1 true))
    (braidMatrix _ (thickGen 1 a 0 true)) (crossingF _ (a, true))
    (braidMatrix _ (thickCross a 1 1 false)) _ (braidMatrix _ (thickGen a 1 1 true))
    (braidMatrix _ (thickGen a a 2 true)) _ _ (capAt (2 * a) 0) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [show thickGen (a + 1) (a + 1) 0 true = thickGen (1 + a) (a + 1) 0 true from by
        rw [Nat.add_comm 1 a], thickGen_add_left, braidMatrix_append,
      braidMatrix_thickGen_add_right _ 1 a 1 0]
    simp only [Nat.zero_add]
    rw [show thickGen 1 1 a true = [(a, true)] from rfl, braidMatrix_cons,
      braidMatrix_nil, Matrix.mul_one]
  · exact (crossingF_mul_capAt (2 * a) a true (by omega)).trans (by simp only [↓reduceIte])
  · have h := braidMatrix_thickCross_mul_capAt_leg (2 * a) a 0 true (by omega)
    simp only [Nat.zero_add, Bool.not_true] at h
    exact h
  · have h := braidMatrix_mul_thickCross_snd (2 * a + 2) a (a + 1) 1 true (thickCross a 1 0 false)
      (by omega) fun g hg ↦ by
        have := mem_thickCross hg
        omega
    rw [← thickCross_add_off, ← thickCross_add_off] at h
    simp only [Nat.zero_add] at h
    rw [Nat.add_comm 1 a] at h
    exact h.symm
  · have h := braidMatrix_thickGen_add_right (2 * a + 2) a 1 a 1
    rw [Nat.add_comm 1 a] at h
    exact h
  · have h := capAt_mul_braidMatrix_of_le (2 * a) 0 (thickGen a a 0 true) fun _ _ ↦ Nat.zero_le _
    rw [show (thickGen a a 0 true).map (fun g ↦ (g.1 + 2, g.2)) = thickGen a a 2 true from
      (thickCross_add_off a a 0 2 true).symm] at h
    exact h.symm
  · have h := braidMatrix_thickCross_mul_capAt_leg (2 * a) a 0 false (by omega)
    simp only [Nat.zero_add, Bool.not_false] at h
    exact h.symm
  · refine (braidMatrix_commute_of_far _ _ _ fun g hg g' hg' ↦ ?_).eq.symm
    have h1 := mem_thickCross hg
    have h2 := mem_thickCross hg'
    omega

/-- The statement for the inverse half twist from the statement for the half twist. -/
private theorem inv_halfTwist_cap_of_halfTwistCap {N n : ℕ} (κ κ' : RatFunc ℚ)
    (S Si W W' Wi' : SkMat N N) (C : SkMat N n) (T Ti : SkMat n n)
    (h : S * C = κ • (W * C * T)) (hS : Si * S = 1) (hT : T * Ti = 1)
    (hW : Si * W = W' * Si) (hW' : Wi' * W' = 1) (hκ : κ' * κ = 1) :
    Si * C = κ' • (Wi' * C * Ti) := by
  have h1 : C * Ti = κ • (W' * (Si * C)) := by
    calc C * Ti = Si * S * C * Ti := by rw [hS, Matrix.one_mul]
      _ = Si * (S * C) * Ti := by simp only [Matrix.mul_assoc]
      _ = κ • (Si * W * C * (T * Ti)) := by
          rw [h]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = κ • (W' * (Si * C)) := by
          rw [hW, hT, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  calc Si * C = (κ' * κ) • (Wi' * W' * (Si * C)) := by rw [hκ, hW', one_smul, Matrix.one_mul]
    _ = κ' • (Wi' * (κ • (W' * (Si * C)))) := by
        simp only [Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    _ = κ' • (Wi' * C * Ti) := by rw [← h1, Matrix.mul_assoc]

/-- The negative half twist against the cap, in terms of words. -/
private theorem thickGen_mul_capAt_neg_halfTwistCap (a : ℕ) :
    braidMatrix (2 * a + 2) (thickGen (a + 1) (a + 1) 0 false) * capAt (2 * a) a =
      (-(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ)) •
        (braidMatrix (2 * a + 2) (thickCross 1 a 0 true) *
          braidMatrix (2 * a + 2) (thickCross a 1 (a + 1) true) * capAt (2 * a) a *
            braidMatrix (2 * a) (thickGen a a 0 false)) := by
  refine inv_halfTwist_cap_of_halfTwistCap _ _ _ _ _
    (braidMatrix (2 * a + 2) (thickCross 1 a (a + 1) false) *
      braidMatrix (2 * a + 2) (thickCross a 1 0 false)) _ _ _ _
    (thickGen_mul_capAt_pos_halfTwistCap a) (braidMatrix_thickGen_inv_mul _ _ _ _)
    (braidMatrix_thickGen_mul_inv _ _ _ _) ?_ ?_ ?_
  · have s1 := braidMatrix_mul_thickCross_snd (2 * a + 2) (a + 1) (a + 1) 0 false
      (thickCross 1 a 0 false) (by omega) fun g hg ↦ by
        have := mem_thickCross hg
        omega
    have s2 := braidMatrix_mul_thickCross_fst (2 * a + 2) (a + 1) (a + 1) 0 false
      (thickCross a 1 0 false) (by omega) fun g hg ↦ by
        have := mem_thickCross hg
        omega
    rw [← thickCross_add_off, ← thickCross_add_off] at s1 s2
    simp only [Nat.zero_add] at s1 s2
    change braidMatrix (2 * a + 2) (thickCross (a + 1) (a + 1) 0 false) * _ =
      _ * braidMatrix (2 * a + 2) (thickCross (a + 1) (a + 1) 0 false)
    rw [← Matrix.mul_assoc, ← s1, Matrix.mul_assoc, ← s2, Matrix.mul_assoc]
  · have i1 : braidMatrix (2 * a + 2) (thickCross a 1 (a + 1) true) *
        braidMatrix (2 * a + 2) (thickCross 1 a (a + 1) false) = 1 :=
      braidMatrix_thickGen_mul_inv _ a 1 (a + 1)
    have i2 : braidMatrix (2 * a + 2) (thickCross 1 a 0 true) *
        braidMatrix (2 * a + 2) (thickCross a 1 0 false) = 1 :=
      braidMatrix_thickGen_mul_inv _ 1 a 0
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (braidMatrix _ (thickCross a 1 (a + 1) true)), i1,
      Matrix.one_mul, i2]
  · rw [neg_mul_neg, ← zpow_add₀ RatFunc.X_ne_zero]
    norm_num

/-- The half twist followed by the cap between the bundles, without projectors. -/
theorem halfTwist_mul_skCap (a : ℕ) (s : Bool) :
    halfTwist (a + 1) s * skPlace (2 * (a + 1)) (2 * a) a skCap =
      (if s then -(RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ) else -(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ)) •
        (braidMatrix (2 * (a + 1)) (thickCross 1 a 0 (!s) ++ thickCross a 1 (a + 1) (!s)) *
          skPlace (2 * (a + 1)) (2 * a) a skCap * halfTwist a s) := by
  rw [braidMatrix_append, halfTwist_eq_braidMatrix_thickCross,
    halfTwist_eq_braidMatrix_thickCross]
  cases s
  · exact thickGen_mul_capAt_neg_halfTwistCap a
  · exact thickGen_mul_capAt_pos_halfTwistCap a

/-- The half twist commutes with `f ⊗ f`. -/
theorem halfTwist_mul_twoBundleProj (c : ℕ) (s : Bool) :
    halfTwist c s * twoBundleProj c = twoBundleProj c * halfTwist c s := by
  have h1 := jwAt_mul_braidMatrix_thickCross_fst (2 * c) c c 0 s (by omega)
  have h2 := jwAt_mul_braidMatrix_thickCross_snd (2 * c) c c 0 s (by omega)
  rw [Nat.zero_add] at h1 h2
  have h3 : jwAt (2 * c) 0 c * jwAt (2 * c) c c * braidMatrix (2 * c) (thickCross c c 0 s) =
      braidMatrix (2 * c) (thickCross c c 0 s) * (jwAt (2 * c) c c * jwAt (2 * c) 0 c) := by
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  rw [twoBundleProj, halfTwist_eq_braidMatrix_thickCross, h3,
    (commute_jwAt_jwAt_halfTwistCap c).eq]

/-- The projector `f ⊗ f` absorbs the two backward crossings. -/
private theorem twoBundleProj_mul_braidMatrix_legs_halfTwistCap (a : ℕ) (s : Bool) :
    twoBundleProj (a + 1) *
        braidMatrix (2 * (a + 1)) (thickCross 1 a 0 s ++ thickCross a 1 (a + 1) s) =
      ((RatFunc.X : RatFunc ℚ) ^ ((if s then 1 else -1) * (a : ℤ)) *
        (RatFunc.X : RatFunc ℚ) ^ ((if s then 1 else -1) * (a : ℤ))) • twoBundleProj (a + 1) := by
  have hc := commute_jwAt_jwAt_halfTwistCap (a + 1)
  have hU := jwAt_mul_braidMatrix_of_inside (2 * (a + 1)) 0 (a + 1) (thickCross 1 a 0 s)
    fun g hg ↦ by
      have := mem_thickCross hg
      omega
  have hV := jwAt_mul_braidMatrix_of_inside (2 * (a + 1)) (a + 1) (a + 1)
    (thickCross a 1 (a + 1) s) fun g hg ↦ by
      have := mem_thickCross hg
      omega
  rw [writhe_thickCross_halfTwistCap, Nat.one_mul] at hU
  rw [writhe_thickCross_halfTwistCap, Nat.mul_one] at hV
  rw [twoBundleProj, braidMatrix_append]
  calc jwAt (2 * (a + 1)) 0 (a + 1) * jwAt (2 * (a + 1)) (a + 1) (a + 1) *
        (braidMatrix (2 * (a + 1)) (thickCross 1 a 0 s) *
          braidMatrix (2 * (a + 1)) (thickCross a 1 (a + 1) s))
      = jwAt (2 * (a + 1)) (a + 1) (a + 1) *
          (jwAt (2 * (a + 1)) 0 (a + 1) * braidMatrix (2 * (a + 1)) (thickCross 1 a 0 s)) *
            braidMatrix (2 * (a + 1)) (thickCross a 1 (a + 1) s) := by
        rw [hc.eq]
        simp only [Matrix.mul_assoc]
    _ = (RatFunc.X : RatFunc ℚ) ^ ((if s then 1 else -1) * (a : ℤ)) •
          (jwAt (2 * (a + 1)) 0 (a + 1) * (jwAt (2 * (a + 1)) (a + 1) (a + 1) *
            braidMatrix (2 * (a + 1)) (thickCross a 1 (a + 1) s))) := by
        rw [hU, Matrix.mul_smul, Matrix.smul_mul, ← hc.eq, Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_smul, smul_smul]

/-- The half twist followed by the cap between the bundles, on projectors: the scalar
`-t^{∓(2a+3)}`. -/
theorem twoBundleProj_mul_halfTwist_mul_skCap (a : ℕ) (s : Bool) :
    twoBundleProj (a + 1) * halfTwist (a + 1) s * skPlace (2 * (a + 1)) (2 * a) a skCap =
      (if s then -(RatFunc.X : RatFunc ℚ) ^ (-(2 * (a : ℤ) + 3))
        else -(RatFunc.X : RatFunc ℚ) ^ (2 * (a : ℤ) + 3)) •
        (twoBundleProj (a + 1) * skPlace (2 * (a + 1)) (2 * a) a skCap * halfTwist a s) := by
  rw [Matrix.mul_assoc, halfTwist_mul_skCap, Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc (twoBundleProj (a + 1)), twoBundleProj_mul_braidMatrix_legs_halfTwistCap,
    Matrix.smul_mul, smul_smul, ← Matrix.mul_assoc]
  congr 1
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, one_mul, neg_mul]
    rw [← zpow_add₀ RatFunc.X_ne_zero, ← zpow_add₀ RatFunc.X_ne_zero]
    congr 2
    ring
  · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, neg_mul, one_mul]
    rw [← zpow_add₀ RatFunc.X_ne_zero, ← zpow_add₀ RatFunc.X_ne_zero]
    congr 2
    ring

end AJConjecture
