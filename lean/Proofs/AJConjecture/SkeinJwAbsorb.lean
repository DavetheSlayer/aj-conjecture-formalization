import Mathlib
import AJConjecture.ColoredJones
import AJConjecture.SkeinJwBasic

/-!
# Absorption and locality of the Jones–Wenzl projector

`f_k` is `1` plus a combination of words in the generators of its block, each word containing
a generator on the left and on the right. Hence `f_k` absorbs every projector on a sub-block,
absorbs a crossing inside its block as the scalar `t^{±1}` (and a braid word inside its block as
`t` to the power of the writhe), commutes with every generator outside its block, and is the
placement of the projector of `V^{⊗ k}`. The statements hold for every ambient size, because the
recursion is stationary once `e_{i+k} = 0`.
-/

namespace AJConjecture

/-- Wenzl's recursion, as a rewriting rule. -/
private theorem jwAt_succ_succ_jwAbsorb (n i k : ℕ) :
    jwAt n i (k + 2) = jwAt n i (k + 1) + (quantumInt ((k : ℤ) + 1) / quantumInt ((k : ℤ) + 2)) •
      (jwAt n i (k + 1) * tlGenF n (i + k) * jwAt n i (k + 1)) := by
  rw [jwAt]

/-- `f_k` absorbs a Jones–Wenzl projector on a sub-block, on the right. -/
theorem jwAt_mul_jwAt_of_le (n i k i' k' : ℕ) (hi : i ≤ i') (hk : i' + k' ≤ i + k) :
    jwAt n i k * jwAt n i' k' = jwAt n i k := by
  induction k' using Nat.twoStepInduction with
  | zero => rw [jwAt, Matrix.mul_one]
  | one => rw [jwAt, Matrix.mul_one]
  | more k' _ ih =>
    have ih' := ih (by omega)
    rw [jwAt_succ_succ_jwAbsorb, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ih', jwAt_mul_tlGenF n i k (i' + k') (by omega) (by omega),
      Matrix.zero_mul, smul_zero, add_zero]

/-- `f_k` absorbs a Jones–Wenzl projector on a sub-block, on the left. -/
theorem jwAt_mul_jwAt_of_ge (n i k i' k' : ℕ) (hi : i ≤ i') (hk : i' + k' ≤ i + k) :
    jwAt n i' k' * jwAt n i k = jwAt n i k := by
  induction k' using Nat.twoStepInduction with
  | zero => rw [jwAt, Matrix.one_mul]
  | one => rw [jwAt, Matrix.one_mul]
  | more k' _ ih =>
    have ih' := ih (by omega)
    rw [jwAt_succ_succ_jwAbsorb, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc,
      ih', Matrix.mul_assoc, tlGenF_mul_jwAt n i k (i' + k') (by omega) (by omega),
      Matrix.mul_zero, smul_zero, add_zero]

/-- A crossing inside the block of `f_k` is absorbed on the right as the scalar `t` or `t⁻¹`. -/
theorem jwAt_mul_crossingF (n i k j : ℕ) (s : Bool) (hij : i ≤ j) (hjk : j + 1 < i + k) :
    jwAt n i k * crossingF n (j, s) =
      (if s then (RatFunc.X : RatFunc ℚ) else (RatFunc.X : RatFunc ℚ)⁻¹) • jwAt n i k := by
  cases s
  · rw [crossingF_neg, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      jwAt_mul_tlGenF n i k j hij hjk, smul_zero, add_zero]
    rfl
  · rw [crossingF_pos, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      jwAt_mul_tlGenF n i k j hij hjk, smul_zero, add_zero]
    rfl

/-- A crossing inside the block of `f_k` is absorbed on the left as the scalar `t` or `t⁻¹`. -/
theorem crossingF_mul_jwAt (n i k j : ℕ) (s : Bool) (hij : i ≤ j) (hjk : j + 1 < i + k) :
    crossingF n (j, s) * jwAt n i k =
      (if s then (RatFunc.X : RatFunc ℚ) else (RatFunc.X : RatFunc ℚ)⁻¹) • jwAt n i k := by
  cases s
  · rw [crossingF_neg, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
      tlGenF_mul_jwAt n i k j hij hjk, smul_zero, add_zero]
    rfl
  · rw [crossingF_pos, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
      tlGenF_mul_jwAt n i k j hij hjk, smul_zero, add_zero]
    rfl

/-- A braid word inside the block of `f_k` is absorbed as `t` to the power of its writhe. -/
theorem jwAt_mul_braidMatrix_of_inside (n i k : ℕ) (w : BraidWord)
    (hw : ∀ g ∈ w, i ≤ g.1 ∧ g.1 + 1 < i + k) :
    jwAt n i k * braidMatrix n w = (RatFunc.X : RatFunc ℚ) ^ (writhe w) • jwAt n i k := by
  induction w with
  | nil => rw [braidMatrix_nil, Matrix.mul_one, writhe, List.map_nil, List.sum_nil, zpow_zero,
      one_smul]
  | cons g w ih =>
    obtain ⟨j, s⟩ := g
    have hg := hw (j, s) List.mem_cons_self
    have ih' := ih fun g' hg' ↦ hw g' (List.mem_cons_of_mem _ hg')
    have hcons : braidMatrix n ((j, s) :: w) = crossingF n (j, s) * braidMatrix n w := by
      rw [braidMatrix, List.map_cons, List.prod_cons, braidMatrix]
    have hwr : writhe ((j, s) :: w) = (if s then (1 : ℤ) else -1) + writhe w := by
      rw [writhe, List.map_cons, List.sum_cons, writhe]
    rw [hcons, ← Matrix.mul_assoc, jwAt_mul_crossingF n i k j s hg.1 hg.2, Matrix.smul_mul, ih',
      smul_smul, hwr, zpow_add₀ RatFunc.X_ne_zero]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, zpow_neg, zpow_one]
    · simp only [↓reduceIte, zpow_one]

/-- `f_k` commutes with the generators outside its block. -/
theorem jwAt_commute_tlGenF (n i k j : ℕ) (h : j + 1 < i ∨ i + k ≤ j) :
    Commute (jwAt n i k) (tlGenF n j) := by
  induction k using Nat.twoStepInduction with
  | zero => rw [jwAt]; exact Commute.one_left _
  | one => rw [jwAt]; exact Commute.one_left _
  | more k _ ih =>
    have h1 := ih (by omega)
    have h2 : Commute (tlGenF n (i + k)) (tlGenF n j) := by
      rcases h with h | h
      · exact (tlGenF_commute n j (i + k) (by omega)).symm
      · exact tlGenF_commute n (i + k) j (by omega)
    rw [jwAt_succ_succ_jwAbsorb]
    exact h1.add_left (((h1.mul_left h2).mul_left h1).smul_left _)

/-- `f_j` at `i` in `V^{⊗ n}` is the placement of `f_j` at `0` in any `V^{⊗ m}` that contains its
block. -/
private theorem jwAt_eq_skPlace_of_le_jwAbsorb (n i m : ℕ) (h : i + m ≤ n) :
    ∀ j : ℕ, j ≤ m → jwAt n i j = skPlace n n i (jwAt m 0 j)
  | 0, _ => by rw [jwAt, jwAt, skPlace_one n i m h]
  | 1, _ => by rw [jwAt, jwAt, skPlace_one n i m h]
  | j + 2, hj => by
    have ih := jwAt_eq_skPlace_of_le_jwAbsorb n i m h (j + 1) (by omega)
    have he : skPlace n n i (tlGenF m (0 + j)) = tlGenF n (i + j) := by
      rw [tlGenF_eq_skPlace m, skPlace_skPlace n n i (0 + j) (tlGenF 2 0) (by omega) rfl h rfl,
        Nat.zero_add, ← tlGenF_eq_skPlace]
    rw [jwAt_succ_succ_jwAbsorb, jwAt_succ_succ_jwAbsorb, skPlace_add, skPlace_smul,
      skPlace_mul n n n i _ _ h rfl rfl, skPlace_mul n n n i _ _ h rfl rfl, he, ← ih]

/-- `f_k` on the factors `i, …, i + k - 1` is the projector of `V^{⊗ k}` placed at `i`. -/
theorem jwAt_eq_skPlace (n i k : ℕ) (h : i + k ≤ n) :
    jwAt n i k = skPlace n n i (jwAt k 0 k) :=
  jwAt_eq_skPlace_of_le_jwAbsorb n i k h k le_rfl

end AJConjecture
