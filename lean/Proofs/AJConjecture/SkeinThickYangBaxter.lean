import Mathlib
import AJConjecture.SkeinCapLegTransfer
import AJConjecture.SkeinThickCrossTlBase
import AJConjecture.SkeinThickGenInv

/-!
# The braid relation for bundles

Three bundles of `a`, `b`, `c` strands: crossing the first with the second, then with the
third, then the second with the third is the same as crossing the second with the third first.
For positive crossings: induction on the three thicknesses from the braid relation and far
commutation of single crossings, with the splitting lemmas. For negative crossings
(`thickCross x y off false` is the inverse of `thickGen y x off true`): invert both sides of the
positive relation for the bundles `c`, `b`, `a`.
-/

namespace AJConjecture

/-- A thick crossing commutes with a thick crossing that starts on the right of its window. -/
private theorem braidMatrix_thickGen_commute_thickYangBaxter (n a b off a' b' off' : ℕ)
    (h : off + a + b ≤ off') :
    Commute (braidMatrix n (thickGen a b off true)) (braidMatrix n (thickGen a' b' off' true)) :=
  braidMatrix_commute_of_far n _ _ fun g hg g' hg' ↦ by
    have h1 := mem_thickGen_true hg
    have h2 := mem_thickGen_true hg'
    omega

/-- The crossing of an empty bundle with a bundle is the identity. -/
private theorem braidMatrix_thickGen_zero_left_thickYangBaxter (n b off : ℕ) :
    braidMatrix n (thickGen 0 b off true) = 1 :=
  braidMatrix_nil n

/-- The crossing of a bundle with an empty bundle is the identity. -/
private theorem braidMatrix_thickGen_zero_right_thickYangBaxter (n a off : ℕ) :
    braidMatrix n (thickGen a 0 off true) = 1 := by
  have h0 : thickGen a 0 off true = [] := List.flatMap_eq_nil_iff.mpr fun _ _ ↦ rfl
  rw [h0, braidMatrix_nil]

/-- The Yang–Baxter relation is compatible with splitting the first bundle (in a monoid). -/
private theorem mul_split_first_thickYangBaxter {M : Type*} [Monoid M]
    {p₁ p₂ q₁ q₂ r rm r' q₁' q₂' p₁' p₂' : M}
    (h1 : p₁ * q₁ * r = rm * q₁' * p₁') (h2 : p₂ * q₂ * rm = r' * q₂' * p₂')
    (k1 : Commute p₁ q₂) (k2 : Commute p₂' q₁') :
    p₂ * p₁ * (q₂ * q₁) * r = r' * (q₂' * q₁') * (p₂' * p₁') := by
  calc p₂ * p₁ * (q₂ * q₁) * r = p₂ * (p₁ * q₂) * q₁ * r := by simp only [mul_assoc]
    _ = p₂ * q₂ * (p₁ * q₁ * r) := by
        rw [k1.eq]
        simp only [mul_assoc]
    _ = p₂ * q₂ * rm * q₁' * p₁' := by
        rw [h1]
        simp only [mul_assoc]
    _ = r' * q₂' * (p₂' * q₁') * p₁' := by
        rw [h2]
        simp only [mul_assoc]
    _ = r' * (q₂' * q₁') * (p₂' * p₁') := by
        rw [k2.eq]
        simp only [mul_assoc]

/-- The Yang–Baxter relation is compatible with splitting the second bundle (in a monoid). -/
private theorem mul_split_second_thickYangBaxter {M : Type*} [Monoid M]
    {p₁ p₂ q qm q' r₁ r₂ r₁' r₂' p₁' p₂' : M}
    (h1 : p₁ * qm * r₁ = r₁' * q' * p₁') (h2 : p₂ * q * r₂ = r₂' * qm * p₂')
    (k1 : Commute p₁ r₂') (k2 : Commute p₂' r₁) :
    p₁ * p₂ * q * (r₂ * r₁) = r₂' * r₁' * q' * (p₁' * p₂') := by
  calc p₁ * p₂ * q * (r₂ * r₁) = p₁ * (p₂ * q * r₂) * r₁ := by simp only [mul_assoc]
    _ = p₁ * r₂' * qm * (p₂' * r₁) := by
        rw [h2]
        simp only [mul_assoc]
    _ = r₂' * (p₁ * qm * r₁) * p₂' := by
        rw [k1.eq, k2.eq]
        simp only [mul_assoc]
    _ = r₂' * r₁' * q' * (p₁' * p₂') := by
        rw [h1]
        simp only [mul_assoc]

/-- The Yang–Baxter relation is compatible with splitting the third bundle (in a monoid). -/
private theorem mul_split_third_thickYangBaxter {M : Type*} [Monoid M]
    {p pm p' q₁ q₂ q₁' q₂' r₁ r₂ r₁' r₂' : M}
    (h1 : p * q₁ * r₁ = r₁' * q₁' * pm) (h2 : pm * q₂ * r₂ = r₂' * q₂' * p')
    (k1 : Commute q₂ r₁) (k2 : Commute q₁' r₂') :
    p * (q₁ * q₂) * (r₁ * r₂) = r₁' * r₂' * (q₁' * q₂') * p' := by
  calc p * (q₁ * q₂) * (r₁ * r₂) = p * q₁ * (q₂ * r₁) * r₂ := by simp only [mul_assoc]
    _ = p * q₁ * r₁ * q₂ * r₂ := by
        rw [k1.eq]
        simp only [mul_assoc]
    _ = r₁' * q₁' * (pm * q₂ * r₂) := by
        rw [h1]
        simp only [mul_assoc]
    _ = r₁' * (q₁' * r₂') * q₂' * p' := by
        rw [h2]
        simp only [mul_assoc]
    _ = r₁' * r₂' * (q₁' * q₂') * p' := by
        rw [k2.eq]
        simp only [mul_assoc]

/-- Inverting both sides of an equality of triple products (in a monoid). -/
private theorem mul_inv_triple_thickYangBaxter {M : Type*} [Monoid M]
    {p₁ p₂ p₃ q₁ q₂ q₃ p₁' p₂' p₃' q₁' q₂' q₃' : M} (h : p₁ * p₂ * p₃ = q₁ * q₂ * q₃)
    (hp₁ : p₁ * p₁' = 1) (hp₂ : p₂ * p₂' = 1) (hp₃ : p₃ * p₃' = 1)
    (hq₁ : q₁' * q₁ = 1) (hq₂ : q₂' * q₂ = 1) (hq₃ : q₃' * q₃ = 1) :
    p₃' * p₂' * p₁' = q₃' * q₂' * q₁' := by
  have hL : p₁ * p₂ * p₃ * (p₃' * p₂' * p₁') = 1 := by
    calc p₁ * p₂ * p₃ * (p₃' * p₂' * p₁') = p₁ * (p₂ * (p₃ * p₃') * p₂') * p₁' := by
          simp only [mul_assoc]
      _ = 1 := by rw [hp₃, mul_one, hp₂, mul_one, hp₁]
  have hR : q₃' * q₂' * q₁' * (q₁ * q₂ * q₃) = 1 := by
    calc q₃' * q₂' * q₁' * (q₁ * q₂ * q₃) = q₃' * (q₂' * (q₁' * q₁) * q₂) * q₃ := by
          simp only [mul_assoc]
      _ = 1 := by rw [hq₁, mul_one, hq₂, mul_one, hq₃]
  calc p₃' * p₂' * p₁' = q₃' * q₂' * q₁' * (q₁ * q₂ * q₃) * (p₃' * p₂' * p₁') := by
        rw [hR, one_mul]
    _ = q₃' * q₂' * q₁' := by
        rw [mul_assoc (q₃' * q₂' * q₁') (q₁ * q₂ * q₃), ← h, hL, mul_one]

/-- The Yang–Baxter relation for positive thick crossings of bundles of `a`, `b`, `c` strands
at the position `off`. -/
private def ThickYangBaxterPos (n a b c off : ℕ) : Prop :=
  braidMatrix n (thickGen a b off true) * braidMatrix n (thickGen a c (off + b) true) *
      braidMatrix n (thickGen b c off true) =
    braidMatrix n (thickGen b c (off + a) true) * braidMatrix n (thickGen a c off true) *
      braidMatrix n (thickGen a b (off + c) true)

/-- The positive relation for a split first bundle. -/
private theorem thickYangBaxterPos_add_first (n a₁ a₂ b c off : ℕ)
    (h1 : ThickYangBaxterPos n a₁ b c off) (h2 : ThickYangBaxterPos n a₂ b c (off + a₁)) :
    ThickYangBaxterPos n (a₁ + a₂) b c off := by
  unfold ThickYangBaxterPos at h1 h2 ⊢
  rw [add_right_comm off a₁ b, add_right_comm off a₁ c] at h2
  rw [thickGen_add_left a₁ a₂ b off, braidMatrix_append, thickGen_add_left a₁ a₂ c (off + b),
    braidMatrix_append, thickGen_add_left a₁ a₂ c off, braidMatrix_append,
    thickGen_add_left a₁ a₂ b (off + c), braidMatrix_append, ← add_assoc]
  exact mul_split_first_thickYangBaxter h1 h2
    (braidMatrix_thickGen_commute_thickYangBaxter n _ _ _ _ _ _ (by omega))
    (braidMatrix_thickGen_commute_thickYangBaxter n _ _ _ _ _ _ (by omega)).symm

/-- The positive relation for a split second bundle. -/
private theorem thickYangBaxterPos_add_second (n a b₁ b₂ c off : ℕ)
    (h1 : ThickYangBaxterPos n a b₁ c off) (h2 : ThickYangBaxterPos n a b₂ c (off + b₁)) :
    ThickYangBaxterPos n a (b₁ + b₂) c off := by
  unfold ThickYangBaxterPos at h1 h2 ⊢
  rw [add_right_comm off b₁ a, add_right_comm off b₁ c] at h2
  rw [braidMatrix_thickGen_add_right n a b₁ b₂ off, thickGen_add_left b₁ b₂ c off,
    braidMatrix_append, thickGen_add_left b₁ b₂ c (off + a), braidMatrix_append,
    braidMatrix_thickGen_add_right n a b₁ b₂ (off + c), ← add_assoc]
  exact mul_split_second_thickYangBaxter h1 h2
    (braidMatrix_thickGen_commute_thickYangBaxter n _ _ _ _ _ _ (by omega))
    (braidMatrix_thickGen_commute_thickYangBaxter n _ _ _ _ _ _ (by omega)).symm

/-- The positive relation for a split third bundle. -/
private theorem thickYangBaxterPos_add_third (n a b c₁ c₂ off : ℕ)
    (h1 : ThickYangBaxterPos n a b c₁ off) (h2 : ThickYangBaxterPos n a b c₂ (off + c₁)) :
    ThickYangBaxterPos n a b (c₁ + c₂) off := by
  unfold ThickYangBaxterPos at h1 h2 ⊢
  rw [add_right_comm off c₁ b, add_right_comm off c₁ a] at h2
  rw [braidMatrix_thickGen_add_right n a c₁ c₂ (off + b),
    braidMatrix_thickGen_add_right n b c₁ c₂ off,
    braidMatrix_thickGen_add_right n b c₁ c₂ (off + a),
    braidMatrix_thickGen_add_right n a c₁ c₂ off, ← add_assoc]
  exact mul_split_third_thickYangBaxter h1 h2
    (braidMatrix_thickGen_commute_thickYangBaxter n _ _ _ _ _ _ (by omega)).symm
    (braidMatrix_thickGen_commute_thickYangBaxter n _ _ _ _ _ _ (by omega))

/-- The positive relation for three single strands is the braid relation. -/
private theorem thickYangBaxterPos_one_one_one (n off : ℕ) (hn : off + 3 ≤ n) :
    ThickYangBaxterPos n 1 1 1 off := by
  have h1 : ∀ o : ℕ, braidMatrix n (thickGen 1 1 o true) = crossingF n (o, true) := fun o ↦ by
    rw [show thickGen 1 1 o true = [(o, true)] from rfl, braidMatrix_cons,
      braidMatrix_nil, Matrix.mul_one]
  unfold ThickYangBaxterPos
  rw [h1, h1]
  exact crossingF_braid n off true (by omega)

/-- The positive relation for a bundle and two single strands. -/
private theorem thickYangBaxterPos_one_one (n a off : ℕ) (hn : off + a + 2 ≤ n) :
    ThickYangBaxterPos n a 1 1 off := by
  induction a generalizing off with
  | zero =>
    unfold ThickYangBaxterPos
    simp only [braidMatrix_thickGen_zero_left_thickYangBaxter, Matrix.one_mul, Matrix.mul_one,
      add_zero]
  | succ a ih =>
    rw [add_comm a 1]
    exact thickYangBaxterPos_add_first n 1 a 1 1 off
      (thickYangBaxterPos_one_one_one n off (by omega)) (ih (off + 1) (by omega))

/-- The positive relation for two bundles and a single strand. -/
private theorem thickYangBaxterPos_one (n a b off : ℕ) (hn : off + a + b + 1 ≤ n) :
    ThickYangBaxterPos n a b 1 off := by
  induction b generalizing off with
  | zero =>
    unfold ThickYangBaxterPos
    simp only [braidMatrix_thickGen_zero_left_thickYangBaxter,
      braidMatrix_thickGen_zero_right_thickYangBaxter, Matrix.one_mul, Matrix.mul_one, add_zero]
  | succ b ih =>
    rw [add_comm b 1]
    exact thickYangBaxterPos_add_second n a 1 b 1 off
      (thickYangBaxterPos_one_one n a off (by omega)) (ih (off + 1) (by omega))

/-- The Yang–Baxter relation for positive thick crossings. -/
private theorem thickYangBaxterPos_of_le (n a b c off : ℕ) (hn : off + a + b + c ≤ n) :
    ThickYangBaxterPos n a b c off := by
  induction c generalizing off with
  | zero =>
    unfold ThickYangBaxterPos
    simp only [braidMatrix_thickGen_zero_right_thickYangBaxter, Matrix.one_mul, Matrix.mul_one,
      add_zero]
  | succ c ih =>
    rw [add_comm c 1]
    exact thickYangBaxterPos_add_third n a b 1 c off
      (thickYangBaxterPos_one n a b off (by omega)) (ih (off + 1) (by omega))

/-- The Yang–Baxter (third Reidemeister) relation for thick crossings of the same sign. -/
theorem braidMatrix_thickCross_yangBaxter (n a b c off : ℕ) (s : Bool)
    (hn : off + a + b + c ≤ n) :
    braidMatrix n (thickCross a b off s) * braidMatrix n (thickCross a c (off + b) s) *
        braidMatrix n (thickCross b c off s) =
      braidMatrix n (thickCross b c (off + a) s) * braidMatrix n (thickCross a c off s) *
        braidMatrix n (thickCross a b (off + c) s) := by
  cases s
  · exact mul_inv_triple_thickYangBaxter (thickYangBaxterPos_of_le n c b a off (by omega))
      (braidMatrix_thickGen_mul_inv n c b off) (braidMatrix_thickGen_mul_inv n c a (off + b))
      (braidMatrix_thickGen_mul_inv n b a off) (braidMatrix_thickGen_inv_mul n b a (off + c))
      (braidMatrix_thickGen_inv_mul n c a off) (braidMatrix_thickGen_inv_mul n c b (off + a))
  · exact thickYangBaxterPos_of_le n a b c off hn

end AJConjecture
