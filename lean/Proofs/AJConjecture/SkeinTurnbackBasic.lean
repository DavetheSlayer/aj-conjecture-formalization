import Mathlib
import AJConjecture.SkeinJwCapComm
import AJConjecture.SkeinJwAbsorb
import AJConjecture.SkeinThickCup
import AJConjecture.SkeinTwoBundle

/-!
# First facts on the two-bundle projector and the turnback elements

`f ⊗ f` is an idempotent (two commuting idempotents, `AJConjecture.jwAt_commute_tlGenF`),
`D_0 = f ⊗ f` (the empty nest of caps and cups is `1`), `D_1 = (f ⊗ f) e_{c-1} (f ⊗ f)`
(`AJConjecture.capAt_mul_cupAt`), `D_k = 0` for `k > c` (the placement does not fit), and
`f ⊗ f` is a unit for the `D_k`. A nest of `k` caps in the middle of two bundles of `a + k`
strands with projectors absorbs the projectors `f_a ⊗ f_a` on the `2a` strands that are left:
`f_{a+k}` absorbs `f_a` on its outer `a` strands (`AJConjecture.jwAt_mul_jwAt_of_le`), which
commutes with the caps (`AJConjecture.jwAt_mul_capAt_of_le`, `AJConjecture.jwAt_mul_capAt_of_ge`,
one cap at a time with `AJConjecture.capThick_succ_inner`); and symmetrically for cups.
-/

namespace AJConjecture

/-- A generator on the left of a placed matrix commutes with it. -/
theorem tlGenF_mul_skPlace_of_lt (n n' i j : ℕ) {p q : ℕ} (X : SkMat p q)
    (hij : i + 2 ≤ j) (hj : j + p ≤ n) (hn : n + q = n' + p) :
    tlGenF n i * skPlace n n' j X = skPlace n n' j X * tlGenF n' i := by
  have h := skPlace_mul_skPlace_comm n n n' n' i j (tlGenF 2 0) X hij hj rfl hn hn
  rw [Nat.add_sub_cancel] at h
  rw [tlGenF_eq_skPlace n i, tlGenF_eq_skPlace n' i, h]

/-- A generator on the right of a placed matrix commutes with it; its position is shifted. -/
theorem tlGenF_mul_skPlace_of_ge (n n' i j : ℕ) {p q : ℕ} (X : SkMat p q)
    (hji : j + p ≤ i) (hi : i + 2 ≤ n) (hn : n + q = n' + p) :
    tlGenF n i * skPlace n n' j X = skPlace n n' j X * tlGenF n' (i + q - p) := by
  have h := skPlace_mul_skPlace_comm n n' n n' j i X (tlGenF 2 0) hji hi hn rfl rfl
  rw [tlGenF_eq_skPlace n i, tlGenF_eq_skPlace n' (i + q - p), h]

/-- A projector on the left of a placed matrix commutes with it. -/
theorem jwAt_mul_skPlace_of_le (n n' i k j : ℕ) {p q : ℕ} (X : SkMat p q)
    (h : i + k ≤ j) (hj : j + p ≤ n) (hn : n + q = n' + p) :
    jwAt n i k * skPlace n n' j X = skPlace n n' j X * jwAt n' i k :=
  jwAt_mul_eq_mul_jwAt n n' i i _ k fun l _ ↦
    tlGenF_mul_skPlace_of_lt n n' (i + l) j X (by omega) hj hn

/-- A projector on the right of a placed matrix commutes with it; its position is shifted. -/
private theorem jwAt_mul_skPlace_of_ge_turnbackBasic (n n' i k j : ℕ) {p q : ℕ} (X : SkMat p q)
    (h : j + p ≤ i) (hi : i + k ≤ n) (hn : n + q = n' + p) :
    jwAt n i k * skPlace n n' j X = skPlace n n' j X * jwAt n' (i + q - p) k :=
  jwAt_mul_eq_mul_jwAt n n' i (i + q - p) _ k fun l _ ↦ by
    rw [tlGenF_mul_skPlace_of_ge n n' (i + l) j X (by omega) (by omega) hn,
      show i + l + q - p = i + q - p + l from by omega]

/-- The two projectors of `f ⊗ f` commute. -/
private theorem jwAt_mul_jwAt_comm_turnbackBasic (c : ℕ) :
    jwAt (2 * c) 0 c * jwAt (2 * c) c c = jwAt (2 * c) c c * jwAt (2 * c) 0 c :=
  (jwAt_mul_eq_mul_jwAt (2 * c) (2 * c) c c (jwAt (2 * c) 0 c) c fun l _ ↦
    (jwAt_commute_tlGenF (2 * c) 0 c (c + l) (Or.inr (by omega))).eq.symm).symm

/-- The product of two commuting idempotents is an idempotent. -/
private theorem mul_mul_self_of_comm_turnbackBasic {M : Type*} [Monoid M] (f g : M)
    (hfg : f * g = g * f) (hf : f * f = f) (hg : g * g = g) : f * g * (f * g) = f * g := by
  calc f * g * (f * g) = f * (g * f) * g := by simp only [mul_assoc]
    _ = f * f * (g * g) := by rw [← hfg]; simp only [mul_assoc]
    _ = f * g := by rw [hf, hg]

/-- A product of two commuting elements absorbs on the right what its factors absorb. -/
private theorem mul_mul_absorb_right_turnbackBasic {M : Type*} [Monoid M] (f g f' g' : M)
    (hfg : f * g = g * f) (hf : f * f' = f) (hg : g * g' = g) : f * g * (f' * g') = f * g := by
  calc f * g * (f' * g') = g * (f * f') * g' := by rw [hfg]; simp only [mul_assoc]
    _ = f * (g * g') := by rw [hf, ← hfg, mul_assoc]
    _ = f * g := by rw [hg]

/-- A product of two commuting elements absorbs on the left what its factors absorb. -/
private theorem mul_mul_absorb_left_turnbackBasic {M : Type*} [Monoid M] (f g f' g' : M)
    (hfg : f * g = g * f) (hf : f' * f = f) (hg : g' * g = g) : f' * g' * (f * g) = f * g := by
  calc f' * g' * (f * g) = f' * (g' * g) * f := by rw [hfg]; simp only [mul_assoc]
    _ = f' * f * g := by rw [hg, mul_assoc, ← hfg, ← mul_assoc]
    _ = f * g := by rw [hf]

/-- A placement that does not fit is zero. -/
private theorem skPlace_eq_zero_turnbackBasic (n n' i : ℕ) {k l : ℕ} (A : SkMat k l)
    (h : ¬(i + k ≤ n ∧ n + l = n' + k)) : skPlace n n' i A = 0 := by
  ext a b
  simp [skPlace, h]

/-- The thick cup on one strand is the cup. -/
private theorem cupThick_one_turnbackBasic : cupThick 1 = skCup :=
  (cupThick_succ 0).trans <| by
    rw [cupThick_zero, skPlace_one 2 1 0 (by omega), Matrix.mul_one]

/-- The thick cap on one strand is the cap. -/
private theorem capThick_one_turnbackBasic : capThick 1 = skCap :=
  (capThick_succ 0).trans <| by
    rw [capThick_zero, skPlace_one 2 1 0 (by omega), Matrix.one_mul]

/-- `f ⊗ f` is an idempotent. -/
theorem twoBundleProj_mul_self (c : ℕ) : twoBundleProj c * twoBundleProj c = twoBundleProj c :=
  mul_mul_self_of_comm_turnbackBasic _ _ (jwAt_mul_jwAt_comm_turnbackBasic c)
    (jwAt_mul_self (2 * c) 0 c) (jwAt_mul_self (2 * c) c c)

/-- `D_0 = f ⊗ f`. -/
theorem turnback_zero (c : ℕ) : turnback c 0 = twoBundleProj c := by
  rw [turnback, capThick_zero, cupThick_zero, Matrix.mul_one,
    Nat.sub_zero, skPlace_one (2 * c) c 0 (by omega), Matrix.mul_one, twoBundleProj_mul_self]

/-- `D_1 = (f ⊗ f) e_{c-1} (f ⊗ f)`. -/
theorem turnback_one (c : ℕ) :
    turnback c 1 = twoBundleProj c * tlGenF (2 * c) (c - 1) * twoBundleProj c := by
  rw [turnback, capThick_one_turnbackBasic, cupThick_one_turnbackBasic, skCap_mul_skCup,
    ← tlGenF_eq_skPlace]

/-- `D_k = 0` for `k > c`. -/
theorem turnback_eq_zero (c k : ℕ) (h : c < k) : turnback c k = 0 := by
  rw [turnback, skPlace_eq_zero_turnbackBasic (2 * c) (2 * c) (c - k) _ (by omega),
    Matrix.mul_zero, Matrix.zero_mul]

/-- `f ⊗ f` is a left unit for the turnback elements. -/
theorem twoBundleProj_mul_turnback (c k : ℕ) : twoBundleProj c * turnback c k = turnback c k := by
  rw [turnback, ← Matrix.mul_assoc, ← Matrix.mul_assoc, twoBundleProj_mul_self]

/-- `f ⊗ f` is a right unit for the turnback elements. -/
theorem turnback_mul_twoBundleProj (c k : ℕ) : turnback c k * twoBundleProj c = turnback c k := by
  rw [turnback, Matrix.mul_assoc, twoBundleProj_mul_self]

/-- Nested caps below `f ⊗ f` absorb the projectors on the strands that are left. -/
theorem twoBundleProj_mul_capThick_mul_twoBundleProj (a k : ℕ) :
    twoBundleProj (a + k) * skPlace (2 * (a + k)) (2 * a) a (capThick k) * twoBundleProj a =
      twoBundleProj (a + k) * skPlace (2 * (a + k)) (2 * a) a (capThick k) := by
  have h1 := jwAt_mul_skPlace_of_le (2 * (a + k)) (2 * a) 0 a a (capThick k)
    (by omega) (by omega) (by omega)
  have h2 := jwAt_mul_skPlace_of_ge_turnbackBasic (2 * (a + k)) (2 * a) (a + 2 * k) a a
    (capThick k) (by omega) (by omega) (by omega)
  rw [show a + 2 * k + 0 - 2 * k = a from by omega] at h2
  have h3 : twoBundleProj (a + k) *
      (jwAt (2 * (a + k)) 0 a * jwAt (2 * (a + k)) (a + 2 * k) a) = twoBundleProj (a + k) :=
    mul_mul_absorb_right_turnbackBasic _ _ _ _ (jwAt_mul_jwAt_comm_turnbackBasic (a + k))
      (jwAt_mul_jwAt_of_le (2 * (a + k)) 0 (a + k) 0 a le_rfl (by omega))
      (jwAt_mul_jwAt_of_le (2 * (a + k)) (a + k) (a + k) (a + 2 * k) a (by omega) (by omega))
  have hP : twoBundleProj a = jwAt (2 * a) 0 a * jwAt (2 * a) a a := rfl
  rw [Matrix.mul_assoc, hP, ← Matrix.mul_assoc _ (jwAt (2 * a) 0 a), ← h1,
    Matrix.mul_assoc _ _ (jwAt (2 * a) a a), ← h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_assoc (twoBundleProj (a + k)), h3]

/-- Nested cups above `f ⊗ f` absorb the projectors on the strands they start from. -/
theorem twoBundleProj_mul_cupThick_mul_twoBundleProj (a k : ℕ) :
    twoBundleProj a * skPlace (2 * a) (2 * (a + k)) a (cupThick k) * twoBundleProj (a + k) =
      skPlace (2 * a) (2 * (a + k)) a (cupThick k) * twoBundleProj (a + k) := by
  have h1 := jwAt_mul_skPlace_of_le (2 * a) (2 * (a + k)) 0 a a (cupThick k)
    (by omega) (by omega) (by omega)
  have h2 := jwAt_mul_skPlace_of_ge_turnbackBasic (2 * a) (2 * (a + k)) a a a (cupThick k)
    (by omega) (by omega) (by omega)
  rw [show a + 2 * k - 0 = a + 2 * k from by omega] at h2
  have h3 : jwAt (2 * (a + k)) 0 a * jwAt (2 * (a + k)) (a + 2 * k) a * twoBundleProj (a + k) =
      twoBundleProj (a + k) :=
    mul_mul_absorb_left_turnbackBasic _ _ _ _ (jwAt_mul_jwAt_comm_turnbackBasic (a + k))
      (jwAt_mul_jwAt_of_ge (2 * (a + k)) 0 (a + k) 0 a le_rfl (by omega))
      (jwAt_mul_jwAt_of_ge (2 * (a + k)) (a + k) (a + k) (a + 2 * k) a (by omega) (by omega))
  have hP : twoBundleProj a = jwAt (2 * a) 0 a * jwAt (2 * a) a a := rfl
  rw [hP, Matrix.mul_assoc (jwAt (2 * a) 0 a), h2, ← Matrix.mul_assoc, h1,
    Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (jwAt (2 * (a + k)) 0 a), h3]

end AJConjecture
