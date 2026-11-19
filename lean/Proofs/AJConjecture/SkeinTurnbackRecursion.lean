import Mathlib
import AJConjecture.SkeinTurnbackOneSided

/-!
# The turnback recursion `D_1 D_k = α_k D_{k+1} + β_k D_k`

`α_k = [c-k]²/[c]²` and `β_k = -[k][2c+1-k]/[c]²`. Multiply the one-sided recursion
(`AJConjecture.turnback_one_mul_capThick_place`, or
`AJConjecture.turnback_one_mul_capThick` for `k = c`) on the right by the nest of `k` cups and
`f ⊗ f`: the projectors on the strands that are left are absorbed
(`AJConjecture.twoBundleProj_mul_cupThick_mul_twoBundleProj`), and the cup followed by the nest of
`k` cups is the nest of `k + 1` cups (`AJConjecture.cupThick_succ`, placed). For `k > c` both sides
vanish (`AJConjecture.turnback_eq_zero`), and for `c = 0` all terms vanish, so the statement needs
no hypothesis.
-/

namespace AJConjecture

/-- A placed nest of `c + 1` cups: the outer cup, then the placed nest of `c` cups. -/
private theorem skPlace_cupThick_succ_turnbackRec (n n' i c : ℕ) (h : i ≤ n)
    (h' : n + 2 * (c + 1) = n') :
    skPlace n n' i (cupThick (c + 1)) =
      skPlace n (n + 2) i skCup * skPlace (n + 2) n' (i + 1) (cupThick c) := by
  rw [cupThick_succ, skPlace_mul n (n + 2) n' i skCup _ (by omega) (by omega) (by omega),
    skPlace_skPlace (n + 2) n' i 1 (cupThick c) (by omega) (by omega) (by omega) (by omega)]

/-- The algebra of the turnback recursion for `k < c`: the one-sided recursion multiplied by the
nest of cups `C` and `F = f ⊗ f`. -/
private theorem turnback_one_mul_alg_turnbackRec {K N L L0 : Type*} [CommRing K] [Fintype N]
    [Fintype L] [Fintype L0] (D F : Matrix N N K) (P : Matrix N L K) (C : Matrix L N K)
    (F1 : Matrix L L K) (Q : Matrix N L0 K) (u : Matrix L0 L K) (α β : K)
    (hOS : D * P = β • (F * P) + α • (F * Q * u * F1)) (hDF : D * F = D)
    (habs : F1 * C * F = C * F) :
    D * (F * (P * C) * F) = α • (F * (Q * (u * C)) * F) + β • (F * (P * C) * F) :=
  calc D * (F * (P * C) * F) = D * F * P * C * F := by simp only [Matrix.mul_assoc]
    _ = (β • (F * P) + α • (F * Q * u * F1)) * C * F := by rw [hDF, hOS]
    _ = β • (F * P * C * F) + α • (F * Q * u * (F1 * C * F)) := by
      simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = α • (F * (Q * (u * C)) * F) + β • (F * (P * C) * F) := by
      rw [habs, add_comm]
      simp only [Matrix.mul_assoc]

/-- The algebra of the turnback recursion for `k = c`. -/
private theorem turnback_one_mul_full_alg_turnbackRec {K N L : Type*} [CommRing K] [Fintype N]
    [Fintype L] (D F : Matrix N N K) (P : Matrix N L K) (C : Matrix L N K) (β : K)
    (hOS : D * P = β • (F * P)) (hDF : D * F = D) :
    D * (F * (P * C) * F) = β • (F * (P * C) * F) :=
  calc D * (F * (P * C) * F) = D * F * P * C * F := by simp only [Matrix.mul_assoc]
    _ = β • (F * P) * C * F := by rw [hDF, hOS]
    _ = β • (F * (P * C) * F) := by simp only [Matrix.smul_mul, Matrix.mul_assoc]

/-- The turnback recursion for `k < c`, with `c = a + 1 + k`. -/
private theorem turnback_one_mul_of_lt_turnbackRec (a k : ℕ) :
    turnback (a + 1 + k) 1 * turnback (a + 1 + k) k =
      (quantumInt ((a : ℤ) + 1) ^ 2 / quantumInt ((a : ℤ) + 1 + k) ^ 2) •
          turnback (a + 1 + k) (k + 1) +
        (-(quantumInt (k : ℤ) * quantumInt (2 * (a : ℤ) + k + 3)) /
          quantumInt ((a : ℤ) + 1 + k) ^ 2) • turnback (a + 1 + k) k := by
  have hTk : turnback (a + 1 + k) k = twoBundleProj (a + 1 + k) *
      (skPlace (2 * (a + 1 + k)) (2 * (a + 1)) (a + 1) (capThick k) *
        skPlace (2 * (a + 1)) (2 * (a + 1 + k)) (a + 1) (cupThick k)) *
      twoBundleProj (a + 1 + k) := by
    rw [turnback, Nat.add_sub_cancel,
      skPlace_mul (2 * (a + 1 + k)) (2 * (a + 1)) (2 * (a + 1 + k)) (a + 1) (capThick k)
        (cupThick k) (by omega) (by omega) (by omega)]
  have hTk1 : turnback (a + 1 + k) (k + 1) = twoBundleProj (a + 1 + k) *
      (skPlace (2 * (a + 1 + k)) (2 * a) a (capThick (k + 1)) *
        (skPlace (2 * a) (2 * (a + 1)) a skCup *
          skPlace (2 * (a + 1)) (2 * (a + 1 + k)) (a + 1) (cupThick k))) *
      twoBundleProj (a + 1 + k) := by
    rw [turnback, show a + 1 + k - (k + 1) = a from by omega,
      skPlace_mul (2 * (a + 1 + k)) (2 * a) (2 * (a + 1 + k)) a (capThick (k + 1))
        (cupThick (k + 1)) (by omega) (by omega) (by omega),
      skPlace_cupThick_succ_turnbackRec (2 * a) (2 * (a + 1 + k)) a k (by omega) (by omega)]
    rfl
  rw [hTk, hTk1]
  exact turnback_one_mul_alg_turnbackRec _ _ _ _ _ _ _ _ _
    (turnback_one_mul_capThick_place a k) (turnback_mul_twoBundleProj (a + 1 + k) 1)
    (twoBundleProj_mul_cupThick_mul_twoBundleProj (a + 1) k)

/-- The turnback recursion for `k = c`. -/
private theorem turnback_one_mul_self_turnbackRec (c : ℕ) :
    turnback c 1 * turnback c c =
      (-(quantumInt (c : ℤ) * quantumInt ((c : ℤ) + 1)) / quantumInt (c : ℤ) ^ 2) •
        turnback c c := by
  have hT : turnback c c = twoBundleProj c * (capThick c * cupThick c) * twoBundleProj c := by
    rw [turnback, Nat.sub_self, skPlace_self]
  rw [hT]
  exact turnback_one_mul_full_alg_turnbackRec _ _ _ _ _ (turnback_one_mul_capThick c)
    (turnback_mul_twoBundleProj c 1)

/-- The turnback recursion. -/
theorem turnback_one_mul (c k : ℕ) :
    turnback c 1 * turnback c k =
      (quantumInt ((c : ℤ) - k) ^ 2 / quantumInt (c : ℤ) ^ 2) • turnback c (k + 1) +
        (-(quantumInt (k : ℤ) * quantumInt (2 * (c : ℤ) + 1 - k)) / quantumInt (c : ℤ) ^ 2) •
          turnback c k := by
  rcases lt_trichotomy k c with h | rfl | h
  · obtain ⟨a, rfl⟩ : ∃ a, c = a + 1 + k := ⟨c - k - 1, by omega⟩
    rw [show ((a + 1 + k : ℕ) : ℤ) - k = (a : ℤ) + 1 from by push_cast; ring,
      show 2 * ((a + 1 + k : ℕ) : ℤ) + 1 - k = 2 * (a : ℤ) + k + 3 from by push_cast; ring,
      show ((a + 1 + k : ℕ) : ℤ) = (a : ℤ) + 1 + k from by push_cast; ring]
    exact turnback_one_mul_of_lt_turnbackRec a k
  · rw [turnback_eq_zero k (k + 1) (by omega), smul_zero, zero_add,
      show 2 * (k : ℤ) + 1 - k = (k : ℤ) + 1 from by ring]
    exact turnback_one_mul_self_turnbackRec k
  · rw [turnback_eq_zero c k h, turnback_eq_zero c (k + 1) (by omega), Matrix.mul_zero,
      smul_zero, smul_zero, add_zero]

end AJConjecture
