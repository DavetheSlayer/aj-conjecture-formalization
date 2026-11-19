import Mathlib
import AJConjecture.SkeinThickCrossCapBase

/-!
# Naturality of a thick crossing with respect to caps

A cap on two adjacent strands of one of the bundles slides through the crossing: the bundle is
thinner by two on the side of the cap that has been passed. For a positive crossing, induct on
the thickness of the other bundle: split it with `AJConjecture.braidMatrix_thickGen_add_right`
(first statement) or `AJConjecture.thickGen_add_left` (second statement) and use the case of a
single strand, `AJConjecture.capAt_mul_braidMatrix_thickGen_right_one` and
`AJConjecture.capAt_mul_braidMatrix_thickGen_left_one`. The negative crossing
`thickCross a b off false` is the inverse of the positive crossing of the bundles in the other
order, so each statement for it is the other statement for the positive crossing multiplied by
the inverses (`AJConjecture.braidMatrix_thickGen_mul_inv`).
-/

namespace AJConjecture

/-- A positive thick crossing with an empty second bundle is the empty word. -/
private theorem thickGen_zero_right_thickCrossCap (a off : ℕ) : thickGen a 0 off true = [] := by
  simp [thickGen]

/-- A positive thick crossing with an empty first bundle is the empty word. -/
private theorem thickGen_zero_left_thickCrossCap (b off : ℕ) : thickGen 0 b off true = [] := by
  simp [thickGen]

/-- A cap on the first bundle slides through a positive thick crossing. -/
private theorem capAt_mul_braidMatrix_thickGen_fst_thickCrossCap (n a b off j : ℕ)
    (hn : off + a + b ≤ n) (hj : j ≤ a) :
    capAt n (off + j) * braidMatrix n (thickGen a b off true) =
      braidMatrix (n + 2) (thickGen (a + 2) b off true) * capAt n (off + b + j) := by
  induction b with
  | zero =>
    simp only [thickGen_zero_right_thickCrossCap, braidMatrix_nil, Matrix.mul_one,
      Matrix.one_mul, Nat.add_zero]
  | succ b ih =>
    rw [braidMatrix_thickGen_add_right, braidMatrix_thickGen_add_right, ← Matrix.mul_assoc,
      ih (by omega), Matrix.mul_assoc,
      capAt_mul_braidMatrix_thickGen_right_one n a (off + b) j (by omega) hj, Matrix.mul_assoc,
      show off + b + 1 + j = off + (b + 1) + j from by omega]

/-- A cap on the second bundle slides through a positive thick crossing. -/
private theorem capAt_mul_braidMatrix_thickGen_snd_thickCrossCap (n a b off j : ℕ)
    (hn : off + a + b ≤ n) (hj : j ≤ b) :
    capAt n (off + a + j) * braidMatrix n (thickGen a b off true) =
      braidMatrix (n + 2) (thickGen a (b + 2) off true) * capAt n (off + j) := by
  induction a with
  | zero =>
    simp only [thickGen_zero_left_thickCrossCap, braidMatrix_nil, Matrix.mul_one,
      Matrix.one_mul, Nat.add_zero]
  | succ a ih =>
    rw [thickGen_add_left, thickGen_add_left, braidMatrix_append, braidMatrix_append,
      ← Matrix.mul_assoc, show off + (a + 1) + j = off + a + 1 + j from by omega,
      capAt_mul_braidMatrix_thickGen_left_one n b (off + a) j (by omega) hj, Matrix.mul_assoc,
      ih (by omega), Matrix.mul_assoc]

/-- An intertwining relation `C * P = P' * D` gives the relation for the inverses. -/
private theorem mul_inv_eq_inv_mul_of_mul_eq_thickCrossCap {N n : ℕ} (C D : SkMat N n)
    (P Q : SkMat n n) (P' Q' : SkMat N N) (h : C * P = P' * D) (hPQ : P * Q = 1)
    (hQP : Q' * P' = 1) : D * Q = Q' * C := by
  calc D * Q = Q' * P' * D * Q := by rw [hQP, Matrix.one_mul]
    _ = Q' * (C * P) * Q := by rw [Matrix.mul_assoc Q', h]
    _ = Q' * C := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hPQ, Matrix.mul_one]

/-- A cap on the first bundle slides through a thick crossing. -/
theorem capAt_mul_braidMatrix_thickCross_fst (n a b off j : ℕ) (s : Bool)
    (hn : off + a + b ≤ n) (hj : j ≤ a) :
    capAt n (off + j) * braidMatrix n (thickCross a b off s) =
      braidMatrix (n + 2) (thickCross (a + 2) b off s) * capAt n (off + b + j) := by
  cases s
  · simp only [thickCross, Bool.false_eq_true, ite_false]
    exact mul_inv_eq_inv_mul_of_mul_eq_thickCrossCap _ _ _ _ _ _
      (capAt_mul_braidMatrix_thickGen_snd_thickCrossCap n b a off j (by omega) hj)
      (braidMatrix_thickGen_mul_inv n b a off) (braidMatrix_thickGen_inv_mul (n + 2) b (a + 2) off)
  · simp only [thickCross, ite_true]
    exact capAt_mul_braidMatrix_thickGen_fst_thickCrossCap n a b off j hn hj

/-- A cap on the second bundle slides through a thick crossing. -/
theorem capAt_mul_braidMatrix_thickCross_snd (n a b off j : ℕ) (s : Bool)
    (hn : off + a + b ≤ n) (hj : j ≤ b) :
    capAt n (off + a + j) * braidMatrix n (thickCross a b off s) =
      braidMatrix (n + 2) (thickCross a (b + 2) off s) * capAt n (off + j) := by
  cases s
  · simp only [thickCross, Bool.false_eq_true, ite_false]
    exact mul_inv_eq_inv_mul_of_mul_eq_thickCrossCap _ _ _ _ _ _
      (capAt_mul_braidMatrix_thickGen_fst_thickCrossCap n b a off j (by omega) hj)
      (braidMatrix_thickGen_mul_inv n b a off) (braidMatrix_thickGen_inv_mul (n + 2) (b + 2) a off)
  · simp only [thickCross, ite_true]
    exact capAt_mul_braidMatrix_thickGen_snd_thickCrossCap n a b off j hn hj

end AJConjecture
