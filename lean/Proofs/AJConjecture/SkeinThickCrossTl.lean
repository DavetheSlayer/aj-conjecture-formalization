import Mathlib
import AJConjecture.SkeinThickCrossTlBase
import AJConjecture.SkeinThickGenInv

/-!
# Naturality of a thick crossing with respect to the Temperley–Lieb generators

A generator `e_j` on two strands of one of the bundles slides through the crossing to the same
two strands of the bundle after the crossing. The case in which the other bundle is a single
strand is `AJConjecture.tlGenF_mul_braidMatrix_thickGen_right_one` and
`AJConjecture.tlGenF_mul_braidMatrix_thickGen_left_one`; the general positive crossing follows by
induction on the thickness of the other bundle with the splitting lemmas
(`AJConjecture.braidMatrix_thickGen_add_right` for the first statement,
`AJConjecture.thickGen_add_left` for the second). The negative crossing is the inverse of the
positive crossing of the bundles in the other order, so its statement follows from the other
statement for the positive crossing by multiplying with the inverses on both sides.
-/

namespace AJConjecture

/-- A generator on the first bundle slides through a positive thick crossing. -/
private theorem tlGenF_mul_thickGen_fst_thickCrossTl (n a b off j : ℕ) (hn : off + a + b ≤ n)
    (hj : j + 1 < a) :
    tlGenF n (off + j) * braidMatrix n (thickGen a b off true) =
      braidMatrix n (thickGen a b off true) * tlGenF n (off + b + j) := by
  induction b generalizing off with
  | zero =>
    have h0 : thickGen a 0 off true = [] := List.flatMap_eq_nil_iff.mpr fun _ _ ↦ rfl
    rw [h0, braidMatrix_nil, Matrix.mul_one, Matrix.one_mul, add_zero]
  | succ b ih =>
    rw [add_comm b 1, braidMatrix_thickGen_add_right, ← Matrix.mul_assoc,
      tlGenF_mul_braidMatrix_thickGen_right_one n a off j (by omega) hj, Matrix.mul_assoc,
      ih (off + 1) (by omega), Matrix.mul_assoc, ← add_assoc]

/-- A generator on the second bundle slides through a positive thick crossing. -/
private theorem tlGenF_mul_thickGen_snd_thickCrossTl (n a b off j : ℕ) (hn : off + a + b ≤ n)
    (hj : j + 1 < b) :
    tlGenF n (off + a + j) * braidMatrix n (thickGen a b off true) =
      braidMatrix n (thickGen a b off true) * tlGenF n (off + j) := by
  induction a with
  | zero =>
    rw [show thickGen 0 b off true = [] from rfl, braidMatrix_nil, Matrix.mul_one,
      Matrix.one_mul, add_zero]
  | succ a ih =>
    rw [thickGen_add_left a 1 b off, braidMatrix_append, ← Matrix.mul_assoc, ← add_assoc,
      tlGenF_mul_braidMatrix_thickGen_left_one n b (off + a) j (by omega) hj, Matrix.mul_assoc,
      ih (by omega), Matrix.mul_assoc]

/-- If `e'` slides through `p` to `e`, then `e` slides through the inverse of `p` to `e'`. -/
private theorem mul_inv_slide_thickCrossTl {M : Type*} [Monoid M] {e e' p q : M}
    (hpq : p * q = 1) (hqp : q * p = 1) (h : e' * p = p * e) : e * q = q * e' := by
  calc e * q = q * (p * e) * q := by rw [← mul_assoc, hqp, one_mul]
    _ = q * e' * (p * q) := by
        rw [← h]
        simp only [mul_assoc]
    _ = q * e' := by rw [hpq, mul_one]

/-- A generator on the first bundle slides through a thick crossing. -/
theorem tlGenF_mul_braidMatrix_thickCross_fst (n a b off j : ℕ) (s : Bool)
    (hn : off + a + b ≤ n) (hj : j + 1 < a) :
    tlGenF n (off + j) * braidMatrix n (thickCross a b off s) =
      braidMatrix n (thickCross a b off s) * tlGenF n (off + b + j) := by
  cases s
  · exact mul_inv_slide_thickCrossTl (braidMatrix_thickGen_mul_inv n b a off)
      (braidMatrix_thickGen_inv_mul n b a off)
      (tlGenF_mul_thickGen_snd_thickCrossTl n b a off j (by omega) hj)
  · exact tlGenF_mul_thickGen_fst_thickCrossTl n a b off j hn hj

/-- A generator on the second bundle slides through a thick crossing. -/
theorem tlGenF_mul_braidMatrix_thickCross_snd (n a b off j : ℕ) (s : Bool)
    (hn : off + a + b ≤ n) (hj : j + 1 < b) :
    tlGenF n (off + a + j) * braidMatrix n (thickCross a b off s) =
      braidMatrix n (thickCross a b off s) * tlGenF n (off + j) := by
  cases s
  · exact mul_inv_slide_thickCrossTl (braidMatrix_thickGen_mul_inv n b a off)
      (braidMatrix_thickGen_inv_mul n b a off)
      (tlGenF_mul_thickGen_fst_thickCrossTl n b a off j (by omega) hj)
  · exact tlGenF_mul_thickGen_snd_thickCrossTl n a b off j hn hj

end AJConjecture
