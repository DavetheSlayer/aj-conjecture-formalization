import Mathlib
import AJConjecture.SkeinJwAbsorb

/-!
# Wenzl's recursion from the left

The projector is characterised by `f² = f`, `e_j f = f e_j = 0` and `f - 1 ∈` the ideal generated
by the `e_j`; the element built by the mirror recursion (adding the new strand on the left)
has the same properties, hence the two agree: if `g` is another such element then
`f = f g = g`.
-/

namespace AJConjecture

/-- One step of Wenzl's recursion is killed by the new generator: if `g f = f`, `g` commutes
with `e` and `e f e = d g e` with `c d = -1`, then `e (f + c f e f) = 0`. -/
private theorem wenzl_kill_jwMirror {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (f g e : A) (c d : K) (hgf : g * f = f) (hge : g * e = e * g)
    (hefe : e * f * e = d • (g * e)) (hcd : c * d = -1) :
    e * (f + c • (f * e * f)) = 0 := by
  have hefe' : ∀ x : A, e * (f * (e * x)) = d • (g * (e * x)) := fun x ↦ by
    rw [← mul_assoc, ← mul_assoc, hefe, smul_mul_assoc, mul_assoc]
  have hge' : ∀ x : A, g * (e * x) = e * (g * x) := fun x ↦ by
    rw [← mul_assoc, hge, mul_assoc]
  simp only [mul_add, mul_smul_comm, mul_assoc, hefe', hge', hgf, smul_smul, hcd]
  module

/-- `f_k` fixes every matrix killed on the left by the generators of its block. -/
private theorem jwAt_mul_of_forall_tlGenF_mul_eq_zero_jwMirror (n i : ℕ) {l : ℕ}
    (Z : SkMat n l) :
    ∀ k : ℕ, (∀ j : ℕ, i ≤ j → j + 1 < i + k → tlGenF n j * Z = 0) → jwAt n i k * Z = Z
  | 0, _ => by rw [jwAt, Matrix.one_mul]
  | 1, _ => by rw [jwAt, Matrix.one_mul]
  | k + 2, hZ => by
    have ih := jwAt_mul_of_forall_tlGenF_mul_eq_zero_jwMirror n i Z (k + 1) fun j hij hjk ↦
      hZ j hij (by omega)
    rw [jwAt, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, ih, Matrix.mul_assoc,
      hZ (i + k) (by omega) (by omega), Matrix.mul_zero, smul_zero, add_zero]

/-- Wenzl's recursion with the new strand on the left. -/
theorem jwAt_succ_succ_left (n i k : ℕ) (h : i + k + 2 ≤ n) :
    jwAt n i (k + 2) = jwAt n (i + 1) (k + 1) +
      (quantumInt ((k : ℤ) + 1) / quantumInt ((k : ℤ) + 2)) •
        (jwAt n (i + 1) (k + 1) * tlGenF n i * jwAt n (i + 1) (k + 1)) := by
  induction k generalizing i with
  | zero => simp [jwAt]
  | succ k ih =>
    have hc1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    have hsand : tlGenF n i * jwAt n (i + 1) (k + 1 + 1) * tlGenF n i =
        ((-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) +
          quantumInt ((k + 1 : ℕ) : ℤ) / quantumInt (((k + 1 : ℕ) : ℤ) + 1)) •
          (jwAt n (i + 1 + 1) (k + 1) * tlGenF n i) := by
      rw [ih (i + 1) (by omega), hc1, show (k : ℤ) + 1 + 1 = (k : ℤ) + 2 from by ring]
      exact wenzl_sandwich (jwAt n (i + 1 + 1) (k + 1)) (tlGenF n i) (tlGenF n (i + 1))
        _ _ (jwAt_mul_self n _ _)
        (jwAt_commute_tlGenF n (i + 1 + 1) (k + 1) i (Or.inl (by omega))).eq
        (tlGenF_mul_self n i) (tlGenF_mul_succ_mul n i (by omega))
    have heG := wenzl_kill_jwMirror (jwAt n (i + 1) (k + 1 + 1)) (jwAt n (i + 1 + 1) (k + 1))
      (tlGenF n i) (quantumInt (((k + 1 : ℕ) : ℤ) + 1) / quantumInt (((k + 1 : ℕ) : ℤ) + 2)) _
      (jwAt_mul_jwAt_of_ge n (i + 1) (k + 1 + 1) (i + 1 + 1) (k + 1) (by omega) (by omega))
      (jwAt_commute_tlGenF n (i + 1 + 1) (k + 1) i (Or.inl (by omega))).eq hsand
      (wenzl_scalar (k + 1))
    have hfG := jwAt_mul_of_forall_tlGenF_mul_eq_zero_jwMirror n i
      (jwAt n (i + 1) (k + 1 + 1) + (quantumInt (((k + 1 : ℕ) : ℤ) + 1) /
        quantumInt (((k + 1 : ℕ) : ℤ) + 2)) • (jwAt n (i + 1) (k + 1 + 1) * tlGenF n i *
          jwAt n (i + 1) (k + 1 + 1))) (k + 1 + 2) fun j hij hjk ↦ by
      rcases eq_or_lt_of_le hij with rfl | hlt
      · exact heG
      · rw [Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
          tlGenF_mul_jwAt n (i + 1) (k + 1 + 1) j (by omega) (by omega), Matrix.zero_mul,
          Matrix.zero_mul, smul_zero, add_zero]
    rw [← hfG, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      jwAt_mul_jwAt_of_le n i (k + 1 + 2) (i + 1) (k + 1 + 1) (by omega) (by omega),
      jwAt_mul_tlGenF n i (k + 1 + 2) i le_rfl (by omega), Matrix.zero_mul, smul_zero, add_zero]

end AJConjecture
