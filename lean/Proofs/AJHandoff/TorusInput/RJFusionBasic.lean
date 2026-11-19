import Mathlib
import AJHandoff.TorusInput.RJDefs
import AJConjecture.SkeinTurnbackBasic
import AJConjecture.SkeinJwAbsorb
import AJConjecture.SkeinJwCapComm
import AJConjecture.SkeinJwCapThick
import AJConjecture.SkeinPlaceMul
import AJConjecture.SkeinPlaceComm

/-!
# Two unequal bundles: projector algebra and absorption (node RA1.1)

The unequal versions of `twoBundleProj_mul_self`, `twoBundleProj_mul_capThick_mul_twoBundleProj`
and `twoBundleProj_mul_cupThick_mul_twoBundleProj` (`AJConjecture.SkeinTurnbackBasic`), and the
absorption of the projectors by the fusion maps.

Route. Copy the equal-size proofs with the two sizes kept apart: the projectors `f_a` and `f_b`
have disjoint blocks and commute (`jwAt_commute_tlGenF`, `commute_jwAt_of_commute_tlGenF`); a
projector on the first `p` or the last `q` strands commutes with the nest of caps in the middle
(`jwAt_mul_skPlace_of_le`, `tlGenF_mul_skPlace_of_lt`, `tlGenF_mul_skPlace_of_ge`, the transport
principle); `f_(p+j)` absorbs `f_p` (`jwAt_mul_jwAt_of_le`, `jwAt_mul_jwAt_of_ge`). Estimate
120–180 lines.
-/

noncomputable section

namespace AJConjecture

/-- A projector on the right of a placed matrix commutes with it; its position is shifted. -/
private theorem rj_jwAt_mul_skPlace_of_ge_fusionBasic (n n' i k j : ℕ) {p q : ℕ}
    (X : SkMat p q) (h : j + p ≤ i) (hi : i + k ≤ n) (hn : n + q = n' + p) :
    jwAt n i k * skPlace n n' j X = skPlace n n' j X * jwAt n' (i + q - p) k :=
  jwAt_mul_eq_mul_jwAt n n' i (i + q - p) _ k fun l _ ↦ by
    rw [tlGenF_mul_skPlace_of_ge n n' (i + l) j X (by omega) (by omega) hn,
      show i + l + q - p = i + q - p + l from by omega]

/-- The two projectors of `f_a ⊗ f_b` commute. -/
private theorem rj_jwAt_mul_jwAt_comm_fusionBasic (n a b : ℕ) :
    jwAt n 0 a * jwAt n a b = jwAt n a b * jwAt n 0 a :=
  (jwAt_mul_eq_mul_jwAt n n a a (jwAt n 0 a) b fun l _ ↦
    (jwAt_commute_tlGenF n 0 a (a + l) (Or.inr (by omega))).eq.symm).symm

/-- The product of two commuting idempotents is an idempotent. -/
private theorem rj_mul_mul_self_of_comm_fusionBasic {M : Type*} [Monoid M] (f g : M)
    (hfg : f * g = g * f) (hf : f * f = f) (hg : g * g = g) : f * g * (f * g) = f * g := by
  calc f * g * (f * g) = f * (g * f) * g := by simp only [mul_assoc]
    _ = f * f * (g * g) := by rw [← hfg]; simp only [mul_assoc]
    _ = f * g := by rw [hf, hg]

/-- A product of two commuting elements absorbs on the right what its factors absorb. -/
private theorem rj_mul_mul_absorb_right_fusionBasic {M : Type*} [Monoid M] (f g f' g' : M)
    (hfg : f * g = g * f) (hf : f * f' = f) (hg : g * g' = g) : f * g * (f' * g') = f * g := by
  calc f * g * (f' * g') = g * (f * f') * g' := by rw [hfg]; simp only [mul_assoc]
    _ = f * (g * g') := by rw [hf, ← hfg, mul_assoc]
    _ = f * g := by rw [hg]

/-- A product of two commuting elements absorbs on the left what its factors absorb. -/
private theorem rj_mul_mul_absorb_left_fusionBasic {M : Type*} [Monoid M] (f g f' g' : M)
    (hfg : f * g = g * f) (hf : f' * f = f) (hg : g' * g = g) : f' * g' * (f * g) = f * g := by
  calc f' * g' * (f * g) = f' * (g' * g) * f := by rw [hfg]; simp only [mul_assoc]
    _ = f' * f * g := by rw [hg, mul_assoc, ← hfg, ← mul_assoc]
    _ = f * g := by rw [hf]

/-- `f_a ⊗ f_b` is an idempotent. -/
theorem rjBundleProj_mul_self (a b : ℕ) :
    rjBundleProj a b * rjBundleProj a b = rjBundleProj a b :=
  rj_mul_mul_self_of_comm_fusionBasic _ _ (rj_jwAt_mul_jwAt_comm_fusionBasic (a + b) a b)
    (jwAt_mul_self _ 0 a) (jwAt_mul_self _ a b)

/-- The fusion map absorbs `f_a ⊗ f_b` on the left and `f_(a+b-2j)` on the right. -/
theorem rjFusionProj_absorb (a b j : ℕ) :
    rjBundleProj a b * rjFusionProj a b j = rjFusionProj a b j ∧
      rjFusionProj a b j * jwAt (a + b - 2 * j) 0 (a + b - 2 * j) = rjFusionProj a b j := by
  refine ⟨?_, ?_⟩
  · rw [rjFusionProj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, rjBundleProj_mul_self]
  · rw [rjFusionProj, Matrix.mul_assoc, jwAt_mul_self]

/-- The fusion inclusion absorbs `f_(a+b-2j)` on the left and `f_a ⊗ f_b` on the right. -/
theorem rjFusionIncl_absorb (a b j : ℕ) :
    jwAt (a + b - 2 * j) 0 (a + b - 2 * j) * rjFusionIncl a b j = rjFusionIncl a b j ∧
      rjFusionIncl a b j * rjBundleProj a b = rjFusionIncl a b j := by
  refine ⟨?_, ?_⟩
  · rw [rjFusionIncl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, jwAt_mul_self]
  · rw [rjFusionIncl, Matrix.mul_assoc, rjBundleProj_mul_self]

/-- A nest of `j` caps in the middle of `f_(p+j) ⊗ f_(q+j)` is followed by `f_p ⊗ f_q` for
free. -/
theorem rjBundleProj_mul_capThick_mul_bundleProj (p q j : ℕ) :
    rjBundleProj (p + j) (q + j) * skPlace (p + j + (q + j)) (p + q) p (capThick j) *
        rjBundleProj p q =
      rjBundleProj (p + j) (q + j) * skPlace (p + j + (q + j)) (p + q) p (capThick j) := by
  have h1 := jwAt_mul_skPlace_of_le (p + j + (q + j)) (p + q) 0 p p (capThick j)
    (by omega) (by omega) (by omega)
  have h2 := rj_jwAt_mul_skPlace_of_ge_fusionBasic (p + j + (q + j)) (p + q) (p + 2 * j) q p
    (capThick j) (by omega) (by omega) (by omega)
  rw [show p + 2 * j + 0 - 2 * j = p from by omega] at h2
  have h3 : rjBundleProj (p + j) (q + j) *
      (jwAt (p + j + (q + j)) 0 p * jwAt (p + j + (q + j)) (p + 2 * j) q) =
        rjBundleProj (p + j) (q + j) :=
    rj_mul_mul_absorb_right_fusionBasic _ _ _ _ (rj_jwAt_mul_jwAt_comm_fusionBasic _ _ _)
      (jwAt_mul_jwAt_of_le _ 0 (p + j) 0 p le_rfl (by omega))
      (jwAt_mul_jwAt_of_le _ (p + j) (q + j) (p + 2 * j) q (by omega) (by omega))
  have hP : rjBundleProj p q = jwAt (p + q) 0 p * jwAt (p + q) p q := rfl
  rw [Matrix.mul_assoc, hP, ← Matrix.mul_assoc _ (jwAt (p + q) 0 p), ← h1,
    Matrix.mul_assoc _ _ (jwAt (p + q) p q), ← h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_assoc (rjBundleProj (p + j) (q + j)), h3]

/-- A nest of `j` cups in the middle of `f_(p+j) ⊗ f_(q+j)` is preceded by `f_p ⊗ f_q` for
free. -/
theorem rjBundleProj_mul_cupThick_mul_bundleProj (p q j : ℕ) :
    rjBundleProj p q * skPlace (p + q) (p + j + (q + j)) p (cupThick j) *
        rjBundleProj (p + j) (q + j) =
      skPlace (p + q) (p + j + (q + j)) p (cupThick j) * rjBundleProj (p + j) (q + j) := by
  have h1 := jwAt_mul_skPlace_of_le (p + q) (p + j + (q + j)) 0 p p (cupThick j)
    (by omega) (by omega) (by omega)
  have h2 := rj_jwAt_mul_skPlace_of_ge_fusionBasic (p + q) (p + j + (q + j)) p q p (cupThick j)
    (by omega) (by omega) (by omega)
  rw [show p + 2 * j - 0 = p + 2 * j from by omega] at h2
  have h3 : jwAt (p + j + (q + j)) 0 p * jwAt (p + j + (q + j)) (p + 2 * j) q *
      rjBundleProj (p + j) (q + j) = rjBundleProj (p + j) (q + j) :=
    rj_mul_mul_absorb_left_fusionBasic _ _ _ _ (rj_jwAt_mul_jwAt_comm_fusionBasic _ _ _)
      (jwAt_mul_jwAt_of_ge _ 0 (p + j) 0 p le_rfl (by omega))
      (jwAt_mul_jwAt_of_ge _ (p + j) (q + j) (p + 2 * j) q (by omega) (by omega))
  have hP : rjBundleProj p q = jwAt (p + q) 0 p * jwAt (p + q) p q := rfl
  rw [hP, Matrix.mul_assoc (jwAt (p + q) 0 p), h2, ← Matrix.mul_assoc, h1,
    Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (jwAt (p + j + (q + j)) 0 p), h3]

end AJConjecture
