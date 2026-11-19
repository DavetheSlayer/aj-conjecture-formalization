import Mathlib
import AJHandoff.TorusInput.RJFusionTwistCap
import AJConjecture.SkeinJwThickCross
import AJConjecture.SkeinHalfTwistFusion
import AJConjecture.SkeinThickCupAdd

/-!
# The full twist on a channel (node RA1.7)

`J_(a,b) π_j = (θ_(a+b-2j)/(θ_a θ_b)) π_j`, and `J_(a,b)` commutes with `f_a ⊗ f_b`. The equal
case is `halfTwist_mul_fusionProj` (`AJConjecture.SkeinHalfTwistFusion`), for the half twist.

Route. Commutation: each crossing exchanges the two projectors
(`jwAt_mul_braidMatrix_thickCross_fst`, `_snd`). Eigenvalue: induction on `j`, peeling the
innermost cap as in `RJFusionInclProj`. `J_(a+1,b+1) = X_(a+1,b+1) X_(b+1,a+1)`; the cap
`cap_a` (joining the two middle strands after `J`) is pulled back through `X_(b+1,a+1)`
(`rj_bundleProj_mul_thickCross_mul_cap` with the bundles exchanged; the projector
`f_(b+1) ⊗ f_(a+1)` in front is obtained by sliding `f_(a+1) ⊗ f_(b+1)` through
`X_(a+1,b+1)`), then through `X_(a+1,b+1)`, giving `t^(-2(a+b+3)) cap_a J_(a,b)`. For `j = 0`:
all `2ab` crossings of `J` lie
inside the block of `f_(a+b)` (`braidMatrix_mul_jwAt_of_inside`), eigenvalue `t^(2ab)`. The
scalars agree: `θ_(a+b-2j)/(θ_a θ_b) = t^(2ab - 4j(a+b) + 4j² - 4j)` (`kinkScalar`). Numerically
checked (design notes). Estimate 130–200 lines.
-/

noncomputable section

namespace AJConjecture

/-- A crossing of two bundles exchanges the projectors `f_A ⊗ f_B` and `f_B ⊗ f_A`. -/
private theorem rj_bundleJw_mul_thickCross_twistEigen (n A B : ℕ) (hn : A + B ≤ n) :
    jwAt n 0 A * jwAt n A B * braidMatrix n (thickCross A B 0 true) =
      braidMatrix n (thickCross A B 0 true) * (jwAt n 0 B * jwAt n B A) := by
  have h1 := jwAt_mul_braidMatrix_thickCross_fst n A B 0 true (by omega)
  have h2 := jwAt_mul_braidMatrix_thickCross_snd n A B 0 true (by omega)
  rw [Nat.zero_add] at h1 h2
  have hc : jwAt n B A * jwAt n 0 B = jwAt n 0 B * jwAt n B A :=
    jwAt_mul_eq_mul_jwAt n n B B (jwAt n 0 B) A fun l _ ↦
      (jwAt_commute_tlGenF n 0 B (B + l) (Or.inr (by omega))).eq.symm
  rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc, hc]

/-- The cap pulled back through a crossing, in a dimension `n` given by a hypothesis. -/
private theorem rj_cap_pull_twistEigen (a b n : ℕ) (hn : a + 1 + (b + 1) = n) :
    jwAt n 0 (a + 1) * jwAt n (a + 1) (b + 1) * braidMatrix n (thickCross (a + 1) (b + 1) 0 true) *
        skPlace n (a + b) b skCap =
      -((RatFunc.X : RatFunc ℚ) ^ (-((a : ℤ) + b + 3))) •
        (jwAt n 0 (a + 1) * jwAt n (a + 1) (b + 1) * skPlace n (a + b) a skCap *
          braidMatrix (a + b) (thickCross a b 0 true)) := by
  subst hn
  exact rj_bundleProj_mul_thickCross_mul_cap a b

/-- The full twist of the bundles `a + 1`, `b + 1` against the cap between them. -/
private theorem rj_fullTwist_cap_twistEigen (a b : ℕ) :
    rjBundleProj (a + 1) (b + 1) * rjFullTwist (a + 1) (b + 1) *
        skPlace (a + 1 + (b + 1)) (a + b) a skCap =
      ((RatFunc.X : RatFunc ℚ) ^ (-((b : ℤ) + a + 3)) *
          (RatFunc.X : RatFunc ℚ) ^ (-((a : ℤ) + b + 3))) •
        (rjBundleProj (a + 1) (b + 1) * skPlace (a + 1 + (b + 1)) (a + b) a skCap *
          rjFullTwist a b) := by
  have e1 := rj_bundleJw_mul_thickCross_twistEigen (a + 1 + (b + 1)) (a + 1) (b + 1) le_rfl
  have e2 := rj_cap_pull_twistEigen b a (a + 1 + (b + 1)) (by omega)
  have e3 := rj_cap_pull_twistEigen a b (a + 1 + (b + 1)) rfl
  rw [show b + a = a + b from by omega] at e2
  rw [rjBundleProj, rjFullTwist, rjFullTwist, braidMatrix_append, braidMatrix_append,
    ← Matrix.mul_assoc, e1, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ _ (skPlace _ _ _ _),
    e2, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← e1, e3, Matrix.smul_mul,
    smul_smul]
  simp only [Matrix.mul_assoc, neg_mul_neg]

/-- The full twist of two bundles commutes with `f_a ⊗ f_b`. -/
theorem rj_fullTwist_mul_bundleProj (a b : ℕ) :
    rjFullTwist a b * rjBundleProj a b = rjBundleProj a b * rjFullTwist a b := by
  have e1 := rj_bundleJw_mul_thickCross_twistEigen (a + b) a b le_rfl
  have e2 := rj_bundleJw_mul_thickCross_twistEigen (a + b) b a (by omega)
  symm
  rw [rjBundleProj, rjFullTwist, braidMatrix_append,
    ← Matrix.mul_assoc (jwAt (a + b) 0 a * jwAt (a + b) a b), e1, Matrix.mul_assoc, e2]
  simp only [Matrix.mul_assoc]

/-- One peeling step of the eigenvalue equation: the full twist of the bundles `a + 1`, `b + 1`
on `(f_(a+1) ⊗ f_(b+1)) cap (f_a ⊗ f_b) R`. -/
private theorem rj_fullTwist_step_twistEigen (a b m : ℕ) (R : SkMat (a + b) m) (κ : RatFunc ℚ)
    (ih : rjFullTwist a b * (rjBundleProj a b * R) = κ • (rjBundleProj a b * R)) :
    rjFullTwist (a + 1) (b + 1) * (rjBundleProj (a + 1) (b + 1) *
        skPlace (a + 1 + (b + 1)) (a + b) a skCap * (rjBundleProj a b * R)) =
      ((RatFunc.X : RatFunc ℚ) ^ (-((b : ℤ) + a + 3)) *
          (RatFunc.X : RatFunc ℚ) ^ (-((a : ℤ) + b + 3)) * κ) •
        (rjBundleProj (a + 1) (b + 1) * skPlace (a + 1 + (b + 1)) (a + b) a skCap *
          (rjBundleProj a b * R)) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc (rjFullTwist _ _), rj_fullTwist_mul_bundleProj,
    rj_fullTwist_cap_twistEigen, Matrix.smul_mul, Matrix.mul_assoc _ (rjFullTwist a b), ih,
    Matrix.mul_smul, smul_smul]

/-- The eigenvalue of the full twist under a peeling step. -/
private theorem rj_twistRatio_step_twistEigen (A B M : ℕ) :
    (RatFunc.X : RatFunc ℚ) ^ (-((B : ℤ) + A + 3)) *
        (RatFunc.X : RatFunc ℚ) ^ (-((A : ℤ) + B + 3)) *
        (kinkScalar M / (kinkScalar A * kinkScalar B)) =
      kinkScalar M / (kinkScalar (A + 1) * kinkScalar (B + 1)) := by
  have hk : ∀ n : ℕ, kinkScalar (n + 1) =
      -((RatFunc.X : RatFunc ℚ) ^ (2 * (n : ℤ) + 3)) * kinkScalar n := fun n ↦ by
    rw [kinkScalar, kinkScalar, pow_succ,
      show ((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) + 2) =
        2 * (n : ℤ) + 3 + n * (n + 2) from by push_cast; ring, zpow_add₀ RatFunc.X_ne_zero]
    ring
  have hX : (RatFunc.X : RatFunc ℚ) ^ (-((B : ℤ) + A + 3)) *
      (RatFunc.X : RatFunc ℚ) ^ (-((A : ℤ) + B + 3)) =
        ((RatFunc.X : RatFunc ℚ) ^ (2 * (A : ℤ) + 3) *
          (RatFunc.X : RatFunc ℚ) ^ (2 * (B : ℤ) + 3))⁻¹ := by
    rw [← zpow_add₀ RatFunc.X_ne_zero, ← zpow_add₀ RatFunc.X_ne_zero, ← zpow_neg]
    congr 1
    ring
  rw [hk A, hk B, hX]
  ring

/-- The full twist on the projector of all the strands. -/
private theorem rj_twistRatio_zero_twistEigen (p q : ℕ) :
    (RatFunc.X : RatFunc ℚ) ^ ((1 : ℤ) * ((p * q + q * p : ℕ) : ℤ)) =
      kinkScalar (p + q) / (kinkScalar p * kinkScalar q) := by
  have hp : kinkScalar p ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (zpow_ne_zero _ RatFunc.X_ne_zero)
  have hq : kinkScalar q ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (zpow_ne_zero _ RatFunc.X_ne_zero)
  rw [eq_div_iff (mul_ne_zero hp hq), kinkScalar, kinkScalar, kinkScalar, pow_add]
  rw [show (-1 : RatFunc ℚ) ^ p * (-1) ^ q *
      (RatFunc.X : RatFunc ℚ) ^ (((p + q : ℕ) : ℤ) * (((p + q : ℕ) : ℤ) + 2)) =
      (-1) ^ p * (-1) ^ q *
        ((RatFunc.X : RatFunc ℚ) ^ ((1 : ℤ) * ((p * q + q * p : ℕ) : ℤ)) *
        ((RatFunc.X : RatFunc ℚ) ^ ((p : ℤ) * ((p : ℤ) + 2)) *
          (RatFunc.X : RatFunc ℚ) ^ ((q : ℤ) * ((q : ℤ) + 2)))) from by
    rw [← zpow_add₀ RatFunc.X_ne_zero, ← zpow_add₀ RatFunc.X_ne_zero]
    congr 2
    push_cast
    ring]
  ring

/-- A placed nest of `c + 1` caps: the innermost cap, then the placed nest of `c` caps (free
sizes). -/
private theorem rj_skPlace_capThick_succ_inner_twistEigen (c M m n' i j : ℕ) (h : i + 2 * c ≤ m)
    (h' : m = n' + 2 * c) (hM : M = m + 2) (hj : j = i + c) :
    skPlace M n' i (capThick (c + 1)) = skPlace M m j skCap * skPlace m n' i (capThick c) := by
  subst hj hM
  rw [capThick_succ_inner,
    skPlace_mul (m + 2) m n' i _ (capThick c) (by omega) (by omega) (by omega),
    skPlace_skPlace (m + 2) m i c skCap (by omega) (by omega) (by omega) (by omega)]

/-- The eigenvalue equation with the output sizes written as `p + q` and `p`. -/
private theorem rj_fullTwist_mul_fusionProj_clean (p q j : ℕ) :
    rjFullTwist (p + j) (q + j) *
        (rjBundleProj (p + j) (q + j) * skPlace (p + j + (q + j)) (p + q) p (capThick j) *
          jwAt (p + q) 0 (p + q)) =
      (kinkScalar (p + q) / (kinkScalar (p + j) * kinkScalar (q + j))) •
        (rjBundleProj (p + j) (q + j) * skPlace (p + j + (q + j)) (p + q) p (capThick j) *
          jwAt (p + q) 0 (p + q)) := by
  induction j with
  | zero =>
    rw [show p + 0 = p from rfl, show q + 0 = q from rfl, capThick_zero,
      skPlace_one (p + q) p 0 (by omega), Matrix.mul_one, rjBundleProj, Matrix.mul_assoc,
      jwAt_mul_jwAt_of_ge _ 0 (p + q) p q (by omega) (by omega),
      jwAt_mul_jwAt_of_ge _ 0 (p + q) 0 p le_rfl (by omega), rjFullTwist,
      braidMatrix_mul_jwAt_of_inside (p + q) 0 (p + q) _ fun g hg ↦ by
        rcases List.mem_append.1 hg with hg | hg <;>
        · have := mem_thickCross hg
          omega,
      writhe_eq_of_forall_sign _ true fun g hg ↦ by
        rcases List.mem_append.1 hg with hg | hg <;> exact (mem_thickCross hg).2.2,
      List.length_append, length_thickCross, length_thickCross]
    simp only [↓reduceIte]
    rw [rj_twistRatio_zero_twistEigen]
  | succ j ih =>
    have hcap := rj_skPlace_capThick_succ_inner_twistEigen j (p + (j + 1) + (q + (j + 1)))
      (p + j + (q + j)) (p + q) p (p + j) (by omega) (by omega) (by omega) (by omega)
    have hins := rjBundleProj_mul_capThick_mul_bundleProj (p + j) (q + j) 1
    rw [capThick_one] at hins
    rw [hcap, ← Nat.add_assoc p j 1, ← Nat.add_assoc q j 1,
      ← rj_twistRatio_step_twistEigen (p + j) (q + j)]
    have e : rjBundleProj (p + j + 1) (q + j + 1) *
        skPlace (p + j + 1 + (q + j + 1)) (p + j + (q + j)) (p + j) skCap *
          (rjBundleProj (p + j) (q + j) *
            (skPlace (p + j + (q + j)) (p + q) p (capThick j) * jwAt (p + q) 0 (p + q))) =
        rjBundleProj (p + j + 1) (q + j + 1) *
          (skPlace (p + j + 1 + (q + j + 1)) (p + j + (q + j)) (p + j) skCap *
            skPlace (p + j + (q + j)) (p + q) p (capThick j)) * jwAt (p + q) 0 (p + q) := by
      rw [← Matrix.mul_assoc, hins]
      simp only [Matrix.mul_assoc]
    rw [Matrix.mul_assoc (rjBundleProj (p + j) (q + j))] at ih
    rw [← e]
    exact rj_fullTwist_step_twistEigen (p + j) (q + j) _ _ _ ih

/-- The full twist acts on the fusion map of the channel `j` by `θ_(a+b-2j)/(θ_a θ_b)`. -/
theorem rj_fullTwist_mul_fusionProj (a b j : ℕ) (hj : j ≤ min a b) :
    rjFullTwist a b * rjFusionProj a b j = rjTwistRatio a b j • rjFusionProj a b j := by
  obtain ⟨p, rfl⟩ : ∃ p, a = p + j := ⟨a - j, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, b = q + j := ⟨b - j, by omega⟩
  rw [rjFusionProj, rjTwistRatio, show p + j + (q + j) - 2 * j = p + q from by omega,
    show p + j - j = p from by omega]
  exact rj_fullTwist_mul_fusionProj_clean p q j

end AJConjecture
