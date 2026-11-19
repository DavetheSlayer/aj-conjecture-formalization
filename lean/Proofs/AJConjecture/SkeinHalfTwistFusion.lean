import Mathlib
import AJConjecture.SkeinFusionNest
import AJConjecture.SkeinHalfTwistCap

/-!
# The half twist on the fusion maps

`Σ_c^{±1} π_n = λ_{c,n}^{±1} π_n` with `λ_{c,n} = (-1)^(c-n) t^(2n(n+1) - c(c+2))`
(`AJConjecture.claspAlgHalfTwistEigen`), for two bundles of `c = n + m` strands. Induction on `m`.
For `m = 0`, `π = f_{2n}` absorbs the `n²` crossings of the half twist
(`AJConjecture.braidMatrix_mul_jwAt_of_inside`, the mirror of
`AJConjecture.jwAt_mul_braidMatrix_of_inside` by transposition), and `λ_{n,n} = t^(n²)`. For `m +
1`,
`π_{n,m+1} = (f ⊗ f) · cap · π_{n,m}` (`AJConjecture.twoBundleProj_mul_capThick_mul_fusionProj`
with one
cap, `AJConjecture.capThick_one`); the half twist commutes with `f ⊗ f`, passes the cap with the
scalar `-t^{∓(2c+3)}` (`AJConjecture.twoBundleProj_mul_halfTwist_mul_skCap`), acts on `π_{n,m}` by
induction, and `λ_{c+1,n} = -t^{-(2c+3)} λ_{c,n}`.
-/

namespace AJConjecture

/-- A braid word inside the block of `f_k` is absorbed on the left as `t` to the power of its
writhe. -/
theorem braidMatrix_mul_jwAt_of_inside (n i k : ℕ) (w : BraidWord)
    (hw : ∀ g ∈ w, i ≤ g.1 ∧ g.1 + 1 < i + k) :
    braidMatrix n w * jwAt n i k = (RatFunc.X : RatFunc ℚ) ^ (writhe w) • jwAt n i k := by
  induction w with
  | nil => rw [braidMatrix_nil, Matrix.one_mul, writhe, List.map_nil, List.sum_nil, zpow_zero,
      one_smul]
  | cons g w ih =>
    obtain ⟨j, s⟩ := g
    have hg := hw (j, s) List.mem_cons_self
    have ih' := ih fun g' hg' ↦ hw g' (List.mem_cons_of_mem _ hg')
    have hcons : braidMatrix n ((j, s) :: w) = crossingF n (j, s) * braidMatrix n w := by
      rw [braidMatrix, List.map_cons, List.prod_cons, braidMatrix]
    have hwr : writhe ((j, s) :: w) = (if s then (1 : ℤ) else -1) + writhe w := by
      rw [writhe, List.map_cons, List.sum_cons, writhe]
    rw [hcons, Matrix.mul_assoc, ih', Matrix.mul_smul, crossingF_mul_jwAt n i k j s hg.1 hg.2,
      smul_smul, hwr, zpow_add₀ RatFunc.X_ne_zero, mul_comm]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, zpow_neg, zpow_one]
    · simp only [↓reduceIte, zpow_one]

/-- The half-twist eigenvalues for consecutive bundle sizes. -/
theorem halfTwistEigen_succ (c n : ℕ) :
    claspAlgHalfTwistEigen (c + 1) n =
      -(RatFunc.X : RatFunc ℚ) ^ (-(2 * (c : ℤ) + 3)) * claspAlgHalfTwistEigen c n := by
  rw [claspAlgHalfTwistEigen, claspAlgHalfTwistEigen, neg_mul, mul_left_comm,
    ← zpow_add₀ RatFunc.X_ne_zero, add_right_comm, pow_succ, mul_neg_one, neg_mul]
  congr 3
  push_cast
  ring

/-- The half-twist eigenvalue of the top channel. -/
theorem halfTwistEigen_self (n : ℕ) :
    claspAlgHalfTwistEigen n n = (RatFunc.X : RatFunc ℚ) ^ ((n : ℤ) ^ 2) := by
  rw [claspAlgHalfTwistEigen, Even.neg_one_pow ⟨n, rfl⟩, one_mul]
  congr 1
  ring

/-- The fusion map without caps is the projector `f_{2n}`. -/
private theorem fusionProj_zero_halfTwistFusion (n : ℕ) :
    fusionProj n 0 = jwAt (2 * n) 0 (2 * n) := by
  change twoBundleProj n * skPlace (2 * n) (2 * n) n (capThick 0) * jwAt (2 * n) 0 (2 * n) = _
  rw [capThick_zero, skPlace_one (2 * n) n 0 (by omega), Matrix.mul_one,
    twoBundleProj, Matrix.mul_assoc,
    jwAt_mul_jwAt_of_ge (2 * n) 0 (2 * n) n n (by omega) (by omega),
    jwAt_mul_jwAt_of_ge (2 * n) 0 (2 * n) 0 n (by omega) (by omega)]

/-- The half twist on the projector of all the strands: the eigenvalue of the top channel. -/
private theorem halfTwist_mul_jwAt_halfTwistFusion (n : ℕ) (s : Bool) :
    halfTwist n s * jwAt (2 * n) 0 (2 * n) =
      (if s then claspAlgHalfTwistEigen n n else (claspAlgHalfTwistEigen n n)⁻¹) •
        jwAt (2 * n) 0 (2 * n) := by
  have hT : halfTwist n s = braidMatrix (2 * n) (thickCross n n 0 s) := by
    rw [halfTwist, cableGen_eq_thickCross]
    rfl
  rw [hT, braidMatrix_mul_jwAt_of_inside (2 * n) 0 (2 * n) _ fun g hg ↦ by
      have := mem_thickCross hg
      omega,
    writhe_eq_of_forall_sign _ s fun g hg ↦
      (mem_thickCross hg).2.2,
    length_thickCross, halfTwistEigen_self]
  congr 1
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, ← zpow_neg]
    congr 1
    push_cast
    ring
  · simp only [↓reduceIte]
    congr 1
    push_cast
    ring

/-- The scalar of the half twist against a cap multiplies the eigenvalues. -/
private theorem halfTwistEigen_step_halfTwistFusion (c n : ℕ) (s : Bool) :
    (if s then -(RatFunc.X : RatFunc ℚ) ^ (-(2 * (c : ℤ) + 3))
        else -(RatFunc.X : RatFunc ℚ) ^ (2 * (c : ℤ) + 3)) *
      (if s then claspAlgHalfTwistEigen c n else (claspAlgHalfTwistEigen c n)⁻¹) =
      if s then claspAlgHalfTwistEigen (c + 1) n else (claspAlgHalfTwistEigen (c + 1) n)⁻¹ := by
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [halfTwistEigen_succ, mul_inv, inv_neg, ← zpow_neg, neg_neg]
  · simp only [↓reduceIte]
    rw [halfTwistEigen_succ]

/-- The half twist acts on the fusion map `π` by the eigenvalue `λ_{c,n}^{±1}`. -/
theorem halfTwist_mul_fusionProj (n m : ℕ) (s : Bool) :
    halfTwist (n + m) s * fusionProj n m =
      (if s then claspAlgHalfTwistEigen (n + m) n else (claspAlgHalfTwistEigen (n + m) n)⁻¹) •
        fusionProj n m := by
  induction m with
  | zero =>
    rw [fusionProj_zero_halfTwistFusion]
    exact halfTwist_mul_jwAt_halfTwistFusion n s
  | succ m ih =>
    have hnest := twoBundleProj_mul_capThick_mul_fusionProj n m 1
    rw [capThick_one] at hnest
    have hcap := twoBundleProj_mul_halfTwist_mul_skCap (n + m) s
    have hcomm := halfTwist_mul_twoBundleProj (n + m + 1) s
    change halfTwist (n + m + 1) s * fusionProj n (m + 1) =
      (if s then claspAlgHalfTwistEigen (n + m + 1) n
        else (claspAlgHalfTwistEigen (n + m + 1) n)⁻¹) • fusionProj n (m + 1)
    rw [← halfTwistEigen_step_halfTwistFusion]
    change twoBundleProj (n + m + 1) *
      skPlace (2 * (n + m + 1)) (2 * (n + m)) (n + m) skCap * fusionProj n m =
        fusionProj n (m + 1) at hnest
    rw [← hnest, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hcomm, hcap, Matrix.smul_mul,
      Matrix.mul_assoc _ (halfTwist (n + m) s), ih, Matrix.mul_smul, smul_smul]

end AJConjecture
