import Mathlib
import AJHandoff.TorusInput.RJFusionBasic
import AJConjecture.SkeinHalfTwistCap
import AJConjecture.SkeinJwAbsorb

/-!
# Pulling a cap back through a crossing of two unequal bundles (node RA1.6)

With projectors, `(f_(a+1) ⊗ f_(b+1)) X_(a+1,b+1) cap_b = -t^(-(a+b+3)) (f_(a+1) ⊗ f_(b+1)) cap_a
X_(a,b)`: after the first bundle `(x, A')` crosses the second `(B', y)`, the cap joining `y` and
`x` is pulled back; it costs a curl and leaves the crossing `X_(a,b)` of `A'` and `B'`. The equal
case is `twoBundleProj_mul_halfTwist_mul_skCap` (`AJConjecture.SkeinHalfTwistCap`).

Route. The proof of `halfTwist_mul_skCap` is written for thick crossings of arbitrary sizes and
goes through unchanged with `p + 1`, `p + 1` replaced by `a + 1`, `b + 1`: split
`X_(a+1,b+1) = P U σ` (`thickGen_add_left`, `braidMatrix_thickGen_add_right`), the curl
`crossingF_mul_capAt`, the leg move (L) `braidMatrix_thickCross_mul_capAt_leg` twice, (N2)
`braidMatrix_mul_thickCross_snd`, far commutation; finally `f_(a+1)` and `f_(b+1)` absorb the `a`
and `b` crossings inside their blocks (`jwAt_mul_braidMatrix_of_inside`), giving
`-t^(-3) t^(-a) t^(-b)`. Numerically checked for `1 ≤ a, b ≤ 4` (design notes). Estimate
200–280 lines.
-/

noncomputable section

namespace AJConjecture

/-- The chain of rewritings of the crossing against a cap, from its seven steps. -/
private theorem rj_thickCross_cap_chain_twistCap {N n : ℕ} (κ : RatFunc ℚ)
    (S P U σ V V' P₁ P₂ U' : SkMat N N) (Ca C₀ Ca' : SkMat N n) (T : SkMat n n)
    (e1 : S = P * (U * σ)) (e2 : σ * Ca = κ • Ca) (e3 : U * Ca = V * C₀)
    (e4 : P * V = V' * P) (e5 : P = P₁ * P₂) (e6 : P₂ * C₀ = C₀ * T)
    (e7 : P₁ * C₀ = U' * Ca') :
    S * Ca = κ • (V' * U' * Ca' * T) := by
  calc S * Ca = P * (U * (σ * Ca)) := by rw [e1]; simp only [Matrix.mul_assoc]
    _ = κ • (P * (U * Ca)) := by rw [e2]; simp only [Matrix.mul_smul]
    _ = κ • (P * V * C₀) := by rw [e3, Matrix.mul_assoc]
    _ = κ • (V' * P * C₀) := by rw [e4]
    _ = κ • (V' * (P₁ * (P₂ * C₀))) := by rw [e5]; simp only [Matrix.mul_assoc]
    _ = κ • (V' * (P₁ * C₀) * T) := by rw [e6]; simp only [Matrix.mul_assoc]
    _ = κ • (V' * U' * Ca' * T) := by rw [e7]; simp only [Matrix.mul_assoc]

/-- The crossing of two unequal bundles against the cap, without projectors. -/
private theorem rj_thickGen_mul_capAt_twistCap (a b : ℕ) :
    braidMatrix (a + b + 2) (thickGen (a + 1) (b + 1) 0 true) * capAt (a + b) b =
      (-(RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ)) •
        (braidMatrix (a + b + 2) (thickCross b 1 (a + 1) false) *
          braidMatrix (a + b + 2) (thickCross 1 a 0 false) * capAt (a + b) a *
            braidMatrix (a + b) (thickGen a b 0 true)) := by
  refine rj_thickCross_cap_chain_twistCap _ _ (braidMatrix _ (thickGen a (b + 1) 1 true))
    (braidMatrix _ (thickGen 1 b 0 true)) (crossingF _ (b, true))
    (braidMatrix _ (thickCross b 1 1 false)) _ (braidMatrix _ (thickGen a 1 1 true))
    (braidMatrix _ (thickGen a b 2 true)) _ _ (capAt (a + b) 0) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [show thickGen (a + 1) (b + 1) 0 true = thickGen (1 + a) (b + 1) 0 true from by
        rw [Nat.add_comm 1 a], thickGen_add_left, braidMatrix_append,
      braidMatrix_thickGen_add_right _ 1 b 1 0]
    simp only [Nat.zero_add]
    rw [show thickGen 1 1 b true = [(b, true)] from rfl, braidMatrix_cons,
      braidMatrix_nil, Matrix.mul_one]
  · exact (crossingF_mul_capAt (a + b) b true (by omega)).trans (by simp only [↓reduceIte])
  · have h := braidMatrix_thickCross_mul_capAt_leg (a + b) b 0 true (by omega)
    simp only [Nat.zero_add, Bool.not_true] at h
    exact h
  · have h := braidMatrix_mul_thickCross_snd (a + b + 2) a (b + 1) 1 true
      (thickCross b 1 0 false) (by omega) fun g hg ↦ by
        have := mem_thickCross hg
        omega
    rw [← thickCross_add_off, ← thickCross_add_off] at h
    simp only [Nat.zero_add] at h
    rw [Nat.add_comm 1 a] at h
    exact h.symm
  · have h := braidMatrix_thickGen_add_right (a + b + 2) a 1 b 1
    rw [Nat.add_comm 1 b] at h
    exact h
  · have h := capAt_mul_braidMatrix_of_le (a + b) 0 (thickGen a b 0 true)
      fun _ _ ↦ Nat.zero_le _
    rw [show (thickGen a b 0 true).map (fun g ↦ (g.1 + 2, g.2)) = thickGen a b 2 true from
      (thickCross_add_off a b 0 2 true).symm] at h
    exact h.symm
  · have h := braidMatrix_thickCross_mul_capAt_leg (a + b) a 0 false (by omega)
    simp only [Nat.zero_add, Bool.not_false] at h
    exact h.symm

/-- The cap pulled back through the crossing of two unequal bundles with projectors. -/
theorem rj_bundleProj_mul_thickCross_mul_cap (a b : ℕ) :
    rjBundleProj (a + 1) (b + 1) *
        braidMatrix (a + 1 + (b + 1)) (thickCross (a + 1) (b + 1) 0 true) *
        skPlace (a + 1 + (b + 1)) (a + b) b skCap =
      -((RatFunc.X : RatFunc ℚ) ^ (-((a : ℤ) + b + 3))) •
        (rjBundleProj (a + 1) (b + 1) * skPlace (a + 1 + (b + 1)) (a + b) a skCap *
          braidMatrix (a + b) (thickCross a b 0 true)) := by
  have hc : jwAt (a + b + 2) 0 (a + 1) * jwAt (a + b + 2) (a + 1) (b + 1) =
      jwAt (a + b + 2) (a + 1) (b + 1) * jwAt (a + b + 2) 0 (a + 1) :=
    (jwAt_mul_eq_mul_jwAt _ _ (a + 1) (a + 1) (jwAt (a + b + 2) 0 (a + 1)) (b + 1) fun l _ ↦
      (jwAt_commute_tlGenF _ 0 (a + 1) (a + 1 + l) (Or.inr (by omega))).eq.symm).symm
  have hU := jwAt_mul_braidMatrix_of_inside (a + b + 2) 0 (a + 1) (thickCross 1 a 0 false)
    fun g hg ↦ by
      have := mem_thickCross hg
      omega
  have hV := jwAt_mul_braidMatrix_of_inside (a + b + 2) (a + 1) (b + 1)
    (thickCross b 1 (a + 1) false) fun g hg ↦ by
      have := mem_thickCross hg
      omega
  rw [writhe_eq_of_forall_sign _ false fun g hg ↦ (mem_thickCross hg).2.2,
    length_thickCross] at hU hV
  have hk := rj_thickGen_mul_capAt_twistCap a b
  rw [rjBundleProj, show a + 1 + (b + 1) = a + b + 2 from by omega]
  change _ * braidMatrix (a + b + 2) (thickGen (a + 1) (b + 1) 0 true) * capAt (a + b) b =
    _ • (_ * capAt (a + b) a * braidMatrix (a + b) (thickGen a b 0 true))
  have hF : jwAt (a + b + 2) 0 (a + 1) * jwAt (a + b + 2) (a + 1) (b + 1) *
      (braidMatrix (a + b + 2) (thickCross b 1 (a + 1) false) *
        braidMatrix (a + b + 2) (thickCross 1 a 0 false)) =
      ((RatFunc.X : RatFunc ℚ) ^ (-1 * ((b * 1 : ℕ) : ℤ)) *
        (RatFunc.X : RatFunc ℚ) ^ (-1 * ((1 * a : ℕ) : ℤ))) •
        (jwAt (a + b + 2) 0 (a + 1) * jwAt (a + b + 2) (a + 1) (b + 1)) := by
    simp only [Bool.false_eq_true, ite_false] at hU hV
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (jwAt (a + b + 2) (a + 1) (b + 1)), hV,
      Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hc, Matrix.mul_assoc, hU,
      Matrix.mul_smul, smul_smul]
  rw [Matrix.mul_assoc, hk, Matrix.mul_smul, Matrix.mul_assoc (braidMatrix _ _ * _),
    ← Matrix.mul_assoc (jwAt _ 0 (a + 1) * _), hF,
    Matrix.smul_mul, smul_smul, ← Matrix.mul_assoc]
  congr 1
  rw [neg_mul, ← zpow_add₀ RatFunc.X_ne_zero, ← zpow_add₀ RatFunc.X_ne_zero]
  congr 2
  push_cast
  ring

end AJConjecture
