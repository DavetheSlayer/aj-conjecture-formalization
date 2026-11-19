import Mathlib
import AJHandoff.TorusInput.RJFusionOneSided
import AJConjecture.SkeinJwCapKill

/-!
# The first turnback on a fusion map (node RA1.4)

`D_1 π_j = ν_j π_j` with `ν_j = -[j][a+b+1-j]/([a][b])`: the unequal version of
`turnback_one_mul_fusionProj` (`AJConjecture.SkeinFusionBasic`).

Route. If `j < min a b`, write `a = p + 1 + j`, `b = q + 1 + j` and apply
`rj_turnbackOne_mul_capNest`, followed by `f_(p+q+2)`: the second term contains
`cup · (f_(p+1) ⊗ f_(q+1)) · f_(p+q+2) = cup · f_(p+q+2) = 0` (`jwAt_mul_jwAt_of_le`,
`cupAt_mul_jwAt`: both legs of the cup enter the block). If `j = a ≤ b` or `j = b ≤ a`, use the
full versions. For `a = 0` or `b = 0` both sides vanish (`ν_0 = 0`, and `e_(a-1)` lies inside a
block or does not fit). Sizes: rewrite `a + b - 2j` by `omega` facts before applying the
`(p, q, r)` statements. Estimate 80–120 lines.
-/

noncomputable section

namespace AJConjecture

/-- `D_1` absorbs `f_a ⊗ f_b` on the right. -/
private theorem rj_turnbackOne_mul_bundleProj (a b : ℕ) :
    rjTurnbackOne a b * rjBundleProj a b = rjTurnbackOne a b := by
  rw [rjTurnbackOne, Matrix.mul_assoc, rjBundleProj_mul_self]

/-- A cup inside the block of a projector kills it (free sizes). -/
private theorem rj_skCup_mul_jwAt_eq_zero (n N p : ℕ) (hN : N = n + 2) (hp : p + 2 ≤ N) :
    skPlace n N p skCup * jwAt N 0 N = 0 := by
  subst hN
  exact cupAt_mul_jwAt n 0 (n + 2) p (by omega) (by omega)

/-- The projector on all strands absorbs `f_(p+1) ⊗ f_(q+1)`. -/
private theorem rj_bundleProj_mul_jwAt_full (p q : ℕ) :
    rjBundleProj (p + 1) (q + 1) * jwAt (p + 1 + (q + 1)) 0 (p + 1 + (q + 1)) =
      jwAt (p + 1 + (q + 1)) 0 (p + 1 + (q + 1)) := by
  rw [rjBundleProj, Matrix.mul_assoc,
    jwAt_mul_jwAt_of_ge _ 0 (p + 1 + (q + 1)) (p + 1) (q + 1) (by omega) (by omega),
    jwAt_mul_jwAt_of_ge _ 0 (p + 1 + (q + 1)) 0 (p + 1) le_rfl (by omega)]

/-- The first turnback acts on the fusion map of the channel `j` by `ν_j`. -/
theorem rj_turnbackOne_mul_fusionProj (a b j : ℕ) (hj : j ≤ min a b) :
    rjTurnbackOne a b * rjFusionProj a b j = rjTurnbackEigen a b j • rjFusionProj a b j := by
  have hπ : rjTurnbackOne a b * rjFusionProj a b j =
      rjTurnbackOne a b * skPlace (a + b) (a + b - 2 * j) (a - j) (capThick j) *
        jwAt (a + b - 2 * j) 0 (a + b - 2 * j) := by
    rw [rjFusionProj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, rj_turnbackOne_mul_bundleProj]
  rw [hπ, rjFusionProj]
  rcases (show j = a ∨ j = b ∨ (j < a ∧ j < b) by omega) with h | h | ⟨ha, hb⟩
  · subst h
    obtain ⟨q, rfl⟩ : ∃ q, b = j + q := ⟨b - j, by omega⟩
    rw [show j + (j + q) - 2 * j = q from by omega, Nat.sub_self,
      rj_turnbackOne_mul_capNest_full_left j q, Matrix.smul_mul]
  · subst h
    obtain ⟨p, rfl⟩ : ∃ p, a = p + j := ⟨a - j, by omega⟩
    rw [show p + j + j - 2 * j = p from by omega, Nat.add_sub_cancel,
      rj_turnbackOne_mul_capNest_full_right p j, Matrix.smul_mul]
  · obtain ⟨p, rfl⟩ : ∃ p, a = p + 1 + j := ⟨a - j - 1, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, b = q + 1 + j := ⟨b - j - 1, by omega⟩
    rw [show p + 1 + j + (q + 1 + j) - 2 * j = p + 1 + (q + 1) from by omega,
      Nat.add_sub_cancel, rj_turnbackOne_mul_capNest p q j, Matrix.add_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_assoc _ (rjBundleProj (p + 1) (q + 1)),
      rj_bundleProj_mul_jwAt_full, Matrix.mul_assoc _ (skPlace _ _ p skCup),
      rj_skCup_mul_jwAt_eq_zero _ _ p (by omega) (by omega), Matrix.mul_zero, smul_zero,
      add_zero]

end AJConjecture
