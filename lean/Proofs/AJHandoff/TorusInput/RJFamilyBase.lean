import Mathlib
import AJHandoff.TorusInput.RJCycleCols
import AJHandoff.TorusInput.RJNatGen
import AJConjecture.SkeinJwBasic
import AJConjecture.SkeinColorReduction

/-!
# The fusion family of one bundle (node RA2.1)

For `r = 1` the family `[(b, f_b, f_b)]` is good: `f_b^{⊗ 1} = f_b`, the colour `b` is in the
spectrum, `c_1 = 1` and `μ_b = θ_b/θ_b = 1`.

Route. The sizes are `b * 1`: use `skPlace (b * 1) b 0 (jwAt b 0 b)` and its transpose-like
partner with free sizes (or rewrite `b * 1 = b` with `Nat.mul_one` inside the existential).
`rjCycleWord 1 = []`, `rjCycleMat b 1 = 1`; `rjColsProj b 1 = jwAt (b*1) 0 b`; `jwAt_mul_self`;
`rjNat_jwAt`; `kinkScalar_ne_zero`. Estimate 40–70 lines.
-/

noncomputable section

namespace AJConjecture

/-- The column projector of a single bundle is `f_b`. -/
private theorem rjColsProj_one_familyBase (b : ℕ) :
    rjColsProj b 1 = jwAt (b * 1) 0 (b * 1) := by
  have h : ∀ n : ℕ, jwAt n 0 b = jwAt n 0 (b * 1) := fun n ↦ by rw [Nat.mul_one]
  rw [rjColsProj, List.range_one, List.map_singleton, List.prod_singleton, Nat.mul_zero, h]

/-- The cabled cyclic braid on one bundle is the identity. -/
private theorem rjCycleMat_one_familyBase (b : ℕ) : rjCycleMat b 1 = 1 :=
  braidMatrix_nil _

/-- The good family of one bundle. -/
theorem rj_goodFamily_one (b : ℕ) : ∃ L, RJGoodFamily b 1 L := by
  refine ⟨[⟨b * 1, (jwAt (b * 1) 0 (b * 1), jwAt (b * 1) 0 (b * 1))⟩], ?_, ?_⟩
  · rw [List.map_singleton, List.sum_singleton, jwAt_mul_self, rjColsProj_one_familyBase]
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    have hE : rjTwistEigen b 1 (b * 1) = 1 := by
      rw [rjTwistEigen, Nat.mul_one, pow_one, div_self (kinkScalar_ne_zero b)]
    have hNat := rjNat_jwAt (b * 1) 0 (b * 1) (by omega)
    simp only [rjColsProj_one_familyBase, rjCycleMat_one_familyBase, one_pow, Matrix.one_mul,
      Matrix.mul_one, hE, one_smul, jwAt_mul_self, hNat, and_self, and_true]
    exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩

end AJConjecture
