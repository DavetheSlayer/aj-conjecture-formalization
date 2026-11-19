import Mathlib
import AJConjecture.SkeinChannelEigen
import AJConjecture.SkeinChannelIdem
import AJConjecture.SkeinTurnbackIntertwine

/-!
# A nest of caps respects the channels

With `Γ = (f ⊗ f) · caps_k` from two bundles of `a + 1 + k` strands to two bundles of `a + 1`
strands
and `Q'_{n'}` a channel of the smaller bundles: `Q_j Γ Q'_{n'} = Γ Q'_{n'}` for `j = n'` and `0`
otherwise.
Indeed `Y = Γ Q'_{n'}` satisfies `(f ⊗ f) Y = Y` and
`D_1 Y = Γ (β_k + α_k D'_1) Q'_{n'} = (β_k + α_k d'_{1,n'}) Y = d_{1,n'} Y` by
`AJConjecture.turnback_one_mul_twoBundleProj_capThick`,
`AJConjecture.turnback_one_mul_channelIdem` and `AJConjecture.turnbackEigen_one_add`; apply
`AJConjecture.channelIdem_mul_of_turnback_one_mul`.
-/

namespace AJConjecture

/-- The nest of caps sends the channel `n'` of the smaller bundles to the channel `n'` of the
larger ones. -/
theorem channelIdem_mul_capThick_mul_channelIdem (a k j n' : ℕ) (hj : j ≤ a + 1 + k)
    (hn' : n' ≤ a + 1) :
    channelIdem (a + 1 + k) j *
        (twoBundleProj (a + 1 + k) *
          skPlace (2 * (a + 1 + k)) (2 * (a + 1)) (a + 1) (capThick k)) *
        channelIdem (a + 1) n' =
      if j = n' then
        twoBundleProj (a + 1 + k) * skPlace (2 * (a + 1 + k)) (2 * (a + 1)) (a + 1) (capThick k) *
          channelIdem (a + 1) n'
      else 0 := by
  have hE := turnbackEigen_one_add (a + 1) k n' hn'
  have e1 : 2 * ((a + 1 : ℕ) : ℤ) + k + 1 = 2 * (a : ℤ) + k + 3 := by push_cast; ring
  rw [e1, Nat.cast_add a 1, Nat.cast_one] at hE
  rw [Matrix.mul_assoc]
  refine channelIdem_mul_of_turnback_one_mul (a + 1 + k) j n' _ hj (by omega) ?_ ?_
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, twoBundleProj_mul_self]
  · rw [← Matrix.mul_assoc, turnback_one_mul_twoBundleProj_capThick, Matrix.mul_assoc,
      Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, twoBundleProj_mul_channelIdem,
      turnback_one_mul_channelIdem (a + 1) n' hn', smul_smul, ← add_smul, hE, Matrix.mul_smul]

end AJConjecture
