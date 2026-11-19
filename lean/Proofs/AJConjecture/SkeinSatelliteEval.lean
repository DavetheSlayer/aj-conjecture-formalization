import Mathlib
import AJConjecture.SkeinHalfTwistSpectral

/-!
# Powers of negative half twists on a channel

Negative half twists act on the channel idempotent `channelIdem c n` of colour `2n` by powers of
`λ_{c,n}⁻¹`, the inverse of the eigenvalue `claspAlgHalfTwistEigen c n` of the positive half twist
(from `AJConjecture.halfTwist_mul_channelIdem`).
-/

namespace AJConjecture

/-- Negative half twists act on the channel of colour `2n` by powers of `λ_{c,n}⁻¹`. -/
theorem halfTwist_false_pow_mul_channelIdem (c n j : ℕ) (hn : n ≤ c) :
    halfTwist c false ^ j * channelIdem c n =
      ((claspAlgHalfTwistEigen c n)⁻¹) ^ j • channelIdem c n := by
  induction j with
  | zero => rw [pow_zero, pow_zero, one_smul, Matrix.one_mul]
  | succ j ih =>
    have h := halfTwist_mul_channelIdem c n false hn
    simp only [Bool.false_eq_true, ite_false] at h
    rw [pow_succ, Matrix.mul_assoc, h, Matrix.mul_smul, ih, smul_smul, pow_succ']

end AJConjecture
