import Mathlib
import AJConjecture.SkeinFusionComplete
import AJConjecture.SkeinJwTrace

/-!
# The quantum trace of a channel

`qtr Q_n = [2n+1]`: with `c = n + m`, `d_{m,n} qtr(Q_n) = qtr(π ι) = qtr(ι π) = d_{m,n}
qtr(f_{2n})` by
`AJConjecture.fusionProj_mul_fusionIncl`, the cyclicity of the trace
(`AJConjecture.qtr_mul_comm_of_weight` with `AJConjecture.skWeight_mul_fusionProj`) and
`AJConjecture.fusionIncl_mul_fusionProj`; `d_{m,n} ≠ 0` (`AJConjecture.turnbackEigen_ne_zero`) and
`qtr f_{2n} = Δ_{2n} = [2n+1]` (`AJConjecture.qtr_jwAt`).
-/

namespace AJConjecture

/-- The quantum trace of the channel of colour `2n` is `[2n+1]`. -/
theorem qtr_channelIdem (c n : ℕ) (hn : n ≤ c) :
    qtr (2 * c) (channelIdem c n) = quantumInt (2 * (n : ℤ) + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, c = n + m := ⟨c - n, by omega⟩
  have hd : claspAlgTurnbackEigen (n + m) m n ≠ 0 := turnbackEigen_ne_zero (n + m) m n (by omega)
  have h1 := qtr_mul_comm_of_weight (2 * (n + m)) (2 * n) (fusionProj n m) (fusionIncl n m)
    (skWeight_mul_fusionProj n m)
  rw [fusionProj_mul_fusionIncl, fusionIncl_mul_fusionProj, qtr_smul,
    qtr_smul, qtr_jwAt, loopScalar, pow_mul, neg_one_sq, one_pow, one_mul] at h1
  rw [mul_left_cancel₀ hd h1]
  push_cast
  rfl

end AJConjecture
