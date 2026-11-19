import Mathlib
import AJConjecture.SkeinChannelIdem

/-!
# The turnback elements on the channels

`D_k Q_n = d_{k,n} Q_n` and `D_k = ∑_n d_{k,n} Q_n`. Induction on `k`: `D_0 = f ⊗ f`, and
`α_k D_{k+1} Q_n = (D_1 - β_k) D_k Q_n = d_{k,n} (d_{1,n} - β_k) Q_n = α_k d_{k+1,n} Q_n` by
`AJConjecture.turnback_one_mul`, `AJConjecture.turnback_one_mul_channelIdem` and
`AJConjecture.turnbackEigen_succ_mul`, with `α_k ≠ 0` for `k < c`; for `k > c` both sides vanish
(`AJConjecture.turnback_eq_zero`, `AJConjecture.turnbackEigen_eq_zero`). The second statement is
the first one summed over the channels (`AJConjecture.sum_channelIdem`).
-/

namespace AJConjecture

/-- `D_k Q_n = d_{k,n} Q_n`. -/
theorem turnback_mul_channelIdem (c k n : ℕ) (hn : n ≤ c) :
    turnback c k * channelIdem c n = claspAlgTurnbackEigen c k n • channelIdem c n := by
  induction k with
  | zero => rw [turnback_zero, twoBundleProj_mul_channelIdem, turnbackEigen_zero, one_smul]
  | succ k ih =>
    by_cases hk : k < c
    · have hα : quantumInt ((c : ℤ) - k) ^ 2 / quantumInt (c : ℤ) ^ 2 ≠ 0 :=
        div_ne_zero (pow_ne_zero 2 (claspAlg_quantumInt_ne_zero (by omega)))
          (pow_ne_zero 2 (claspAlg_quantumInt_ne_zero (by omega)))
      have h1 := congrArg (· * channelIdem c n) (turnback_one_mul c k)
      simp only [Matrix.mul_assoc, ih, Matrix.mul_smul, turnback_one_mul_channelIdem c n hn,
        Matrix.add_mul, Matrix.smul_mul, smul_smul] at h1
      have h2 := turnbackEigen_succ_mul c k n hk
      refine smul_right_injective _ hα ?_
      dsimp only
      rw [smul_smul, mul_comm _ (claspAlgTurnbackEigen c (k + 1) n), h2, ← sub_eq_zero]
      rw [← sub_eq_zero] at h1
      rw [← neg_eq_zero, ← h1, mul_sub, sub_smul, mul_comm (claspAlgTurnbackEigen c k n)
        (-(quantumInt (k : ℤ) * quantumInt (2 * (c : ℤ) + 1 - k)) / quantumInt (c : ℤ) ^ 2)]
      abel
    · rw [turnback_eq_zero c (k + 1) (by omega), turnbackEigen_eq_zero c (k + 1) n hn (by omega),
        Matrix.zero_mul, zero_smul]

/-- The spectral decomposition of the turnback elements. -/
theorem turnback_eq_sum (c k : ℕ) :
    turnback c k = ∑ n ∈ Finset.range (c + 1), claspAlgTurnbackEigen c k n • channelIdem c n := by
  rw [← turnback_mul_twoBundleProj c k, ← sum_channelIdem c, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  exact turnback_mul_channelIdem c k n (by have := Finset.mem_range.mp hn; omega)

end AJConjecture
