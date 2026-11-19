import Mathlib
import AJConjecture.SkeinFusionComplete
import AJConjecture.SkeinHalfTwistFusion

/-!
# The spectral decomposition of the cabled half twist

`Σ_c^{±1} Q_n = λ_{c,n}^{±1} Q_n` and `Σ_c^{±1} (f ⊗ f) = ∑_n λ_{c,n}^{±1} Q_n`. With `c = n + m`,
`d_{m,n} Q_n = π ι` (`AJConjecture.fusionProj_mul_fusionIncl`), the half twist acts on `π` by
`λ_{c,n}^{±1}` (`AJConjecture.halfTwist_mul_fusionProj`), and `d_{m,n} ≠ 0`
(`AJConjecture.turnbackEigen_ne_zero`). The second statement is the first one summed over the
channels (`AJConjecture.sum_channelIdem`).
-/

namespace AJConjecture

/-- The half twist acts on the channel of colour `2n` by `λ_{c,n}^{±1}`. -/
theorem halfTwist_mul_channelIdem (c n : ℕ) (s : Bool) (hn : n ≤ c) :
    halfTwist c s * channelIdem c n =
      (if s then claspAlgHalfTwistEigen c n else (claspAlgHalfTwistEigen c n)⁻¹) •
        channelIdem c n := by
  obtain ⟨m, rfl⟩ : ∃ m, c = n + m := ⟨c - n, by omega⟩
  have hd : claspAlgTurnbackEigen (n + m) m n ≠ 0 := turnbackEigen_ne_zero (n + m) m n (by omega)
  have h := fusionProj_mul_fusionIncl n m
  refine smul_right_injective _ hd ?_
  change claspAlgTurnbackEigen (n + m) m n • (halfTwist (n + m) s * channelIdem (n + m) n) =
    claspAlgTurnbackEigen (n + m) m n •
      ((if s then claspAlgHalfTwistEigen (n + m) n else (claspAlgHalfTwistEigen (n + m) n)⁻¹) •
        channelIdem (n + m) n)
  rw [← Matrix.mul_smul, ← h, ← Matrix.mul_assoc, halfTwist_mul_fusionProj, Matrix.smul_mul, h,
    smul_comm]

/-- The spectral decomposition of the half twist on two bundles with projectors. -/
theorem halfTwist_mul_twoBundleProj_eq_sum (c : ℕ) (s : Bool) :
    halfTwist c s * twoBundleProj c =
      ∑ n ∈ Finset.range (c + 1),
        (if s then claspAlgHalfTwistEigen c n else (claspAlgHalfTwistEigen c n)⁻¹) •
          channelIdem c n := by
  rw [← sum_channelIdem, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  exact halfTwist_mul_channelIdem c n s (by
    rw [Finset.mem_range] at hn
    omega)

end AJConjecture
