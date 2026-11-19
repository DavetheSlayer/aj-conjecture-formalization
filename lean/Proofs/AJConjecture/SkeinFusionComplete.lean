import Mathlib
import AJConjecture.SkeinChannelNest
import AJConjecture.SkeinChannelTop
import AJConjecture.SkeinFusionBasic
import AJConjecture.SkeinFusionNest

/-!
# Fusion: the channels are the images of the fusion maps

`π ι = d_{m,n} Q_n` for two bundles of `c = n + m` strands, and `Q_c = f_{2c}`: the fusion
decomposition `f ⊗ f = ∑_n d_{c-n,n}⁻¹ π_n ι_n`. Both statements are assembled from lemmas of medium
size; no induction on the size of the bundles is needed.

* `Q_c = f_{2c}`. The top channel kills every generator
(`AJConjecture.channelIdem_self_mul_tlGenF`),
  hence `Q_c f_{2c} = Q_c` (`AJConjecture.mul_jwAt_of_forall_mul_tlGenF_eq_zero`); and
  `Q_c f_{2c} = f_{2c}` is `AJConjecture.channelIdem_mul_fusionProj` for `m = 0`, where
  `π = (f ⊗ f) f_{2c} = f_{2c}` (`AJConjecture.jwAt_mul_jwAt_of_ge`, `AJConjecture.skPlace_one`).
* `π ι = d_{m,n} Q_n` for `n = a + 1`: with `Γ = (f ⊗ f) · caps_m` and `Γ' = cups_m · (f ⊗ f)`,
  `D_m = Γ Γ'` (`AJConjecture.turnback_eq_capThick_mul_cupThick`) and
  `Γ = Γ (f_n ⊗ f_n) = ∑_{n' ≤ n} Γ Q'_{n'}` (`AJConjecture.sum_channelIdem` for the smaller
bundles), so
  `d_{m,n} Q_n = Q_n D_m = ∑_{n'} Q_n Γ Q'_{n'} Γ' = Γ Q'_n Γ'` by
  `AJConjecture.turnback_mul_channelIdem` and
  `AJConjecture.channelIdem_mul_capThick_mul_channelIdem`, and `Q'_n = f_{2n}` by the first
statement:
  `Γ f_{2n} Γ' = π ι` (`AJConjecture.jwAt_mul_self`).
* `π ι = d_{c,0} Q_0` for `n = 0`: `π ι = D_c` (`f_0 = 1`), and `D_c = ∑_n d_{c,n} Q_n` with
`d_{c,n} = 0` for
  `n ≥ 1` (`AJConjecture.turnback_eq_sum`, `AJConjecture.turnbackEigen_eq_zero`).
-/

namespace AJConjecture

/-- The fusion map `π` without caps is the projector `f_{2c}`. -/
private theorem fusionProj_zero_fusionComplete (c : ℕ) :
    twoBundleProj c * skPlace (2 * c) (2 * c) c (capThick 0) * jwAt (2 * c) 0 (2 * c) =
      jwAt (2 * c) 0 (2 * c) := by
  rw [capThick_zero, skPlace_one (2 * c) c 0 (by omega), Matrix.mul_one,
    twoBundleProj, Matrix.mul_assoc,
    jwAt_mul_jwAt_of_ge (2 * c) 0 (2 * c) c c (by omega) (by omega),
    jwAt_mul_jwAt_of_ge (2 * c) 0 (2 * c) 0 c (by omega) (by omega)]

/-- The top channel of two bundles of `c` strands is the projector `f_{2c}`. -/
private theorem channelIdem_self_fusionComplete (c : ℕ) :
    channelIdem c c = jwAt (2 * c) 0 (2 * c) := by
  have h1 : channelIdem c c * jwAt (2 * c) 0 (2 * c) = channelIdem c c :=
    mul_jwAt_of_forall_mul_tlGenF_eq_zero (2 * c) 0 (2 * c) (channelIdem c c)
      fun j _ _ ↦ channelIdem_self_mul_tlGenF c j
  have h2 : channelIdem c c *
      (twoBundleProj c * skPlace (2 * c) (2 * c) c (capThick 0) * jwAt (2 * c) 0 (2 * c)) =
      twoBundleProj c * skPlace (2 * c) (2 * c) c (capThick 0) * jwAt (2 * c) 0 (2 * c) :=
    channelIdem_mul_fusionProj c 0
  rw [fusionProj_zero_fusionComplete, h1] at h2
  exact h2

/-- `Q_n D_k = d_{k,n} Q_n`. -/
private theorem channelIdem_mul_turnback_fusionComplete (c k n : ℕ) (hn : n ≤ c) :
    channelIdem c n * turnback c k = claspAlgTurnbackEigen c k n • channelIdem c n := by
  rw [turnback_eq_sum, Finset.mul_sum, Finset.sum_eq_single n]
  · rw [Matrix.mul_smul, channelIdem_mul_channelIdem c n n hn hn, ite_eq_left rfl]
  · intro b hb hbn
    rw [Finset.mem_range] at hb
    rw [Matrix.mul_smul, channelIdem_mul_channelIdem c n b hn (by omega),
      ite_eq_right (Ne.symm hbn), smul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- The channel `n = a + 1` passes through the nest of caps: `Q_n Γ = Γ Q'_n`. -/
private theorem channelIdem_mul_capThick_fusionComplete (a m : ℕ) :
    channelIdem (a + 1 + m) (a + 1) *
        (twoBundleProj (a + 1 + m) *
          skPlace (2 * (a + 1 + m)) (2 * (a + 1)) (a + 1) (capThick m)) =
      twoBundleProj (a + 1 + m) * skPlace (2 * (a + 1 + m)) (2 * (a + 1)) (a + 1) (capThick m) *
        channelIdem (a + 1) (a + 1) := by
  have h := twoBundleProj_mul_capThick_mul_twoBundleProj (a + 1) m
  rw [← sum_channelIdem (a + 1), Matrix.mul_sum] at h
  conv_lhs => rw [← h]
  rw [Matrix.mul_sum, Finset.sum_eq_single (a + 1)]
  · rw [← Matrix.mul_assoc,
      channelIdem_mul_capThick_mul_channelIdem a m (a + 1) (a + 1) (by omega) le_rfl,
      ite_eq_left rfl]
  · intro b hb hbn
    rw [Finset.mem_range] at hb
    rw [← Matrix.mul_assoc,
      channelIdem_mul_capThick_mul_channelIdem a m (a + 1) b (by omega) (by omega),
      ite_eq_right (Ne.symm hbn)]
  · intro h'
    exact absurd (Finset.mem_range.2 (by omega)) h'

/-- `π ι = d_{m,0} Q_0` for the channel `n = 0`. -/
private theorem fusionProj_mul_fusionIncl_zero_fusionComplete (m : ℕ) :
    fusionProj 0 m * fusionIncl 0 m =
      claspAlgTurnbackEigen (0 + m) m 0 • channelIdem (0 + m) 0 := by
  have h1 : jwAt (2 * 0) 0 (2 * 0) = 1 := rfl
  rw [fusionProj, fusionIncl, h1, Matrix.mul_one, Matrix.one_mul,
    ← turnback_eq_capThick_mul_cupThick 0 m, turnback_eq_sum, Finset.sum_eq_single 0]
  · intro b hb hb0
    rw [Finset.mem_range] at hb
    rw [turnbackEigen_eq_zero (0 + m) m b (by omega) (by omega), zero_smul]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- `π ι = d_{m,n} Q_n`. -/
theorem fusionProj_mul_fusionIncl (n m : ℕ) :
    fusionProj n m * fusionIncl n m =
      claspAlgTurnbackEigen (n + m) m n • channelIdem (n + m) n := by
  rcases n with _ | a
  · exact fusionProj_mul_fusionIncl_zero_fusionComplete m
  · rw [← channelIdem_mul_turnback_fusionComplete (a + 1 + m) m (a + 1) (by omega),
      turnback_eq_capThick_mul_cupThick (a + 1) m, ← Matrix.mul_assoc,
      channelIdem_mul_capThick_fusionComplete a m, channelIdem_self_fusionComplete (a + 1),
      fusionProj, fusionIncl]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (jwAt _ _ _) (jwAt _ _ _), jwAt_mul_self]

end AJConjecture
