import Mathlib
import AJConjecture.SkeinChannelTurnback
import AJConjecture.SkeinThickCupAdd
import AJConjecture.SkeinTurnbackIntertwine

/-!
# The top channel kills the generators

`Q_c e_j = 0` for every generator of `V^{⊗ 2c}`. For `j ≠ c - 1` this is `Q_c = Q_c (f ⊗ f)` and
`AJConjecture.jwAt_mul_tlGenF`. For `j = c - 1 = a`, with `e_a = capAt * cupAt`, it suffices that
`V = Q_c · capAt` vanishes. Now `d_{1,c} = 0`, so `Q_c D_1 = 0`, that is `V · cupAt · (f ⊗ f) = 0`;
multiplying by the cap and the projectors `g = f_a ⊗ f_a` and using the bubble lemma
(`AJConjecture.skCup_mul_twoBundleProj_mul_skCap`) gives `V (x g + y D'_1) = 0`, where `D'_1` is the
turnback element of two bundles of `a` strands, and `V g = V`
(`AJConjecture.twoBundleProj_mul_capThick_mul_twoBundleProj` with one cap,
`AJConjecture.capThick_one`). On the channel `n ≤ a` of the smaller bundles `x g + y D'_1` is the
scalar `x + y d'_{1,n} = d_{1,n}` of the bundles of `a + 1` strands
(`AJConjecture.turnbackEigen_one_add` with `k = 1`), which is not zero
(`AJConjecture.turnbackEigen_ne_zero`). Hence `x g + y D'_1` has the inverse `∑_n d_{1,n}⁻¹ Q'_n`
on the
image of `g` (first statement, from `AJConjecture.turnback_eq_sum`,
`AJConjecture.channelIdem_mul_channelIdem` and `AJConjecture.sum_channelIdem`), and `V = 0`.
-/

namespace AJConjecture

/-- The shifted turnback element `x g + y D'_1` of the bubble lemma is invertible on the image of
`g = f_a ⊗ f_a`. -/
theorem turnback_shift_mul_inverse (a : ℕ) :
    ((-(quantumInt (2 * (a : ℤ) + 2)) / quantumInt ((a : ℤ) + 1) ^ 2) • twoBundleProj a +
          (quantumInt (a : ℤ) ^ 2 / quantumInt ((a : ℤ) + 1) ^ 2) • turnback a 1) *
        ∑ n ∈ Finset.range (a + 1), (claspAlgTurnbackEigen (a + 1) 1 n)⁻¹ • channelIdem a n =
      twoBundleProj a := by
  have hq1 : quantumInt 1 = 1 := by
    rw [quantumInt, mul_one]
    exact div_self claspAlg_ratFuncX_sq_sub_ne_zero
  rw [Finset.mul_sum]
  refine (Finset.sum_congr rfl fun n hn ↦ ?_).trans (sum_channelIdem a)
  have hn' : n ≤ a := by
    rw [Finset.mem_range] at hn
    omega
  have hE := turnbackEigen_one_add a 1 n hn'
  have e1 : 2 * (a : ℤ) + 1 + 1 = 2 * (a : ℤ) + 2 := by ring
  rw [Nat.cast_one, hq1, one_mul, e1] at hE
  rw [Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    twoBundleProj_mul_channelIdem, turnback_one_mul_channelIdem a n hn', smul_smul, ← add_smul,
    smul_smul, hE, inv_mul_cancel₀ (turnbackEigen_ne_zero (a + 1) 1 n (by omega)), one_smul]

/-- The algebra behind the vanishing of the top channel on the middle cap: if `Q F = Q`,
`Q F (cap cup) F = 0`, `cup F cap = T` is invertible on the image of `g` and `F cap g = F cap`,
then `Q cap = 0`. -/
private theorem mul_eq_zero_of_bubble_channelTop {p r : ℕ} (Q F : SkMat p p) (cap : SkMat p r)
    (cup : SkMat r p) (g T S : SkMat r r) (hQF : Q * F = Q) (hQD : Q * (F * (cap * cup) * F) = 0)
    (hB : cup * F * cap = T) (hTS : T * S = g) (hG : F * cap * g = F * cap) : Q * cap = 0 := by
  have h1 : Q * cap = Q * (F * cap * g) := by
    rw [hG, ← Matrix.mul_assoc, hQF]
  have h2 : Q * (F * cap * g) = Q * (F * (cap * cup) * F) * cap * S := by
    rw [← hTS, ← hB]
    simp only [Matrix.mul_assoc]
  rw [h1, h2, hQD, Matrix.zero_mul, Matrix.zero_mul]

/-- The top channel kills the cap on the two middle strands. -/
theorem channelIdem_self_mul_skCap (a : ℕ) :
    channelIdem (a + 1) (a + 1) * skPlace (2 * (a + 1)) (2 * a) a skCap = 0 := by
  have hQD : channelIdem (a + 1) (a + 1) * turnback (a + 1) 1 = 0 := by
    rw [turnback_eq_sum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun n hn ↦ ?_
    rw [Finset.mem_range] at hn
    rw [Matrix.mul_smul, channelIdem_mul_channelIdem (a + 1) (a + 1) n le_rfl (by omega)]
    split_ifs with h
    · rw [← h, turnbackEigen_eq_zero (a + 1) 1 (a + 1) le_rfl (by omega), zero_smul]
    · rw [smul_zero]
  have hE : tlGenF (2 * (a + 1)) (a + 1 - 1) =
      skPlace (2 * (a + 1)) (2 * a) a skCap * skPlace (2 * a) (2 * (a + 1)) a skCup :=
    (capAt_mul_cupAt (2 * a) a (by omega)).symm
  have hB := skCup_mul_twoBundleProj_mul_skCap a
  rw [← turnback_one a] at hB
  have hG : twoBundleProj (a + 1) * skPlace (2 * (a + 1)) (2 * a) a skCap * twoBundleProj a =
      twoBundleProj (a + 1) * skPlace (2 * (a + 1)) (2 * a) a skCap := by
    have h := twoBundleProj_mul_capThick_mul_twoBundleProj a 1
    rwa [capThick_one] at h
  rw [turnback_one, hE] at hQD
  exact mul_eq_zero_of_bubble_channelTop _ _ _ _ _ _ _ (channelIdem_mul_twoBundleProj _ _) hQD hB
    (turnback_shift_mul_inverse a) hG

/-- The top channel kills every generator. -/
theorem channelIdem_self_mul_tlGenF (c j : ℕ) : channelIdem c c * tlGenF (2 * c) j = 0 := by
  rcases c with _ | a
  · rw [tlGenF_eq_zero _ _ (by omega), Matrix.mul_zero]
  · rcases lt_trichotomy j a with h | rfl | h
    · rw [← channelIdem_mul_twoBundleProj, twoBundleProj, Matrix.mul_assoc, Matrix.mul_assoc,
        (jwAt_commute_tlGenF (2 * (a + 1)) (a + 1) (a + 1) j (Or.inl (by omega))).eq,
        ← Matrix.mul_assoc (jwAt _ 0 _), jwAt_mul_tlGenF _ _ _ _ (by omega) (by omega),
        Matrix.zero_mul, Matrix.mul_zero]
    · have hE : tlGenF (2 * (j + 1)) j =
          skPlace (2 * (j + 1)) (2 * j) j skCap * cupAt (2 * j) j :=
        (capAt_mul_cupAt (2 * j) j (by omega)).symm
      rw [hE, ← Matrix.mul_assoc, channelIdem_self_mul_skCap, Matrix.zero_mul]
    · by_cases h2 : j + 1 < 2 * (a + 1)
      · rw [← channelIdem_mul_twoBundleProj, twoBundleProj, Matrix.mul_assoc, Matrix.mul_assoc,
          jwAt_mul_tlGenF _ _ _ _ (by omega) (by omega), Matrix.mul_zero, Matrix.mul_zero]
      · rw [tlGenF_eq_zero _ _ (by omega), Matrix.mul_zero]

end AJConjecture
