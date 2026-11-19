import Mathlib
import AJHandoff.TorusInput.RJFusionTurnbackEigen
import AJConjecture.SkeinFusionBasic

/-!
# The bubble scalar of a channel (node RA1.5)

`ι_j π_j = d_j f_(a+b-2j)` with `d_j = rjFusionDim a b j ≠ 0` for `j ≤ min a b`: the unequal
version of `fusionIncl_mul_fusionProj` (`AJConjecture.SkeinFusionBasic`).

Route. Induction on `j` (for all `a`, `b`), peeling the innermost cap:
`π^{(a+1,b+1)}_(j+1) = (f_(a+1) ⊗ f_(b+1)) κ_1 π^{(a,b)}_j` and
`ι^{(a+1,b+1)}_(j+1) = ι^{(a,b)}_j κ*_1 (f_(a+1) ⊗ f_(b+1))` (`capThick_succ_inner`,
`skPlace_skPlace`, `rjBundleProj_mul_capThick_mul_bundleProj` and its cup version). Then the bubble
lemma `rj_bubble` and `rj_turnbackOne_mul_fusionProj` give the factor
`χ + ψ ν_j = -[j+1][a+b+2-j]/([a+1][b+1])`, which is the ratio `d^{(a+1,b+1)}_(j+1) / d^{(a,b)}_j`
(reindex the product `rjFusionDim`; `quantumInt_mul_shift_sub`). Non-vanishing: every quantum
integer in the product has a nonzero argument when `j ≤ min a b`
(`claspAlg_quantumInt_ne_zero`). The output sizes `a + b - 2j` differ only propositionally
between the two sides of the peeling identity: state the peeling with free sizes (`skPlace`
takes its sizes as parameters) and rewrite with `omega` facts. Estimate 150–220 lines.
-/

noncomputable section

namespace AJConjecture

/-- A placed nest of `c + 1` caps: the innermost cap, then the placed nest of `c` caps (free
sizes). -/
private theorem rj_skPlace_capThick_succ_inner_inclProj (c M m n' i j : ℕ) (h : i + 2 * c ≤ m)
    (h' : m = n' + 2 * c) (hM : M = m + 2) (hj : j = i + c) :
    skPlace M n' i (capThick (c + 1)) = skPlace M m j skCap * skPlace m n' i (capThick c) := by
  subst hj hM
  rw [capThick_succ_inner,
    skPlace_mul (m + 2) m n' i _ (capThick c) (by omega) (by omega) (by omega),
    skPlace_skPlace (m + 2) m i c skCap (by omega) (by omega) (by omega) (by omega)]

/-- A placed nest of `c + 1` cups: the placed nest of `c` cups, then the innermost cup (free
sizes). -/
private theorem rj_skPlace_cupThick_succ_inner_inclProj (c M m n' i j : ℕ) (h : i ≤ n')
    (h' : m = n' + 2 * c) (hM : M = m + 2) (hj : j = i + c) :
    skPlace n' M i (cupThick (c + 1)) = skPlace n' m i (cupThick c) * skPlace m M j skCup := by
  subst hj hM
  rw [cupThick_succ_inner,
    skPlace_mul n' m (m + 2) i (cupThick c) _ (by omega) (by omega) (by omega),
    skPlace_skPlace m (m + 2) i c skCup (by omega) (by omega) (by omega) (by omega)]

/-- `f_a ⊗ f_b` is absorbed by `D_1` on both sides. -/
private theorem rj_turnbackOne_absorb_inclProj (a b : ℕ) :
    rjBundleProj a b * rjTurnbackOne a b = rjTurnbackOne a b ∧
      rjTurnbackOne a b * rjBundleProj a b = rjTurnbackOne a b := by
  refine ⟨?_, ?_⟩
  · rw [rjTurnbackOne, ← Matrix.mul_assoc, ← Matrix.mul_assoc, rjBundleProj_mul_self]
  · rw [rjTurnbackOne, Matrix.mul_assoc, rjBundleProj_mul_self]

/-- The projector on all strands absorbs `f_p ⊗ f_q` on both sides. -/
private theorem rj_jwAt_full_absorb_inclProj (p q : ℕ) :
    rjBundleProj p q * jwAt (p + q) 0 (p + q) = jwAt (p + q) 0 (p + q) ∧
      jwAt (p + q) 0 (p + q) * rjBundleProj p q = jwAt (p + q) 0 (p + q) := by
  refine ⟨?_, ?_⟩
  · rw [rjBundleProj, Matrix.mul_assoc,
      jwAt_mul_jwAt_of_ge _ 0 (p + q) p q (by omega) (by omega),
      jwAt_mul_jwAt_of_ge _ 0 (p + q) 0 p le_rfl (by omega)]
  · rw [rjBundleProj, ← Matrix.mul_assoc,
      jwAt_mul_jwAt_of_le _ 0 (p + q) 0 p le_rfl (by omega),
      jwAt_mul_jwAt_of_le _ 0 (p + q) p q (by omega) (by omega)]

/-- One step of the bubble recursion for `ι π`, for abstract rectangular matrices. -/
private theorem rj_bubble_step_inclProj {p q r : ℕ} (f : SkMat p p) (C : SkMat p q)
    (U : SkMat q r) (P' : SkMat r r) (V : SkMat r q) (K : SkMat q p) (P T : SkMat q q)
    (x y d1 dm : RatFunc ℚ) (hP' : P' * P' = P') (hbub : U * P' * V = x • P + y • T)
    (hP : P * P = P) (hPT : P * T = T) (hTP : T * P = T)
    (ih : f * C * P * (P * K * f) = dm • f) (hD : T * (P * K * f) = d1 • (P * K * f)) :
    f * (C * U) * P' * (P' * (V * K) * f) = ((x + y * d1) * dm) • f := by
  have h1 : f * (C * U) * P' * (P' * (V * K) * f) = f * C * (U * (P' * P') * V) * (K * f) := by
    simp only [Matrix.mul_assoc]
  have h2 : f * C * P * (K * f) = dm • f := by
    rw [← ih]
    conv_lhs => rw [← hP]
    simp only [Matrix.mul_assoc]
  have h3 : f * C * T * (K * f) = (d1 * dm) • f := by
    calc f * C * T * (K * f) = f * C * (P * (T * P)) * (K * f) := by rw [hTP, hPT]
      _ = f * C * P * (T * (P * K * f)) := by simp only [Matrix.mul_assoc]
      _ = (d1 * dm) • f := by rw [hD, Matrix.mul_smul, ih, smul_smul]
  rw [h1, hP', hbub, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul, h2, h3, smul_smul, smul_smul, ← add_smul]
  congr 1
  ring

/-- The factor of one step: `χ + ψ ν_j = -[j+1][A+B+2-j]/([A+1][B+1])`. -/
private theorem rj_bubble_factor_inclProj (A B R : ℤ)
    (hR : quantumInt R = 0 ∨ (quantumInt A ≠ 0 ∧ quantumInt B ≠ 0))
    (hA1 : quantumInt (A + 1) ≠ 0) (hB1 : quantumInt (B + 1) ≠ 0) :
    -quantumInt (A + B + 2) / (quantumInt (A + 1) * quantumInt (B + 1)) +
        quantumInt A * quantumInt B / (quantumInt (A + 1) * quantumInt (B + 1)) *
          (-(quantumInt R * quantumInt (A + B + 1 - R)) / (quantumInt A * quantumInt B)) =
      -(quantumInt (R + 1) * quantumInt (A + B + 2 - R)) /
        (quantumInt (A + 1) * quantumInt (B + 1)) := by
  have key := quantumInt_mul_shift_sub R (A + B + 1 - R) 1
  rw [quantumInt_one, one_mul, show R + (A + B + 1 - R) + 1 = A + B + 2 from by ring,
    show A + B + 1 - R + 1 = A + B + 2 - R from by ring] at key
  rcases hR with h0 | ⟨ha, hb⟩
  · rw [h0, zero_mul, sub_zero] at key
    rw [h0, zero_mul, neg_zero, zero_div, mul_zero, add_zero, key]
  · field_simp
    linear_combination key

/-- The bubble scalar of the channel `j + 1` of the larger bundles from that of the channel `j`. -/
private theorem rj_fusionDim_succ_inclProj (p q j : ℕ) :
    rjFusionDim (p + (j + 1)) (q + (j + 1)) (j + 1) =
      (rjBubbleChi (p + j) (q + j) +
        rjBubblePsi (p + j) (q + j) * rjTurnbackEigen (p + j) (q + j) j) *
          rjFusionDim (p + j) (q + j) j := by
  have hstep : rjFusionDim (p + (j + 1)) (q + (j + 1)) (j + 1) =
      rjFusionDim (p + j) (q + j) j *
        (-(quantumInt ((j : ℤ) + 1) * quantumInt ((p : ℤ) + q + j + 2)) /
          (quantumInt ((p : ℤ) + j + 1) * quantumInt ((q : ℤ) + j + 1))) := by
    unfold rjFusionDim
    rw [Finset.prod_range_succ]
    congr 1
    · refine Finset.prod_congr rfl fun i _ ↦ ?_
      push_cast
      ring_nf
    · push_cast
      ring_nf
  have hfac : rjBubbleChi (p + j) (q + j) +
      rjBubblePsi (p + j) (q + j) * rjTurnbackEigen (p + j) (q + j) j =
        -(quantumInt ((j : ℤ) + 1) * quantumInt ((p : ℤ) + q + j + 2)) /
          (quantumInt ((p : ℤ) + j + 1) * quantumInt ((q : ℤ) + j + 1)) := by
    rw [rjBubbleChi, rjBubblePsi, rjTurnbackEigen]
    rw [rj_bubble_factor_inclProj _ _ _ ?_ (claspAlg_quantumInt_ne_zero (by omega))
      (claspAlg_quantumInt_ne_zero (by omega))]
    · push_cast
      ring_nf
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact Or.inl (by rw [Nat.cast_zero, quantumInt_zero])
      · exact Or.inr ⟨claspAlg_quantumInt_ne_zero (by omega),
          claspAlg_quantumInt_ne_zero (by omega)⟩
  rw [hstep, hfac, mul_comm]

/-- `D_1 π = ν_j π` with the output sizes written as `p + q` and `p`. -/
private theorem rj_turnbackOne_mul_fusionProj_clean (p q j : ℕ) :
    rjTurnbackOne (p + j) (q + j) *
        (rjBundleProj (p + j) (q + j) * skPlace (p + j + (q + j)) (p + q) p (capThick j) *
          jwAt (p + q) 0 (p + q)) =
      rjTurnbackEigen (p + j) (q + j) j •
        (rjBundleProj (p + j) (q + j) * skPlace (p + j + (q + j)) (p + q) p (capThick j) *
          jwAt (p + q) 0 (p + q)) := by
  have h := rj_turnbackOne_mul_fusionProj (p + j) (q + j) j (by omega)
  rw [rjFusionProj, show p + j + (q + j) - 2 * j = p + q from by omega,
    show p + j - j = p from by omega] at h
  exact h

/-- `ι π = d_j f` with the output sizes written as `p + q` and `p`. -/
private theorem rj_fusionIncl_mul_fusionProj_clean (p q j : ℕ) :
    jwAt (p + q) 0 (p + q) * skPlace (p + q) (p + j + (q + j)) p (cupThick j) *
        rjBundleProj (p + j) (q + j) *
      (rjBundleProj (p + j) (q + j) * skPlace (p + j + (q + j)) (p + q) p (capThick j) *
        jwAt (p + q) 0 (p + q)) =
      rjFusionDim (p + j) (q + j) j • jwAt (p + q) 0 (p + q) := by
  induction j with
  | zero =>
    rw [show p + 0 = p from rfl, show q + 0 = q from rfl, cupThick_zero, capThick_zero,
      skPlace_one (p + q) p 0 (by omega), Matrix.mul_one, Matrix.mul_one,
      (rj_jwAt_full_absorb_inclProj p q).2, (rj_jwAt_full_absorb_inclProj p q).1, jwAt_mul_self,
      rjFusionDim, Finset.prod_range_zero, one_smul]
  | succ j ih =>
    have hcap := rj_skPlace_capThick_succ_inner_inclProj j (p + (j + 1) + (q + (j + 1)))
      (p + j + (q + j)) (p + q) p (p + j) (by omega) (by omega) (by omega) (by omega)
    have hcup := rj_skPlace_cupThick_succ_inner_inclProj j (p + (j + 1) + (q + (j + 1)))
      (p + j + (q + j)) (p + q) p (p + j) (by omega) (by omega) (by omega) (by omega)
    rw [hcap, hcup, rj_fusionDim_succ_inclProj]
    exact rj_bubble_step_inclProj _ _ _ _ _ _ _ _ _ _ _ _ (rjBundleProj_mul_self _ _)
      (rj_bubble (p + j) (q + j)) (rjBundleProj_mul_self _ _)
      (rj_turnbackOne_absorb_inclProj _ _).1 (rj_turnbackOne_absorb_inclProj _ _).2 ih
      (rj_turnbackOne_mul_fusionProj_clean p q j)

/-- The inclusion followed by the projection of a channel is the bubble scalar times the
projector. -/
theorem rj_fusionIncl_mul_fusionProj (a b j : ℕ) (hj : j ≤ min a b) :
    rjFusionIncl a b j * rjFusionProj a b j =
      rjFusionDim a b j • jwAt (a + b - 2 * j) 0 (a + b - 2 * j) := by
  obtain ⟨p, rfl⟩ : ∃ p, a = p + j := ⟨a - j, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, b = q + j := ⟨b - j, by omega⟩
  rw [rjFusionIncl, rjFusionProj, show p + j + (q + j) - 2 * j = p + q from by omega,
    show p + j - j = p from by omega]
  exact rj_fusionIncl_mul_fusionProj_clean p q j

/-- The bubble scalar of a channel is not zero. -/
theorem rj_fusionDim_ne_zero (a b j : ℕ) (hj : j ≤ min a b) : rjFusionDim a b j ≠ 0 := by
  rw [rjFusionDim, Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_range] at hi
  have hj' : j ≤ a ∧ j ≤ b := ⟨le_trans hj (min_le_left a b), le_trans hj (min_le_right a b)⟩
  refine div_ne_zero (neg_ne_zero.mpr (mul_ne_zero ?_ ?_)) (mul_ne_zero ?_ ?_) <;>
    exact claspAlg_quantumInt_ne_zero (by omega)

end AJConjecture
