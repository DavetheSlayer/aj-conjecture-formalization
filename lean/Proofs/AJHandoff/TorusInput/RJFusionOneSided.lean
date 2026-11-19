import Mathlib
import AJHandoff.TorusInput.RJFusionBubble
import AJConjecture.SkeinTurnbackOneSided
import AJConjecture.SkeinThickCupInner

/-!
# The first turnback against a nest of caps, unequal bundles (node RA1.3)

The unequal version of `turnback_one_mul_capThick_place` and `turnback_one_mul_capThick`
(`AJConjecture.SkeinTurnbackOneSided`). With `a = p + 1 + r`, `b = q + 1 + r`:
`D_1 κ_r = ν_r (f_a ⊗ f_b) κ_r + α_r (f_a ⊗ f_b) κ_(r+1) κ*_1 (f_(p+1) ⊗ f_(q+1))`,
`ν_r = -[r][a+b+1-r]/([a][b])`, `α_r = [p+1][q+1]/([a][b])`, `κ_r` the nest of `r` caps in the
middle; and when one bundle is used up by the nest (`a = r` or `b = r`) only the first term
remains.

Route. Induction on `r` as in `SkeinTurnbackOneSided`: `κ_(r+1) = κ_1 κ_r` (innermost cap first,
`capThick_succ_inner`, `skPlace_skPlace`), the one-cap identity
`D_1^{(a+1,b+1)} κ_1 = χ F κ_1 + ψ F κ_1 D_1^{(a,b)}` from the bubble lemma (`rj_bubble`) and the
absorption `rjBundleProj_mul_capThick_mul_bundleProj`; the scalars close by
`χ + ψ ν_r = -[r+1][a+b+2-r]/([a+1][b+1])` and `ψ α_r = α_(r+1)` (`quantumInt_mul_shift_sub`).
Numerically checked (design notes). Estimate 220–300 lines.
-/

noncomputable section

namespace AJConjecture

/-- `D_1` vanishes when one of the bundles is empty. -/
private theorem rj_turnbackOne_eq_zero_of_empty (a b : ℕ) (h : a = 0 ∨ b = 0) :
    rjTurnbackOne a b = 0 := by
  rcases h with rfl | rfl
  · by_cases hb : 2 ≤ b
    · have hk : jwAt (0 + b) 0 b * tlGenF (0 + b) (0 - 1) = 0 :=
        jwAt_mul_tlGenF _ 0 b _ (by omega) (by omega)
      rw [rjTurnbackOne, rjBundleProj, Matrix.mul_assoc (jwAt _ 0 0), hk, Matrix.mul_zero,
        Matrix.zero_mul]
    · rw [rjTurnbackOne, tlGenF_eq_zero _ _ (by omega), Matrix.mul_zero, Matrix.zero_mul]
  · rw [rjTurnbackOne, tlGenF_eq_zero _ _ (by omega), Matrix.mul_zero, Matrix.zero_mul]

/-- The generator `e_i` as a cap followed by a cup (free sizes). -/
private theorem rj_tlGenF_eq_cap_mul_cup (N n i : ℕ) (hN : N = n + 2) (hi : i ≤ n) :
    tlGenF N i = skPlace N n i skCap * skPlace n N i skCup := by
  subst hN
  exact (capAt_mul_cupAt n i hi).symm

/-- A placed nest of `c + 1` caps: the innermost cap, then the placed nest of `c` caps (free
sizes). -/
private theorem rj_skPlace_capThick_succ_inner (c M m n' i j : ℕ) (h : i + 2 * c ≤ m)
    (h' : m = n' + 2 * c) (hM : M = m + 2) (hj : j = i + c) :
    skPlace M n' i (capThick (c + 1)) = skPlace M m j skCap * skPlace m n' i (capThick c) := by
  subst hj hM
  rw [capThick_succ_inner,
    skPlace_mul (m + 2) m n' i _ (capThick c) (by omega) (by omega) (by omega),
    skPlace_skPlace (m + 2) m i c skCap (by omega) (by omega) (by omega) (by omega)]

/-- One cap below `f_(a+1) ⊗ f_(b+1)` absorbs `f_a ⊗ f_b`. -/
private theorem rj_bundleProj_mul_skCap_mul_bundleProj (a b : ℕ) :
    rjBundleProj (a + 1) (b + 1) * skPlace (a + 1 + (b + 1)) (a + b) a skCap *
        rjBundleProj a b =
      rjBundleProj (a + 1) (b + 1) * skPlace (a + 1 + (b + 1)) (a + b) a skCap := by
  have h := rjBundleProj_mul_capThick_mul_bundleProj a b 1
  rw [capThick_one] at h
  exact h

/-- `D_1` against one cap: the unequal bubble lemma. -/
private theorem rj_turnbackOne_succ_mul_skCap (a b : ℕ) :
    rjTurnbackOne (a + 1) (b + 1) * skPlace (a + 1 + (b + 1)) (a + b) a skCap =
      rjBubbleChi a b •
          (rjBundleProj (a + 1) (b + 1) * skPlace (a + 1 + (b + 1)) (a + b) a skCap) +
        rjBubblePsi a b •
          (rjBundleProj (a + 1) (b + 1) * skPlace (a + 1 + (b + 1)) (a + b) a skCap *
            rjTurnbackOne a b) := by
  have hE : tlGenF (a + 1 + (b + 1)) (a + 1 - 1) =
      skPlace (a + 1 + (b + 1)) (a + b) a skCap * skPlace (a + b) (a + 1 + (b + 1)) a skCup := by
    rw [Nat.add_sub_cancel]
    exact rj_tlGenF_eq_cap_mul_cup _ _ _ (by omega) (by omega)
  have habs := rj_bundleProj_mul_skCap_mul_bundleProj a b
  have hbub := rj_bubble a b
  rw [rjTurnbackOne.eq_1 (a + 1) (b + 1), hE]
  calc rjBundleProj (a + 1) (b + 1) *
          (skPlace (a + 1 + (b + 1)) (a + b) a skCap *
            skPlace (a + b) (a + 1 + (b + 1)) a skCup) *
          rjBundleProj (a + 1) (b + 1) * skPlace (a + 1 + (b + 1)) (a + b) a skCap =
        rjBundleProj (a + 1) (b + 1) * skPlace (a + 1 + (b + 1)) (a + b) a skCap *
          (skPlace (a + b) (a + 1 + (b + 1)) a skCup * rjBundleProj (a + 1) (b + 1) *
            skPlace (a + 1 + (b + 1)) (a + b) a skCap) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hbub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, habs]

/-- The algebra of the induction step: `D cap = x F cap + y F cap D'`, the induction hypothesis
for `D'`, and the absorption `F cap F' = F cap`. -/
private theorem rj_oneSided_step_alg {K N M L L' : Type*} [CommRing K] [Fintype N] [Fintype M]
    [Fintype L] [Fintype L'] [DecidableEq N] [DecidableEq M] [DecidableEq L]
    (D F : Matrix N N K) (cap : Matrix N M K) (D' F' : Matrix M M K) (P : Matrix M L K)
    (R1 : Matrix M L' K) (R2 : Matrix L' L K) (R3 : Matrix L L K) (x y β α : K)
    (hS : D * cap = x • (F * cap) + y • (F * cap * D'))
    (hIH : D' * P = β • (F' * P) + α • (F' * R1 * R2 * R3))
    (habs : F * cap * F' = F * cap) :
    D * (cap * P) = (x + y * β) • (F * (cap * P)) + (y * α) • (F * (cap * R1) * R2 * R3) := by
  have e1 : F * cap * (F' * P) = F * (cap * P) := by
    rw [← Matrix.mul_assoc, habs, Matrix.mul_assoc]
  have e2 : F * cap * (F' * R1 * R2 * R3) = F * (cap * R1) * R2 * R3 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, habs,
      Matrix.mul_assoc F cap R1]
  rw [← Matrix.mul_assoc, hS, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_assoc (F * cap) D' P, hIH, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, e1, e2,
    Matrix.mul_assoc F cap P]
  module

/-- The algebra of the induction step for the full nest. -/
private theorem rj_oneSided_full_step_alg {K N M L : Type*} [CommRing K] [Fintype N]
    [Fintype M] [Fintype L] [DecidableEq N] [DecidableEq M] [DecidableEq L]
    (D F : Matrix N N K) (cap : Matrix N M K) (D' F' : Matrix M M K) (P : Matrix M L K)
    (x y β : K) (hS : D * cap = x • (F * cap) + y • (F * cap * D'))
    (hIH : D' * P = β • (F' * P)) (habs : F * cap * F' = F * cap) :
    D * (cap * P) = (x + y * β) • (F * (cap * P)) := by
  have e1 : F * cap * (F' * P) = F * (cap * P) := by
    rw [← Matrix.mul_assoc, habs, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, hS, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_assoc (F * cap) D' P, hIH, Matrix.mul_smul, e1, Matrix.mul_assoc F cap P]
  module

/-- The scalar of the induction step: `χ + ψ ν_R = ν'_(R+1)`, from
`[R+1][a+b+2-R] - [R][a+b+1-R] = [a+b+2]`. -/
private theorem rj_nu_step_scalar (a b R : ℤ)
    (hR : quantumInt R = 0 ∨ (quantumInt a ≠ 0 ∧ quantumInt b ≠ 0))
    (ha1 : quantumInt (a + 1) ≠ 0) (hb1 : quantumInt (b + 1) ≠ 0) :
    -quantumInt (a + b + 2) / (quantumInt (a + 1) * quantumInt (b + 1)) +
        quantumInt a * quantumInt b / (quantumInt (a + 1) * quantumInt (b + 1)) *
          (-(quantumInt R * quantumInt (a + b + 1 - R)) / (quantumInt a * quantumInt b)) =
      -(quantumInt (R + 1) * quantumInt (a + 1 + (b + 1) + 1 - (R + 1))) /
        (quantumInt (a + 1) * quantumInt (b + 1)) := by
  have key := quantumInt_mul_shift_sub R (a + b + 1 - R) 1
  rw [quantumInt_one, one_mul, show R + (a + b + 1 - R) + 1 = a + b + 2 from by ring,
    show a + b + 1 - R + 1 = a + 1 + (b + 1) + 1 - (R + 1) from by ring] at key
  rcases hR with h0 | ⟨ha, hb⟩
  · rw [h0, zero_mul, sub_zero] at key
    rw [h0, zero_mul, neg_zero, zero_div, mul_zero, add_zero, key]
  · field_simp
    linear_combination key

/-- The one-sided recursion: the first turnback against `r` nested caps. -/
theorem rj_turnbackOne_mul_capNest (p q r : ℕ) :
    rjTurnbackOne (p + 1 + r) (q + 1 + r) *
        skPlace (p + 1 + r + (q + 1 + r)) (p + 1 + (q + 1)) (p + 1) (capThick r) =
      rjTurnbackEigen (p + 1 + r) (q + 1 + r) r •
          (rjBundleProj (p + 1 + r) (q + 1 + r) *
            skPlace (p + 1 + r + (q + 1 + r)) (p + 1 + (q + 1)) (p + 1) (capThick r)) +
        (quantumInt ((p : ℤ) + 1) * quantumInt ((q : ℤ) + 1) /
            (quantumInt ((p : ℤ) + 1 + r) * quantumInt ((q : ℤ) + 1 + r))) •
          (rjBundleProj (p + 1 + r) (q + 1 + r) *
              skPlace (p + 1 + r + (q + 1 + r)) (p + q) p (capThick (r + 1)) *
            skPlace (p + q) (p + 1 + (q + 1)) p skCup * rjBundleProj (p + 1) (q + 1)) := by
  induction r with
  | zero =>
    have hne : quantumInt ((p : ℤ) + 1) * quantumInt ((q : ℤ) + 1) ≠ 0 :=
      mul_ne_zero (claspAlg_quantumInt_ne_zero (by omega))
        (claspAlg_quantumInt_ne_zero (by omega))
    rw [show p + 1 + 0 = p + 1 from rfl, show q + 1 + 0 = q + 1 from rfl, Nat.zero_add,
      capThick_one]
    have h0 : skPlace (p + 1 + (q + 1)) (p + 1 + (q + 1)) (p + 1) (capThick 0) = 1 := by
      rw [capThick_zero]
      exact skPlace_one _ _ 0 (by omega)
    have h1 : tlGenF (p + 1 + (q + 1)) (p + 1 - 1) =
        skPlace (p + 1 + (q + 1)) (p + q) p skCap * skPlace (p + q) (p + 1 + (q + 1)) p skCup := by
      rw [Nat.add_sub_cancel]
      exact rj_tlGenF_eq_cap_mul_cup _ _ _ (by omega) (by omega)
    rw [h0, Matrix.mul_one, Matrix.mul_one, rjTurnbackEigen, Nat.cast_zero, quantumInt_zero,
      zero_mul, neg_zero, zero_div, zero_smul, zero_add, add_zero, add_zero, div_self hne,
      one_smul, rjTurnbackOne, h1]
    simp only [Matrix.mul_assoc]
  | succ r ih =>
    have hp : quantumInt ((p : ℤ) + 1 + r) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
    have hq : quantumInt ((q : ℤ) + 1 + r) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
    have hp1 : quantumInt ((p : ℤ) + 1 + r + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
    have hq1 : quantumInt ((q : ℤ) + 1 + r + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
    have hS := rj_turnbackOne_succ_mul_skCap (p + 1 + r) (q + 1 + r)
    have habs := rj_bundleProj_mul_skCap_mul_bundleProj (p + 1 + r) (q + 1 + r)
    have hN1 : skPlace (p + 1 + (r + 1) + (q + 1 + (r + 1))) (p + 1 + (q + 1)) (p + 1)
          (capThick (r + 1)) =
        skPlace (p + 1 + (r + 1) + (q + 1 + (r + 1))) (p + 1 + r + (q + 1 + r)) (p + 1 + r)
            skCap *
          skPlace (p + 1 + r + (q + 1 + r)) (p + 1 + (q + 1)) (p + 1) (capThick r) :=
      rj_skPlace_capThick_succ_inner r _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
    have hN2 : skPlace (p + 1 + (r + 1) + (q + 1 + (r + 1))) (p + q) p (capThick (r + 1 + 1)) =
        skPlace (p + 1 + (r + 1) + (q + 1 + (r + 1))) (p + 1 + r + (q + 1 + r)) (p + 1 + r)
            skCap *
          skPlace (p + 1 + r + (q + 1 + r)) (p + q) p (capThick (r + 1)) :=
      rj_skPlace_capThick_succ_inner (r + 1) _ _ _ _ _ (by omega) (by omega) (by omega)
        (by omega)
    have hs1 : rjBubbleChi (p + 1 + r) (q + 1 + r) +
        rjBubblePsi (p + 1 + r) (q + 1 + r) * rjTurnbackEigen (p + 1 + r) (q + 1 + r) r =
          rjTurnbackEigen (p + 1 + (r + 1)) (q + 1 + (r + 1)) (r + 1) := by
      have e1 : ((p + 1 + (r + 1) : ℕ) : ℤ) = ((p + 1 + r : ℕ) : ℤ) + 1 := by push_cast; ring
      have e2 : ((q + 1 + (r + 1) : ℕ) : ℤ) = ((q + 1 + r : ℕ) : ℤ) + 1 := by push_cast; ring
      have e3 : ((r + 1 : ℕ) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
      rw [rjBubbleChi, rjBubblePsi, rjTurnbackEigen, rjTurnbackEigen, e1, e2, e3]
      refine rj_nu_step_scalar _ _ _ (Or.inr ⟨?_, ?_⟩) ?_ ?_ <;> push_cast <;> assumption
    have hs2 : rjBubblePsi (p + 1 + r) (q + 1 + r) *
        (quantumInt ((p : ℤ) + 1) * quantumInt ((q : ℤ) + 1) /
          (quantumInt ((p : ℤ) + 1 + r) * quantumInt ((q : ℤ) + 1 + r))) =
        quantumInt ((p : ℤ) + 1) * quantumInt ((q : ℤ) + 1) /
          (quantumInt ((p : ℤ) + 1 + ((r + 1 : ℕ) : ℤ)) *
            quantumInt ((q : ℤ) + 1 + ((r + 1 : ℕ) : ℤ))) := by
      rw [rjBubblePsi]
      push_cast
      rw [show (p : ℤ) + 1 + (r + 1) = p + 1 + r + 1 from by ring,
        show (q : ℤ) + 1 + (r + 1) = q + 1 + r + 1 from by ring]
      field_simp
    rw [hN1, hN2]
    refine (rj_oneSided_step_alg _ _ _ _ _ _ _ _ _ _ _ _ _ hS ih habs).trans ?_
    rw [hs1, hs2]
    rfl

/-- The first bundle closed completely by the nest. -/
theorem rj_turnbackOne_mul_capNest_full_left (a q : ℕ) :
    rjTurnbackOne a (a + q) * skPlace (a + (a + q)) q 0 (capThick a) =
      rjTurnbackEigen a (a + q) a •
        (rjBundleProj a (a + q) * skPlace (a + (a + q)) q 0 (capThick a)) := by
  induction a with
  | zero =>
    rw [rj_turnbackOne_eq_zero_of_empty 0 (0 + q) (Or.inl rfl), Matrix.zero_mul, rjTurnbackEigen,
      Nat.cast_zero, quantumInt_zero, zero_mul, neg_zero, zero_div, zero_smul]
  | succ a ih =>
    rw [show a + 1 + q = a + q + 1 from by omega]
    have hN : skPlace (a + 1 + (a + q + 1)) q 0 (capThick (a + 1)) =
        skPlace (a + 1 + (a + q + 1)) (a + (a + q)) a skCap *
          skPlace (a + (a + q)) q 0 (capThick a) :=
      rj_skPlace_capThick_succ_inner a _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
    have hs : rjBubbleChi a (a + q) + rjBubblePsi a (a + q) * rjTurnbackEigen a (a + q) a =
        rjTurnbackEigen (a + 1) (a + q + 1) (a + 1) := by
      rw [rjBubbleChi, rjBubblePsi, rjTurnbackEigen, rjTurnbackEigen, Nat.cast_add_one,
        Nat.cast_add_one]
      refine rj_nu_step_scalar _ _ _ ?_ (claspAlg_quantumInt_ne_zero (by omega))
        (claspAlg_quantumInt_ne_zero (by omega))
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · exact Or.inl (by rw [Nat.cast_zero, quantumInt_zero])
      · exact Or.inr ⟨claspAlg_quantumInt_ne_zero (by omega),
          claspAlg_quantumInt_ne_zero (by omega)⟩
    rw [hN]
    refine (rj_oneSided_full_step_alg _ _ _ _ _ _ _ _ _ (rj_turnbackOne_succ_mul_skCap a (a + q))
      ih (rj_bundleProj_mul_skCap_mul_bundleProj a (a + q))).trans ?_
    rw [hs]

/-- The second bundle closed completely by the nest. -/
theorem rj_turnbackOne_mul_capNest_full_right (p b : ℕ) :
    rjTurnbackOne (p + b) b * skPlace (p + b + b) p p (capThick b) =
      rjTurnbackEigen (p + b) b b •
        (rjBundleProj (p + b) b * skPlace (p + b + b) p p (capThick b)) := by
  induction b with
  | zero =>
    rw [rj_turnbackOne_eq_zero_of_empty (p + 0) 0 (Or.inr rfl), Matrix.zero_mul, rjTurnbackEigen,
      Nat.cast_zero, quantumInt_zero, zero_mul, neg_zero, zero_div, zero_smul]
  | succ b ih =>
    rw [show p + (b + 1) = p + b + 1 from rfl]
    have hN : skPlace (p + b + 1 + (b + 1)) p p (capThick (b + 1)) =
        skPlace (p + b + 1 + (b + 1)) (p + b + b) (p + b) skCap *
          skPlace (p + b + b) p p (capThick b) :=
      rj_skPlace_capThick_succ_inner b _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
    have hs : rjBubbleChi (p + b) b + rjBubblePsi (p + b) b * rjTurnbackEigen (p + b) b b =
        rjTurnbackEigen (p + b + 1) (b + 1) (b + 1) := by
      rw [rjBubbleChi, rjBubblePsi, rjTurnbackEigen, rjTurnbackEigen, Nat.cast_add_one,
        Nat.cast_add_one]
      refine rj_nu_step_scalar _ _ _ ?_ (claspAlg_quantumInt_ne_zero (by omega))
        (claspAlg_quantumInt_ne_zero (by omega))
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · exact Or.inl (by rw [Nat.cast_zero, quantumInt_zero])
      · exact Or.inr ⟨claspAlg_quantumInt_ne_zero (by omega),
          claspAlg_quantumInt_ne_zero (by omega)⟩
    rw [hN]
    refine (rj_oneSided_full_step_alg _ _ _ _ _ _ _ _ _ (rj_turnbackOne_succ_mul_skCap (p + b) b)
      ih (rj_bundleProj_mul_skCap_mul_bundleProj (p + b) b)).trans ?_
    rw [hs]

end AJConjecture
