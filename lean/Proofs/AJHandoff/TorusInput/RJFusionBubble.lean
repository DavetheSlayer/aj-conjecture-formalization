import Mathlib
import AJHandoff.TorusInput.RJFusionBasic
import AJConjecture.SkeinBubble
import AJConjecture.SkeinJwCupCap

/-!
# The bubble lemma for two unequal bundles (node RA1.2)

`cup · (f_(a+1) ⊗ f_(b+1)) · cap = χ (f_a ⊗ f_b) + ψ D_1`, with `χ = -[a+b+2]/([a+1][b+1])`,
`ψ = [a][b]/([a+1][b+1])`, the cup creating (and the cap closing) the last strand of the first
bundle and the first strand of the second. For `a = b` this is `skCup_mul_twoBundleProj_mul_skCap`
(`AJConjecture.SkeinBubble`).

Route. As in `SkeinBubble`: expand `f_(a+1) = f_a + x f_a e_(a-1) f_a` (`x = [a]/[a+1]`, the
definition of `jwAt`) and `f_(b+1) = f_b + y f_b e_(a+1) f_b` (`y = [b]/[b+1]`,
`jwAt_succ_succ_left`); the projectors `f_a`, `f_b` pass the cup and the cap; the four terms are
the loop `δ`, two zig-zags (`cupAt_mul_tlGenF_succ_mul_capAt`,
`cupAt_succ_mul_tlGenF_mul_capAt_succ`) giving `x` and `y`, and
`cupAt_succ_mul_tlGenF_mul_tlGenF_mul_capAt_succ` giving `x y g e_(a-1) g`. The scalar is
`δ + x + y = -[a+b+2]/([a+1][b+1])` (from `quantumInt_mul_shift_sub`). The generic algebra
`bubble_expand_alg` of `SkeinBubble` is private: copy it. For `a = 0` or `b = 0`, `ψ = 0`.
Numerically checked for `1 ≤ a, b ≤ 4` (design notes). Proved: the calibration of RA1, a
direct re-parametrization of `SkeinBubble` (about 200 lines).
-/

noncomputable section

namespace AJConjecture

/-- The algebra of the unequal bubble lemma. -/
private theorem rj_bubble_expand_alg {K m N : Type*} [CommRing K] [Fintype m] [Fintype N]
    [DecidableEq m] [DecidableEq N] (u : Matrix m N K) (v : Matrix N m K)
    (G1 G2 e1 e2 : Matrix N N K) (g1 g2 e : Matrix m m K) (x y δ : K)
    (h1 : u * G1 = g1 * u) (h2 : u * G2 = g2 * u) (h3 : G1 * v = v * g1) (h4 : G2 * v = v * g2)
    (hc : G1 * G2 = G2 * G1) (hG1e2 : G1 * e2 = e2 * G1) (hG2e1 : G2 * e1 = e1 * G2)
    (huv : u * v = δ • (1 : Matrix m m K)) (hue1v : u * e1 * v = 1) (hue2v : u * e2 * v = 1)
    (hue1e2v : u * e1 * e2 * v = e) (hg1 : g1 * g1 = g1) (hg2 : g2 * g2 = g2) :
    u * ((G1 + x • (G1 * e1 * G1)) * (G2 + y • (G2 * e2 * G2))) * v =
      (δ + x + y) • (g1 * g2) + (x * y) • (g1 * g2 * e * (g1 * g2)) := by
  have t1 : u * (G1 * G2) * v = δ • (g1 * g2) :=
    calc u * (G1 * G2) * v = (u * G1) * (G2 * v) := by simp only [Matrix.mul_assoc]
      _ = g1 * (u * v) * g2 := by rw [h1, h4]; simp only [Matrix.mul_assoc]
      _ = δ • (g1 * g2) := by rw [huv, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have t2 : u * (G1 * e1 * G1 * G2) * v = g1 * g2 :=
    calc u * (G1 * e1 * G1 * G2) * v = (u * G1) * e1 * G1 * (G2 * v) := by
          simp only [Matrix.mul_assoc]
      _ = g1 * u * e1 * (G1 * v) * g2 := by rw [h1, h4]; simp only [Matrix.mul_assoc]
      _ = g1 * (u * e1 * v) * (g1 * g2) := by rw [h3]; simp only [Matrix.mul_assoc]
      _ = g1 * g2 := by rw [hue1v, Matrix.mul_one, ← Matrix.mul_assoc, hg1]
  have t3 : u * (G1 * (G2 * e2 * G2)) * v = g1 * g2 :=
    calc u * (G1 * (G2 * e2 * G2)) * v = (u * G1) * G2 * e2 * (G2 * v) := by
          simp only [Matrix.mul_assoc]
      _ = g1 * (u * G2) * e2 * v * g2 := by rw [h1, h4]; simp only [Matrix.mul_assoc]
      _ = g1 * g2 * (u * e2 * v) * g2 := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = g1 * g2 := by rw [hue2v, Matrix.mul_one, Matrix.mul_assoc, hg2]
  have t4 : u * (G1 * e1 * G1 * (G2 * e2 * G2)) * v = g1 * g2 * e * (g1 * g2) :=
    calc u * (G1 * e1 * G1 * (G2 * e2 * G2)) * v =
          (u * G1) * e1 * (G1 * G2) * e2 * (G2 * v) := by simp only [Matrix.mul_assoc]
      _ = g1 * u * e1 * G2 * (G1 * e2) * v * g2 := by
          rw [h1, h4, hc]; simp only [Matrix.mul_assoc]
      _ = g1 * u * (e1 * G2) * e2 * (G1 * v) * g2 := by rw [hG1e2]; simp only [Matrix.mul_assoc]
      _ = g1 * (u * G2) * e1 * e2 * v * g1 * g2 := by
          rw [← hG2e1, h3]; simp only [Matrix.mul_assoc]
      _ = g1 * g2 * (u * e1 * e2 * v) * (g1 * g2) := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = g1 * g2 * e * (g1 * g2) := by rw [hue1e2v]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  rw [t1, t2, t3, t4]
  module

/-- The unequal bubble lemma with the ambient sizes written as `n` and `n + 2`, both bundles
nonempty after the cup. -/
private theorem rj_bubble_succ_succ (a b n : ℕ) (hn : n = a + 1 + (b + 1)) :
    cupAt n (a + 1) * (jwAt (n + 2) 0 (a + 2) * jwAt (n + 2) (a + 2) (b + 2)) * capAt n (a + 1) =
      ((-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) +
          quantumInt ((a : ℤ) + 1) / quantumInt ((a : ℤ) + 2) +
          quantumInt ((b : ℤ) + 1) / quantumInt ((b : ℤ) + 2)) •
        (jwAt n 0 (a + 1) * jwAt n (a + 1) (b + 1)) +
      (quantumInt ((a : ℤ) + 1) / quantumInt ((a : ℤ) + 2) *
          (quantumInt ((b : ℤ) + 1) / quantumInt ((b : ℤ) + 2))) •
        (jwAt n 0 (a + 1) * jwAt n (a + 1) (b + 1) * tlGenF n a *
          (jwAt n 0 (a + 1) * jwAt n (a + 1) (b + 1))) := by
  subst hn
  have hJ1 : jwAt (a + 1 + (b + 1) + 2) 0 (a + 2) = jwAt (a + 1 + (b + 1) + 2) 0 (a + 1) +
      (quantumInt ((a : ℤ) + 1) / quantumInt ((a : ℤ) + 2)) •
        (jwAt (a + 1 + (b + 1) + 2) 0 (a + 1) * tlGenF (a + 1 + (b + 1) + 2) a *
          jwAt (a + 1 + (b + 1) + 2) 0 (a + 1)) := by
    rw [jwAt, Nat.zero_add]
  have hJ2 := jwAt_succ_succ_left (a + 1 + (b + 1) + 2) (a + 2) b (by omega)
  rw [hJ1, hJ2]
  refine rj_bubble_expand_alg _ _ _ _ _ _ _ _ _ _ _ _
    (cupAt_mul_jwAt_of_le (a + 1 + (b + 1)) 0 (a + 1) (a + 1) (by omega))
    (cupAt_mul_jwAt_of_ge (a + 1 + (b + 1)) (a + 1) (b + 1) (a + 1) le_rfl)
    (jwAt_mul_capAt_of_le (a + 1 + (b + 1)) 0 (a + 1) (a + 1) (by omega))
    (jwAt_mul_capAt_of_ge (a + 1 + (b + 1)) (a + 1) (b + 1) (a + 1) le_rfl)
    (commute_jwAt_of_commute_tlGenF _ _ _ _ fun l _ ↦
      jwAt_commute_tlGenF _ 0 (a + 1) _ (Or.inr (by omega))).eq
    (jwAt_commute_tlGenF _ 0 (a + 1) (a + 2) (Or.inr (by omega))).eq
    (jwAt_commute_tlGenF _ (a + 2 + 1) (b + 1) a (Or.inl (by omega))).eq
    (cupAt_mul_capAt (a + 1 + (b + 1)) (a + 1) (by omega))
    (cupAt_succ_mul_tlGenF_mul_capAt_succ (a + 1 + (b + 1)) a (by omega))
    (cupAt_mul_tlGenF_succ_mul_capAt (a + 1 + (b + 1)) (a + 1) (by omega))
    (cupAt_succ_mul_tlGenF_mul_tlGenF_mul_capAt_succ (a + 1 + (b + 1)) a)
    (jwAt_mul_self _ _ _) (jwAt_mul_self _ _ _)


/-- `[2] = t² + t⁻²`. -/
private theorem rj_quantumInt_two :
    quantumInt 2 = (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) + RatFunc.X ^ (-2 : ℤ) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hD := claspAlg_ratFuncX_sq_sub_ne_zero
  rw [quantumInt, div_eq_iff hD]
  rw [show (2 : ℤ) * 2 = 2 + 2 from rfl, show -((2 : ℤ) + 2) = -2 + -2 from rfl,
    zpow_add₀ hX, zpow_add₀ hX]
  ring

/-- The scalar of the bubble: `δ [a+1][b+1] + [a][b+1] + [b][a+1] = -[a+b+2]`. -/
private theorem rj_bubble_scalar (a b : ℤ) :
    (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) *
        (quantumInt (a + 1) * quantumInt (b + 1)) +
      quantumInt a * quantumInt (b + 1) + quantumInt b * quantumInt (a + 1) =
      -quantumInt (a + b + 2) := by
  have h1 := quantumInt_mul_shift_sub (a + 1) b 1
  have h2 := quantumInt_mul_shift_sub 1 a 1
  rw [quantumInt_one, one_mul, show a + 1 + b + 1 = a + b + 2 from by ring] at h1
  rw [quantumInt_one, one_mul, one_mul, show (1 : ℤ) + a + 1 = a + 1 + 1 from by ring,
    show (1 : ℤ) + 1 = 2 from rfl, rj_quantumInt_two] at h2
  linear_combination (-1 : RatFunc ℚ) * h1 - quantumInt (b + 1) * h2

/-- The first bubble coefficient as a sum. -/
private theorem rj_chi_eq (A B : ℤ) (hA : quantumInt (A + 1) ≠ 0) (hB : quantumInt (B + 1) ≠ 0) :
    -quantumInt (A + B + 2) / (quantumInt (A + 1) * quantumInt (B + 1)) =
      (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) +
        quantumInt A / quantumInt (A + 1) + quantumInt B / quantumInt (B + 1) := by
  have h := rj_bubble_scalar A B
  generalize (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) = d at h ⊢
  field_simp
  linear_combination -h

/-- A cup and a cap around `A + c A e A` with `A` sliding through both. -/
private theorem rj_one_side_alg {K m N : Type*} [CommRing K] [Fintype m] [Fintype N]
    [DecidableEq m] [DecidableEq N] (u : Matrix m N K) (v : Matrix N m K) (A e : Matrix N N K)
    (f : Matrix m m K) (c δ : K) (hu : u * A = f * u) (hv : A * v = v * f)
    (huv : u * v = δ • (1 : Matrix m m K)) (huev : u * e * v = 1) (hf : f * f = f) :
    u * (A + c • (A * e * A)) * v = (δ + c) • f := by
  have t1 : u * A * v = δ • f := by
    rw [hu, Matrix.mul_assoc, huv, Matrix.mul_smul, Matrix.mul_one]
  have t2 : u * (A * e * A) * v = f := by
    calc u * (A * e * A) * v = (u * A) * e * (A * v) := by simp only [Matrix.mul_assoc]
      _ = f * (u * e * v) * f := by rw [hu, hv]; simp only [Matrix.mul_assoc]
      _ = f := by rw [huev, Matrix.mul_one, hf]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, t1, t2, add_smul]

/-- The unequal bubble lemma, all ambient sizes free. -/
private theorem rj_bubble_aux (a b n N : ℕ) (hN : N = n + 2) (hn : n = a + b) :
    skPlace n N a skCup * (jwAt N 0 (a + 1) * jwAt N (a + 1) (b + 1)) * skPlace N n a skCap =
      rjBubbleChi a b • (jwAt n 0 a * jwAt n a b) +
        rjBubblePsi a b • (jwAt n 0 a * jwAt n a b * tlGenF n (a - 1) *
          (jwAt n 0 a * jwAt n a b)) := by
  subst hN
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  change cupAt n a * (jwAt (n + 2) 0 (a + 1) * jwAt (n + 2) (a + 1) (b + 1)) * capAt n a = _
  rcases a with _ | a <;> rcases b with _ | b
  · subst hn
    have hpsi : rjBubblePsi 0 0 = 0 := by
      rw [rjBubblePsi, Nat.cast_zero, quantumInt_zero, zero_mul, zero_div]
    have hchi : rjBubbleChi 0 0 = -(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ) := by
      simp only [rjBubbleChi, Nat.cast_zero, zero_add, quantumInt_one, mul_one, div_one,
        rj_quantumInt_two]
      ring
    rw [hpsi, zero_smul, add_zero, hchi]
    simp only [jwAt, Matrix.mul_one, add_zero]
    exact cupAt_mul_capAt 0 0 le_rfl
  · obtain rfl : n = b + 1 := by omega
    have hpsi : rjBubblePsi 0 (b + 1) = 0 := by
      rw [rjBubblePsi, Nat.cast_zero, quantumInt_zero, zero_mul, zero_div]
    have hne : quantumInt ((b : ℤ) + 2) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
    have hchi : rjBubbleChi 0 (b + 1) =
        (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) +
          quantumInt ((b : ℤ) + 1) / quantumInt ((b : ℤ) + 2) := by
      have h := rj_chi_eq 0 ((b : ℤ) + 1) (by rw [zero_add, quantumInt_one]; exact one_ne_zero)
        (by rw [show (b : ℤ) + 1 + 1 = (b : ℤ) + 2 from by ring]; exact hne)
      rw [quantumInt_zero, zero_div, add_zero, show (b : ℤ) + 1 + 1 = (b : ℤ) + 2 from by ring,
        show (0 : ℤ) + ((b : ℤ) + 1) + 2 = (b : ℤ) + 1 + 2 from by ring] at h
      rw [← h, rjBubbleChi]
      push_cast
      ring_nf
    have hJ := jwAt_succ_succ_left (b + 1 + 2) 1 b (by omega)
    rw [hpsi, zero_smul, add_zero, hchi]
    have h1 : jwAt (b + 1 + 2) 0 (0 + 1) = 1 := rfl
    have h0 : jwAt (b + 1) 0 0 = 1 := rfl
    rw [h1, Matrix.one_mul, h0, Matrix.one_mul]
    change cupAt (b + 1) 0 * jwAt (b + 1 + 2) 1 (b + 2) * capAt (b + 1) 0 = _
    rw [hJ]
    exact rj_one_side_alg _ _ _ _ _ _ _
      (cupAt_mul_jwAt_of_ge (b + 1) 0 (b + 1) 0 le_rfl)
      (jwAt_mul_capAt_of_ge (b + 1) 0 (b + 1) 0 le_rfl)
      (cupAt_mul_capAt (b + 1) 0 (by omega))
      (cupAt_mul_tlGenF_succ_mul_capAt (b + 1) 0 (by omega))
      (jwAt_mul_self _ _ _)
  · obtain rfl : n = a + 1 := by omega
    have hpsi : rjBubblePsi (a + 1) 0 = 0 := by
      rw [rjBubblePsi, Nat.cast_zero, quantumInt_zero, mul_zero, zero_div]
    rw [hpsi, zero_smul, add_zero]
    have h1 : jwAt (a + 1 + 2) (a + 1 + 1) (0 + 1) = 1 := rfl
    have h0 : jwAt (a + 1) (a + 1) 0 = 1 := rfl
    rw [h1, Matrix.mul_one, h0, Matrix.mul_one, cupAt_mul_jwAt_mul_capAt (a + 1) (a + 1) le_rfl]
    congr 1
    rw [rjBubbleChi]
    push_cast
    rw [quantumInt_one, mul_one, add_zero, neg_div]
  · have h := rj_bubble_succ_succ a b n hn
    refine h.trans ?_
    have hA : quantumInt ((a : ℤ) + 2) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
    have hB : quantumInt ((b : ℤ) + 2) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
    rw [Nat.add_sub_cancel]
    congr 2
    · have h2 := rj_chi_eq ((a : ℤ) + 1) ((b : ℤ) + 1)
        (by rw [show (a : ℤ) + 1 + 1 = (a : ℤ) + 2 from by ring]; exact hA)
        (by rw [show (b : ℤ) + 1 + 1 = (b : ℤ) + 2 from by ring]; exact hB)
      rw [show (a : ℤ) + 1 + 1 = (a : ℤ) + 2 from by ring,
        show (b : ℤ) + 1 + 1 = (b : ℤ) + 2 from by ring] at h2
      rw [← h2, rjBubbleChi]
      push_cast
      ring_nf
    · rw [rjBubblePsi]
      push_cast
      rw [div_mul_div_comm]
      ring_nf

/-- The bubble lemma for `f_(a+1) ⊗ f_(b+1)`. -/
theorem rj_bubble (a b : ℕ) :
    skPlace (a + b) (a + 1 + (b + 1)) a skCup * rjBundleProj (a + 1) (b + 1) *
        skPlace (a + 1 + (b + 1)) (a + b) a skCap =
      rjBubbleChi a b • rjBundleProj a b + rjBubblePsi a b • rjTurnbackOne a b :=
  rj_bubble_aux a b (a + b) (a + 1 + (b + 1)) (by omega) rfl

end AJConjecture
