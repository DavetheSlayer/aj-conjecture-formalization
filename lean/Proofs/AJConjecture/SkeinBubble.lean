import Mathlib
import AJConjecture.SkeinTurnbackEigenBasic
import AJFamily.Skein.TorusOddColorOne
import AJConjecture.SkeinCupTlCap
import AJConjecture.SkeinHalfTwist
import AJConjecture.SkeinJwCapComm
import AJConjecture.SkeinJwMirror

/-!
# The bubble lemma

Two bundles of `a + 1` strands with projectors, the last strand of the first joined to the first
strand of the second by a cup below and a cap above:
`cup · (f_{a+1} ⊗ f_{a+1}) · cap = -([2a+2]/[a+1]²) g + ([a]²/[a+1]²) g e_{a-1} g` with
`g = f_a ⊗ f_a`.

Route. Expand the first projector by Wenzl's recursion (new strand on the right, the definition
of `AJConjecture.jwAt`) and the second by the recursion from the left
(`AJConjecture.jwAt_succ_succ_left`): `f_{a+1} = f_a + x f_a e f_a` with `x = [a]/[a+1]`, the
generators being `e_{a-1}` and `e_{a+1}` of `V^{⊗ (2a+2)}`. The projectors `f_a` commute with the
cup
and the cap (`AJConjecture.jwAt_mul_capAt_of_le`, `AJConjecture.jwAt_mul_capAt_of_ge` and the
statements for cups) and with each other. The four terms are: a loop, `δ g`; twice a generator
between the cup and the cap, `x g` each (`AJConjecture.cupAt_mul_tlGenF_succ_mul_capAt`,
`AJConjecture.cupAt_succ_mul_tlGenF_mul_capAt_succ`); and `x² g e_{a-1} g`
(`AJConjecture.cupAt_succ_mul_tlGenF_mul_tlGenF_mul_capAt_succ`). Finally
`δ + 2x = ([a] - [a+2])/[a+1] = -[2a+2]/[a+1]²`. For `a = 0` the statement is the loop value.
-/

namespace AJConjecture

/-- `[2] = t² + t⁻²`. -/
private theorem quantumInt_two_bubble :
    quantumInt 2 = (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) + RatFunc.X ^ (-2 : ℤ) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hD := claspAlg_ratFuncX_sq_sub_ne_zero
  rw [quantumInt, div_eq_iff hD]
  rw [show (2 : ℤ) * 2 = 2 + 2 from rfl, show -((2 : ℤ) + 2) = -2 + -2 from rfl,
    zpow_add₀ hX, zpow_add₀ hX]
  ring

/-- `[0] = 0`. -/
theorem quantumInt_zero : quantumInt 0 = 0 := by
  rw [quantumInt, mul_zero, neg_zero, sub_self, zero_div]

/-- The scalar of the bubble: `δ + 2 [m]/[m+1] = -[2m+2]/[m+1]²`. -/
private theorem loop_add_two_quantumInt_div_bubble (m : ℤ) (hm : quantumInt (m + 1) ≠ 0) :
    (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) +
        2 * (quantumInt m / quantumInt (m + 1)) =
      -quantumInt (2 * m + 2) / quantumInt (m + 1) ^ 2 := by
  have h1 := quantumInt_mul_shift_sub (m + 1) m 1
  have h2 := quantumInt_mul_shift_sub 1 m 1
  rw [quantumInt_one, one_mul, show m + 1 + m + 1 = 2 * m + 2 from by ring] at h1
  rw [quantumInt_one, one_mul, one_mul,
    show (1 : ℤ) + m + 1 = m + 1 + 1 from by ring] at h2
  rw [show (1 : ℤ) + 1 = 2 from rfl, quantumInt_two_bubble] at h2
  rw [show -(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ) =
    -((RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) + RatFunc.X ^ (-2 : ℤ)) from by ring]
  generalize (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) + RatFunc.X ^ (-2 : ℤ) = d at h2 ⊢
  field_simp
  linear_combination (-1 : RatFunc ℚ) * h1 - quantumInt (m + 1) * h2

/-- An operator that commutes with the generators of a window commutes with its projector. -/
theorem commute_jwAt_of_commute_tlGenF (n i : ℕ) (X : SkMat n n) :
    ∀ k : ℕ, (∀ l : ℕ, l + 2 ≤ k → Commute X (tlGenF n (i + l))) → Commute X (jwAt n i k)
  | 0, _ => by rw [jwAt]; exact Commute.one_right _
  | 1, _ => by rw [jwAt]; exact Commute.one_right _
  | k + 2, h => by
    have ih := commute_jwAt_of_commute_tlGenF n i X (k + 1) fun l hl ↦ h l (by omega)
    rw [jwAt]
    exact ih.add_right (((ih.mul_right (h k le_rfl)).mul_right ih).smul_right _)

/-- The algebra of the bubble lemma: both projectors are expanded, `u` is the cup and `v` the
cap. -/
private theorem bubble_expand_alg {K m N : Type*} [CommRing K] [Fintype m] [Fintype N]
    [DecidableEq m] [DecidableEq N] (u : Matrix m N K) (v : Matrix N m K)
    (G1 G2 e1 e2 : Matrix N N K) (g1 g2 e : Matrix m m K) (x δ : K)
    (h1 : u * G1 = g1 * u) (h2 : u * G2 = g2 * u) (h3 : G1 * v = v * g1) (h4 : G2 * v = v * g2)
    (hc : G1 * G2 = G2 * G1) (hG1e2 : G1 * e2 = e2 * G1) (hG2e1 : G2 * e1 = e1 * G2)
    (huv : u * v = δ • (1 : Matrix m m K)) (hue1v : u * e1 * v = 1) (hue2v : u * e2 * v = 1)
    (hue1e2v : u * e1 * e2 * v = e) (hg1 : g1 * g1 = g1) (hg2 : g2 * g2 = g2) :
    u * ((G1 + x • (G1 * e1 * G1)) * (G2 + x • (G2 * e2 * G2))) * v =
      (δ + 2 * x) • (g1 * g2) + x ^ 2 • (g1 * g2 * e * (g1 * g2)) := by
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

/-- The bubble lemma for two bundles of `b + 2` strands, the smaller ambient size being free. -/
private theorem cupAt_mul_jwAt_mul_jwAt_mul_capAt_bubble (b n : ℕ) (hn : n = 2 * b + 2) :
    cupAt n (b + 1) * (jwAt (n + 2) 0 (b + 2) * jwAt (n + 2) (b + 2) (b + 2)) * capAt n (b + 1) =
      ((-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) +
          2 * (quantumInt ((b : ℤ) + 1) / quantumInt ((b : ℤ) + 2))) •
        (jwAt n 0 (b + 1) * jwAt n (b + 1) (b + 1)) +
      (quantumInt ((b : ℤ) + 1) / quantumInt ((b : ℤ) + 2)) ^ 2 •
        (jwAt n 0 (b + 1) * jwAt n (b + 1) (b + 1) * tlGenF n b *
          (jwAt n 0 (b + 1) * jwAt n (b + 1) (b + 1))) := by
  subst hn
  have hJ1 : jwAt (2 * b + 2 + 2) 0 (b + 2) = jwAt (2 * b + 2 + 2) 0 (b + 1) +
      (quantumInt ((b : ℤ) + 1) / quantumInt ((b : ℤ) + 2)) •
        (jwAt (2 * b + 2 + 2) 0 (b + 1) * tlGenF (2 * b + 2 + 2) b *
          jwAt (2 * b + 2 + 2) 0 (b + 1)) := by
    rw [jwAt, Nat.zero_add]
  have hJ2 := jwAt_succ_succ_left (2 * b + 2 + 2) (b + 2) b (by omega)
  rw [hJ1, hJ2]
  refine bubble_expand_alg _ _ _ _ _ _ _ _ _ _ _
    (cupAt_mul_jwAt_of_le (2 * b + 2) 0 (b + 1) (b + 1) (by omega))
    (cupAt_mul_jwAt_of_ge (2 * b + 2) (b + 1) (b + 1) (b + 1) le_rfl)
    (jwAt_mul_capAt_of_le (2 * b + 2) 0 (b + 1) (b + 1) (by omega))
    (jwAt_mul_capAt_of_ge (2 * b + 2) (b + 1) (b + 1) (b + 1) le_rfl)
    (commute_jwAt_of_commute_tlGenF _ _ _ _ fun l _ ↦
      jwAt_commute_tlGenF _ 0 (b + 1) _ (Or.inr (by omega))).eq
    (jwAt_commute_tlGenF _ 0 (b + 1) (b + 2) (Or.inr (by omega))).eq
    (jwAt_commute_tlGenF _ (b + 2 + 1) (b + 1) b (Or.inl (by omega))).eq
    (cupAt_mul_capAt (2 * b + 2) (b + 1) (by omega))
    (cupAt_succ_mul_tlGenF_mul_capAt_succ (2 * b + 2) b (by omega))
    (cupAt_mul_tlGenF_succ_mul_capAt (2 * b + 2) (b + 1) (by omega))
    (cupAt_succ_mul_tlGenF_mul_tlGenF_mul_capAt_succ (2 * b + 2) b)
    (jwAt_mul_self _ _ _) (jwAt_mul_self _ _ _)

/-- The bubble lemma for two bundles of `a + 1` strands. -/
theorem skCup_mul_twoBundleProj_mul_skCap (a : ℕ) :
    skPlace (2 * a) (2 * (a + 1)) a skCup * twoBundleProj (a + 1) *
        skPlace (2 * (a + 1)) (2 * a) a skCap =
      (-(quantumInt (2 * (a : ℤ) + 2)) / quantumInt ((a : ℤ) + 1) ^ 2) • twoBundleProj a +
        (quantumInt (a : ℤ) ^ 2 / quantumInt ((a : ℤ) + 1) ^ 2) •
          (twoBundleProj a * tlGenF (2 * a) (a - 1) * twoBundleProj a) := by
  rcases a with _ | b
  · have hP1 : twoBundleProj (0 + 1) = 1 := by rw [twoBundleProj, jwAt, jwAt, Matrix.one_mul]
    have hP0 : twoBundleProj 0 = 1 := by rw [twoBundleProj, jwAt, Matrix.one_mul]
    have hs1 : -(quantumInt (2 * ((0 : ℕ) : ℤ) + 2)) / quantumInt (((0 : ℕ) : ℤ) + 1) ^ 2 =
        -(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ) := by
      rw [Nat.cast_zero, mul_zero, zero_add, zero_add, quantumInt_one,
        quantumInt_two_bubble]
      ring
    have hs2 : quantumInt ((0 : ℕ) : ℤ) ^ 2 / quantumInt (((0 : ℕ) : ℤ) + 1) ^ 2 = 0 := by
      rw [Nat.cast_zero, quantumInt_zero]
      ring
    rw [hP1, hP0, Matrix.mul_one, hs1, hs2, zero_smul, add_zero]
    exact cupAt_mul_capAt 0 0 le_rfl
  · refine (cupAt_mul_jwAt_mul_jwAt_mul_capAt_bubble b (2 * (b + 1)) (by omega)).trans ?_
    have hne : quantumInt ((b : ℤ) + 1 + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
    rw [Nat.cast_succ, show (b : ℤ) + 2 = (b : ℤ) + 1 + 1 from by ring,
      loop_add_two_quantumInt_div_bubble _ hne, div_pow, Nat.add_sub_cancel]
    rfl

end AJConjecture
