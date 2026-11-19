import Mathlib
import AJTwist.Quantum.TwQSatEval
import AJHandoff.TorusQuantum.PairQJones

/-!
# The coloured Jones function of a twisted band-and-clasp satellite (Unit Q2)

Generalization of `pairQ_laurentToField_coloredJones` to signed twists, both clasp signs and
companions of any writhe. Let `C` have odd-colour input `u` with framing exponent `w ∈ ℤ`
(hypothesis `hC`), and let `IsBandClasp K C (2κ) σ` hold (the output of the isotopy: `2κ` signed
half twists, band framing `w + κ`).

* `twQ_coloredJones_of_isBandClasp_true`: for the negative clasp and `writhe K = -2κ - 2`, the
  coloured Jones function of `K` is `pairQFormula v`, `v_n = q^((w+κ) n(n+1)) u_n`.
* `twQ_coloredJones_of_isBandClasp_false`: for the positive clasp and `writhe K = -2κ + 2`, it
  is the bar of `pairQFormula v'`, `v'_n = q^(-(w+κ) n(n+1)) \bar u_n`.

The writhe hypotheses are forced: a half twist of sign `true` joins two antiparallel strands, so
it contributes `-1` to the writhe of `K`, and the clasp of sign `σ` contributes `∓ 2`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The unreduced formula vanishes at the colour `0`. -/
private theorem pairQFormula_zero_twQJones (u : ℕ → RatFunc ℚ) : pairQFormula u 0 = 0 := by
  simp only [pairQFormula, lt_irrefl, ite_false]

/-- The unreduced formula is odd in the colour. -/
private theorem pairQFormula_neg_twQJones (u : ℕ → RatFunc ℚ) (n : ℤ) :
    pairQFormula u (-n) = -pairQFormula u n := by
  unfold pairQFormula
  rcases lt_trichotomy 0 n with hn | hn | hn
  · have h1 : ¬ (0 : ℤ) < -n := by omega
    have h2 : -n < 0 := by omega
    simp only [h1, h2, hn, ite_true, ite_false, neg_neg]
  · subst hn
    simp only [neg_zero, lt_irrefl, ite_false]
  · have h1 : (0 : ℤ) < -n := by omega
    have h2 : ¬ (0 : ℤ) < n := by omega
    simp only [h1, h2, hn, ite_true, ite_false, neg_neg]

/-- If the coloured Jones function of `K` agrees with an odd function `F` at every positive
colour, it agrees at every integer colour. -/
private theorem laurentToField_coloredJones_of_pos_twQJones (K : BraidKnot)
    (F : ℤ → RatFunc ℚ) (h0 : F 0 = 0) (hodd : ∀ n : ℤ, F (-n) = -F n)
    (h : ∀ k : ℕ, laurentToField (coloredJonesPos K k) = F ((k : ℤ) + 1)) (n : ℤ) :
    laurentToField (coloredJones K n) = F n := by
  unfold coloredJones
  rcases lt_trichotomy 0 n with hn | hn | hn
  · have h1 : ((n.toNat - 1 : ℕ) : ℤ) + 1 = n := by omega
    simp only [hn, ite_true]
    rw [h, h1]
  · subst hn
    simp only [lt_irrefl, ite_false, map_zero, h0]
  · have hn' : ¬ (0 : ℤ) < n := by omega
    have h1 : (((-n).toNat - 1 : ℕ) : ℤ) + 1 = -n := by omega
    simp only [hn', hn, ite_false, ite_true]
    rw [map_neg, h, h1, hodd, neg_neg]

/-- The framing correction cancels the framing scalar of the band-and-clasp trace. -/
private theorem kinkScalar_zpow_neg_mul_cancel_twQJones (c : ℕ) (e : ℤ) (F : RatFunc ℚ) :
    (-1 : RatFunc ℚ) ^ c * kinkScalar c ^ (-e) * ((-1) ^ c * kinkScalar c ^ e * F) = F := by
  have hθ : kinkScalar c ≠ 0 := kinkScalar_ne_zero c
  have h1 : ((-1 : RatFunc ℚ) ^ c) * (-1) ^ c = 1 := by
    rw [← mul_pow]
    norm_num
  have h2 : kinkScalar c ^ (-e) * kinkScalar c ^ e = 1 := by
    rw [← zpow_add₀ hθ, neg_add_cancel, zpow_zero]
  calc (-1 : RatFunc ℚ) ^ c * kinkScalar c ^ (-e) * ((-1) ^ c * kinkScalar c ^ e * F)
      = ((-1 : RatFunc ℚ) ^ c * (-1) ^ c) * (kinkScalar c ^ (-e) * kinkScalar c ^ e) * F := by
        ring
    _ = F := by rw [h1, h2, one_mul, one_mul]

/-- The coloured Jones function of a band-and-clasp satellite with the negative clasp. -/
theorem twQ_coloredJones_of_isBandClasp_true (K C : BraidKnot) (w κ : ℤ)
    (u : ℕ → RatFunc ℚ)
    (hC : ∀ n : ℕ, knotTrace C (2 * n) (jwAt (2 * n) 0 (2 * n)) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * w * (n : ℤ) * ((n : ℤ) + 1)) * u n)
    (hK : IsBandClasp K C (2 * κ) true) (hw : writhe K.word = -(2 * κ) - 2) (n : ℤ) :
    laurentToField (coloredJones K n) =
      pairQFormula (fun i ↦ qParam ^ ((w + κ) * (i : ℤ) * ((i : ℤ) + 1)) * u i) n := by
  refine laurentToField_coloredJones_of_pos_twQJones K _ (pairQFormula_zero_twQJones _)
    (pairQFormula_neg_twQJones _) (fun c ↦ ?_) n
  rw [laurentToField_coloredJonesPos, twQ_knotTrace_jwAt_of_isBandClasp hK c,
    twSatTrace_true_eq C w κ u hC c, hw]
  exact kinkScalar_zpow_neg_mul_cancel_twQJones c _ _

/-- The coloured Jones function of a band-and-clasp satellite with the positive clasp. -/
theorem twQ_coloredJones_of_isBandClasp_false (K C : BraidKnot) (w κ : ℤ)
    (u : ℕ → RatFunc ℚ)
    (hC : ∀ n : ℕ, knotTrace C (2 * n) (jwAt (2 * n) 0 (2 * n)) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * w * (n : ℤ) * ((n : ℤ) + 1)) * u n)
    (hK : IsBandClasp K C (2 * κ) false) (hw : writhe K.word = -(2 * κ) + 2) (n : ℤ) :
    laurentToField (coloredJones K n) =
      twQBar (pairQFormula
        (fun i ↦ qParam ^ (-((w + κ) * (i : ℤ) * ((i : ℤ) + 1))) * twQBar (u i)) n) := by
  refine laurentToField_coloredJones_of_pos_twQJones K
    (fun m ↦ twQBar (pairQFormula
      (fun i ↦ qParam ^ (-((w + κ) * (i : ℤ) * ((i : ℤ) + 1))) * twQBar (u i)) m))
    ?_ (fun m ↦ ?_) (fun c ↦ ?_) n
  · rw [pairQFormula_zero_twQJones, map_zero]
  · rw [pairQFormula_neg_twQJones, map_neg]
  · rw [laurentToField_coloredJonesPos, twQ_knotTrace_jwAt_of_isBandClasp hK c,
      twSatTrace_false_eq C w κ u hC c, hw]
    exact kinkScalar_zpow_neg_mul_cancel_twQJones c _ _

end AJConjecture
