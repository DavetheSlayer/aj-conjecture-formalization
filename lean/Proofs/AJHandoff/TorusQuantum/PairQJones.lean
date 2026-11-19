import Mathlib
import AJConjecture.SkeinChebyshevProjector
import AJConjecture.SkeinColorReduction
import AJHandoff.TorusQuantum.PairQSatelliteEval

/-!
# T-JONES for an arbitrary companion

`pairQ_laurentToField_coloredJones`: let `C` be a braid knot (the companion) with odd-colour
input `u` (hypothesis `hC`, with framing exponent `w`), and let `K` be a braid knot whose
long-knot operator at every colour `c` is the partial trace of the band-and-clasp operator over
`C` with `2w` negative half twists (hypothesis `hK`, the output of the isotopy), and whose writhe
is `2w - 2`. Then the coloured Jones function of `K` is `pairQFormula u` at every integer colour,
with `q = t⁴` kept throughout.

For `C = torusKnot k`, `w = 2k + 1`, `K = whiteheadTorusKnot k hk` this is the library's
`laurentToField_coloredJones_whiteheadTorusKnot`. For the torus pair `(r, s)` one takes
`C = torusPairKnot r s h`, `w = (r - 1) s` (the writhe of `torusPairWord r s`): see
`AJHandoff.TorusQuantum.PairQTorusInput`.

The clauses `J_0 = 0` and `J_(-n) = -J_n` of the contract hold by the definition of
`coloredJones` for every braid knot (`pairQ_coloredJones_zero`, `pairQ_coloredJones_neg`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- If the coloured Jones function of `K` agrees with `pairQFormula u` at every positive colour,
it agrees at every integer colour: both sides are odd in the colour. -/
private theorem laurentToField_coloredJones_of_pos_pairQ (K : BraidKnot) (u : ℕ → RatFunc ℚ)
    (h : ∀ k : ℕ, laurentToField (coloredJonesPos K k) = pairQFormula u ((k : ℤ) + 1))
    (n : ℤ) : laurentToField (coloredJones K n) = pairQFormula u n := by
  unfold coloredJones
  rcases lt_trichotomy 0 n with hn | hn | hn
  · have h1 : ((n.toNat - 1 : ℕ) : ℤ) + 1 = n := by omega
    simp only [hn, ite_true]
    rw [h, h1]
  · subst hn
    simp [pairQFormula]
  · have hn' : ¬ (0 : ℤ) < n := by omega
    have hpos : (0 : ℤ) < -n := by omega
    have h1 : (((-n).toNat - 1 : ℕ) : ℤ) + 1 = -n := by omega
    simp only [hn', hn, ite_false, ite_true]
    rw [map_neg, h, h1]
    simp only [pairQFormula, hpos, hn', hn, ite_true, ite_false, neg_neg]

/-- T-JONES: the coloured Jones function of a band-and-clasp satellite of a companion with
odd-colour input `u` is the closed formula of `u`. -/
theorem pairQ_laurentToField_coloredJones (K C : BraidKnot) (w : ℕ) (u : ℕ → RatFunc ℚ)
    (hC : ∀ n : ℕ, knotTrace C (2 * n) (jwAt (2 * n) 0 (2 * n)) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (w : ℤ) * (n : ℤ) * ((n : ℤ) + 1)) * u n)
    (hK : ∀ c : ℕ, longKnotOp K c =
      ptrTail c (2 * c) (longKnotOp C (2 * c) * (halfTwist c false ^ (2 * w) * claspOp c)))
    (hw : writhe K.word = 2 * (w : ℤ) - 2) (n : ℤ) :
    laurentToField (coloredJones K n) = pairQFormula u n := by
  refine laurentToField_coloredJones_of_pos_pairQ K u (fun c ↦ ?_) n
  rw [laurentToField_coloredJonesPos,
    pairQ_knotTrace_jwAt_of_longKnotOp K C w c (hK c), pairQSatTrace_eq C w u hC c, hw]
  have hθ : kinkScalar c ≠ 0 := kinkScalar_ne_zero c
  have h1 : ((-1 : RatFunc ℚ) ^ c) * (-1) ^ c = 1 := by
    rw [← mul_pow]
    norm_num
  have h2 : kinkScalar c ^ (-(2 * (w : ℤ) - 2)) * kinkScalar c ^ (2 * (w : ℤ) - 2) = 1 := by
    rw [← zpow_add₀ hθ, neg_add_cancel, zpow_zero]
  calc (-1 : RatFunc ℚ) ^ c * kinkScalar c ^ (-(2 * (w : ℤ) - 2)) *
        ((-1) ^ c * kinkScalar c ^ (2 * (w : ℤ) - 2) * pairQFormula u ((c : ℤ) + 1))
      = ((-1 : RatFunc ℚ) ^ c * (-1) ^ c) *
          (kinkScalar c ^ (-(2 * (w : ℤ) - 2)) * kinkScalar c ^ (2 * (w : ℤ) - 2)) *
          pairQFormula u ((c : ℤ) + 1) := by ring
    _ = pairQFormula u ((c : ℤ) + 1) := by rw [h1, h2, one_mul, one_mul]

/-- `J_K(0) = 0` for every braid knot. -/
theorem pairQ_coloredJones_zero (K : BraidKnot) : coloredJones K 0 = 0 := by
  simp only [coloredJones, lt_irrefl, ite_false]

/-- `J_K(-n) = -J_K(n)` for every braid knot. -/
theorem pairQ_coloredJones_neg (K : BraidKnot) (n : ℤ) :
    coloredJones K (-n) = -coloredJones K n := by
  unfold coloredJones
  rcases lt_trichotomy 0 n with hn | hn | hn
  · have h1 : ¬ (0 : ℤ) < -n := by omega
    have h2 : -n < 0 := by omega
    simp only [h1, h2, hn, ite_true, ite_false, neg_neg]
  · subst hn
    simp only [neg_zero, lt_irrefl, ite_false]
  · have h1 : (0 : ℤ) < -n := by omega
    have h2 : ¬ (0 : ℤ) < n := by omega
    simp only [h1, h2, hn, ite_true, ite_false, neg_neg]

end AJConjecture
