import Mathlib
import AJConjecture.SkeinTlRelations

/-!
# Relations between crossings

The second and third Reidemeister moves for single strands: `σ_i σ_i⁻¹ = 1`,
`σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1}`, and far commutation. With `σ_i^{±1} = t^{±1} + t^{∓1} e_i`
they are consequences of the Temperley–Lieb relations (`1 + (t² + t⁻² + δ) e = 1`).
-/

namespace AJConjecture

/-- The product of two Kauffman expansions `a + b e`, `c + d e` when `e² = δ e`. -/
private theorem kauffman_mul_crossingRel {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (e : A) (δ a b c d : R) (he : e * e = δ • e) :
    (a • (1 : A) + b • e) * (c • (1 : A) + d • e) =
      (a * c) • (1 : A) + (a * d + b * c + b * d * δ) • e := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, he, smul_smul]
  module

/-- The braid relation for the Kauffman expansions `a + b e`, `a + b f` of two generators with
the Temperley–Lieb relations, when `a² + a b δ + b² = 0`. -/
private theorem kauffman_braid_crossingRel {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (e f : A) (δ a b : R) (he : e * e = δ • e) (hf : f * f = δ • f) (hefe : e * f * e = e)
    (hfef : f * e * f = f) (hab : a * a + a * b * δ + b * b = 0) :
    (a • (1 : A) + b • e) * (a • (1 : A) + b • f) * (a • (1 : A) + b • e) =
      (a • (1 : A) + b • f) * (a • (1 : A) + b • e) * (a • (1 : A) + b • f) := by
  have key : (a • (1 : A) + b • e) * (a • (1 : A) + b • f) * (a • (1 : A) + b • e) -
      (a • (1 : A) + b • f) * (a • (1 : A) + b • e) * (a • (1 : A) + b • f) =
      (b * (a * a + a * b * δ + b * b)) • (e - f) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, he, hf, hefe,
      hfef, smul_smul]
    module
  rw [hab, mul_zero, zero_smul] at key
  exact sub_eq_zero.mp key

/-- The product of two Kauffman expansions on the same pair of strands. -/
private theorem smul_one_add_smul_tlGenF_mul_crossingRel (m i : ℕ) (a b c d : RatFunc ℚ) :
    (a • (1 : SkMat m m) + b • tlGenF m i) * (c • (1 : SkMat m m) + d • tlGenF m i) =
      (a * c) • (1 : SkMat m m) +
        (a * d + b * c + b * d * (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))) •
          tlGenF m i :=
  kauffman_mul_crossingRel (tlGenF m i) _ a b c d (tlGenF_mul_self m i)

/-- The scalar identities behind `σ σ⁻¹ = 1`. -/
private theorem kauffman_scalar_crossingRel :
    (RatFunc.X : RatFunc ℚ) * RatFunc.X + RatFunc.X⁻¹ * RatFunc.X⁻¹ +
      RatFunc.X⁻¹ * RatFunc.X * (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) =
        0 := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  simp only [zpow_neg, zpow_ofNat]
  field_simp
  ring

/-- `σ_i σ_i⁻¹ = 1` (for every `i`, also when `e_i = 0`). -/
theorem crossingF_mul_inv (m i : ℕ) : crossingF m (i, true) * crossingF m (i, false) = 1 := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h0 := kauffman_scalar_crossingRel
  rw [crossingF_pos, crossingF_neg, smul_one_add_smul_tlGenF_mul_crossingRel,
    mul_inv_cancel₀ hX, h0, one_smul, zero_smul, add_zero]

/-- `σ_i⁻¹ σ_i = 1`. -/
theorem crossingF_inv_mul (m i : ℕ) : crossingF m (i, false) * crossingF m (i, true) = 1 := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h0 : (RatFunc.X : RatFunc ℚ)⁻¹ * RatFunc.X⁻¹ + RatFunc.X * RatFunc.X +
      RatFunc.X * RatFunc.X⁻¹ * (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) =
        0 := by
    linear_combination kauffman_scalar_crossingRel
  rw [crossingF_neg, crossingF_pos, smul_one_add_smul_tlGenF_mul_crossingRel,
    inv_mul_cancel₀ hX, h0, one_smul, zero_smul, add_zero]

/-- The braid relation for two Kauffman expansions with coefficients `a`, `b` such that
`a² + a b δ + b² = 0`. -/
private theorem braid_of_tl_crossingRel (m i : ℕ) (h : i + 2 < m) (a b : RatFunc ℚ)
    (hab : a * a + a * b * (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) +
      b * b = 0) :
    (a • (1 : SkMat m m) + b • tlGenF m i) * (a • (1 : SkMat m m) + b • tlGenF m (i + 1)) *
        (a • (1 : SkMat m m) + b • tlGenF m i) =
      (a • (1 : SkMat m m) + b • tlGenF m (i + 1)) * (a • (1 : SkMat m m) + b • tlGenF m i) *
        (a • (1 : SkMat m m) + b • tlGenF m (i + 1)) :=
  kauffman_braid_crossingRel (tlGenF m i) (tlGenF m (i + 1)) _ a b (tlGenF_mul_self m i)
    (tlGenF_mul_self m (i + 1)) (tlGenF_mul_succ_mul m i h) (tlGenF_succ_mul_mul m i) hab

/-- The braid relation, for crossings of the same sign. -/
theorem crossingF_braid (m i : ℕ) (s : Bool) (h : i + 2 < m) :
    crossingF m (i, s) * crossingF m (i + 1, s) * crossingF m (i, s) =
      crossingF m (i + 1, s) * crossingF m (i, s) * crossingF m (i + 1, s) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  cases s
  · rw [crossingF_neg, crossingF_neg]
    refine braid_of_tl_crossingRel m i h _ _ ?_
    simp only [zpow_neg, zpow_ofNat]
    field_simp
    ring
  · rw [crossingF_pos, crossingF_pos]
    refine braid_of_tl_crossingRel m i h _ _ ?_
    simp only [zpow_neg, zpow_ofNat]
    field_simp
    ring

/-- Kauffman expansions on disjoint pairs of strands commute. -/
private theorem commute_smul_one_add_smul_tlGenF_crossingRel (m i j : ℕ) (h : i + 1 < j)
    (a b c d : RatFunc ℚ) :
    Commute (a • (1 : SkMat m m) + b • tlGenF m i) (c • (1 : SkMat m m) + d • tlGenF m j) := by
  have hc := tlGenF_commute m i j h
  have h1 : Commute (a • (1 : SkMat m m)) (c • (1 : SkMat m m) + d • tlGenF m j) :=
    (Commute.one_left _).smul_left a
  have h2 : Commute (b • tlGenF m i) (c • (1 : SkMat m m) + d • tlGenF m j) :=
    (((Commute.one_right _).smul_right c).add_right (hc.smul_right d)).smul_left b
  exact h1.add_left h2

/-- Crossings on disjoint pairs of strands commute. -/
theorem crossingF_commute (m i j : ℕ) (s s' : Bool) (h : i + 1 < j) :
    Commute (crossingF m (i, s)) (crossingF m (j, s')) := by
  cases s <;> cases s' <;>
    simp only [crossingF_pos, crossingF_neg] <;>
    exact commute_smul_one_add_smul_tlGenF_crossingRel m i j h _ _ _ _

end AJConjecture
