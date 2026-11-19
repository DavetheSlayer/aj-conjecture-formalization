import Mathlib
import AJFamily.Quantum.TwistPolyBasic
import AJPaper.Sharp.PpSMInv

/-!
# The twist polynomials `B_k` under simultaneous inversion (Unit PpS, node `PpS_TwPInvPos`)

Source: Section 8.2 and Section 8.4 of the paper (`conclusion.tex`): the mirror image inverts
the meridian, `f_{S^*}(M, L) ≐ f_S(M⁻¹, L)`, and "the corresponding factor … is
`𝒫_ℓ(M⁻¹, L)` up to a unit in `R`". The library states the classical bound of the positive clasp
with `L` inverted (`Polynomial.reverse`). The two agree because the filling polynomials are
invariant under `(M, L) ↦ (M⁻¹, L⁻¹)` up to a monomial:

`B_k(M, L) = M^(8k) L^(2k) B_k(M⁻¹, L⁻¹)`   (`pps_twistPoly_inv`).

Proof route: induction along the defining recursion
`B_(k+2) = Ẑ B_(k+1) - M⁴ (M² + L)⁴ B_k`, with
`Ẑ(M, L) = M⁸ L² Ẑ(M⁻¹, L⁻¹)` (`pps_zetaMoebiusM_inv`, from `zetaMoebiusM_eq_explicit`) and
`M⁴ (M² + L)⁴ = M¹⁶ L⁴ · M⁻⁴ (M⁻² + L⁻¹)⁴`; base cases `B_0 = 1` and `B_1`
(`twistPoly_one_eq_explicit`). All identities are in `R = ℚ(M)[L, L⁻¹]`, where `M` and `L` are
units (`LaurentPolynomial.C RatFunc.X`, `LaurentPolynomial.T 1`).

Checked symbolically for `k ≤ 4` (`SCR/S/py/s01_sym.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The image of `M` in the comparison ring. -/
private theorem toComparison_C_X_ppsTwPInvPos :
    toComparison (C X) = LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) := by
  simp [toComparison]

/-- The image of `L` in the comparison ring. -/
private theorem toComparison_X_ppsTwPInvPos : toComparison X = LaurentPolynomial.T 1 := by
  simp [toComparison]

/-- `M · M⁻¹ = 1` in the comparison ring. -/
private theorem C_X_mul_C_inv_ppsTwPInvPos :
    (LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) : ComparisonRing) *
      LaurentPolynomial.C (RatFunc.X : RatFunc ℚ)⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ RatFunc.X_ne_zero, map_one]

/-- `L · L⁻¹ = 1` in the comparison ring. -/
private theorem T_one_mul_T_neg_one_ppsTwPInvPos :
    (LaurentPolynomial.T 1 : ComparisonRing) * LaurentPolynomial.T (-1) = 1 := by
  rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

/-- `L^n` in the comparison ring. -/
private theorem T_natCast_ppsTwPInvPos (n : ℕ) :
    (LaurentPolynomial.T (n : ℤ) : ComparisonRing) = LaurentPolynomial.T 1 ^ n := by
  rw [LaurentPolynomial.T_pow, mul_one]

/-- `Ẑ(x, l) = x⁴ l² Ẑ(x⁻¹, l⁻¹)` in a commutative ring (`x = M²`). -/
private theorem zeta_inv_identity_ppsTwPInvPos {R : Type*} [CommRing R] (x xi l li : R)
    (hx : x * xi = 1) (hl : l * li = 1) :
    (x ^ 2 + 1) * l ^ 2 - (x ^ 4 - 2 * x ^ 3 - 2 * x ^ 2 - 2 * x + 1) * l + x ^ 2 * (x ^ 2 + 1) =
      x ^ 4 * l ^ 2 * ((xi ^ 2 + 1) * li ^ 2 -
        (xi ^ 4 - 2 * xi ^ 3 - 2 * xi ^ 2 - 2 * xi + 1) * li + xi ^ 2 * (xi ^ 2 + 1)) := by
  have h : x ^ 4 * l ^ 2 * ((xi ^ 2 + 1) * li ^ 2 -
      (xi ^ 4 - 2 * xi ^ 3 - 2 * xi ^ 2 - 2 * xi + 1) * li + xi ^ 2 * (xi ^ 2 + 1)) =
      (x ^ 2 * (x * xi) ^ 2 + x ^ 4) * (l * li) ^ 2 -
        ((x * xi) ^ 4 - 2 * x * (x * xi) ^ 3 - 2 * x ^ 2 * (x * xi) ^ 2 - 2 * x ^ 3 * (x * xi) +
          x ^ 4) * l * (l * li) + ((x * xi) ^ 4 + x ^ 2 * (x * xi) ^ 2) * l ^ 2 := by
    ring
  rw [h, hx, hl]
  ring

/-- `B_1(x, l) = x⁴ l² B_1(x⁻¹, l⁻¹)` in a commutative ring (`x = M²`). -/
private theorem twistOne_inv_identity_ppsTwPInvPos {R : Type*} [CommRing R] (x xi l li : R)
    (hx : x * xi = 1) (hl : l * li = 1) :
    x ^ 2 * l ^ 2 + (-x ^ 4 + x ^ 3 + 2 * x ^ 2 + x - 1) * l + x ^ 2 =
      x ^ 4 * l ^ 2 * (xi ^ 2 * li ^ 2 + (-xi ^ 4 + xi ^ 3 + 2 * xi ^ 2 + xi - 1) * li +
        xi ^ 2) := by
  have h : x ^ 4 * l ^ 2 * (xi ^ 2 * li ^ 2 + (-xi ^ 4 + xi ^ 3 + 2 * xi ^ 2 + xi - 1) * li +
      xi ^ 2) =
      x ^ 2 * (x * xi) ^ 2 * (l * li) ^ 2 +
        (-(x * xi) ^ 4 + x * (x * xi) ^ 3 + 2 * x ^ 2 * (x * xi) ^ 2 + x ^ 3 * (x * xi) -
          x ^ 4) * l * (l * li) + x ^ 2 * (x * xi) ^ 2 * l ^ 2 := by
    ring
  rw [h, hx, hl]
  ring

/-- `x² (x + l)^n = x^(n+4) l^n · x⁻² (x⁻¹ + l⁻¹)^n` in a commutative ring (`x = M²`). -/
private theorem weight_inv_identity_ppsTwPInvPos {R : Type*} [CommRing R] (x xi l li : R)
    (hx : x * xi = 1) (hl : l * li = 1) (n : ℕ) :
    x ^ 2 * (x + l) ^ n = x ^ (n + 4) * l ^ n * (xi ^ 2 * (xi + li) ^ n) := by
  have h : x ^ (n + 4) * l ^ n * (xi ^ 2 * (xi + li) ^ n) =
      x ^ 2 * (x * xi) ^ 2 * (x * xi * l + x * (l * li)) ^ n := by
    rw [show x * xi * l + x * (l * li) = x * l * (xi + li) by ring, mul_pow, mul_pow]
    ring
  rw [h, hx, hl]
  ring

/-- `Ẑ(M, L) = M⁸ L² Ẑ(M⁻¹, L⁻¹)` in `ℚ(M)[L, L⁻¹]`. -/
theorem pps_zetaMoebiusM_inv :
    toComparison zetaMoebiusM =
      LaurentPolynomial.C ((RatFunc.X : RatFunc ℚ) ^ 8) * LaurentPolynomial.T 2 *
        LaurentPolynomial.invert (ppsMInv (toComparison zetaMoebiusM)) := by
  have hm := C_X_mul_C_inv_ppsTwPInvPos
  have key := zeta_inv_identity_ppsTwPInvPos _ _ _ _
    (show (LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) : ComparisonRing) ^ 2 *
      LaurentPolynomial.C (RatFunc.X : RatFunc ℚ)⁻¹ ^ 2 = 1 by rw [← mul_pow, hm, one_pow])
    T_one_mul_T_neg_one_ppsTwPInvPos
  rw [zetaMoebiusM_eq_explicit, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, T_natCast_ppsTwPInvPos]
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, toComparison_C_X_ppsTwPInvPos,
    toComparison_X_ppsTwPInvPos, ppsMInv_C, ppsMInv_T, twQBar_X, LaurentPolynomial.invert_C,
    LaurentPolynomial.invert_T]
  linear_combination key

/-- The recursion weight: `M⁴ (M² + L)⁴ = M¹⁶ L⁴ · (M⁴ (M² + L)⁴)(M⁻¹, L⁻¹)`. -/
theorem pps_twistWeight_inv :
    toComparison (C (X ^ 4) * (C (X ^ 2) + X) ^ 4) =
      LaurentPolynomial.C ((RatFunc.X : RatFunc ℚ) ^ 16) * LaurentPolynomial.T 4 *
        LaurentPolynomial.invert
          (ppsMInv (toComparison (C (X ^ 4) * (C (X ^ 2) + X) ^ 4))) := by
  have hm := C_X_mul_C_inv_ppsTwPInvPos
  have key := weight_inv_identity_ppsTwPInvPos _ _ _ _
    (show (LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) : ComparisonRing) ^ 2 *
      LaurentPolynomial.C (RatFunc.X : RatFunc ℚ)⁻¹ ^ 2 = 1 by rw [← mul_pow, hm, one_pow])
    T_one_mul_T_neg_one_ppsTwPInvPos 4
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, T_natCast_ppsTwPInvPos]
  simp only [map_add, map_mul, map_pow, toComparison_C_X_ppsTwPInvPos,
    toComparison_X_ppsTwPInvPos, ppsMInv_C, ppsMInv_T, twQBar_X, LaurentPolynomial.invert_C,
    LaurentPolynomial.invert_T]
  linear_combination key

/-- **Inversion symmetry of `B_k`**: `B_k(M, L) = M^(8k) L^(2k) B_k(M⁻¹, L⁻¹)` in
`ℚ(M)[L, L⁻¹]`. -/
theorem pps_twistPoly_inv (k : ℕ) :
    toComparison (twistPoly k) =
      LaurentPolynomial.C ((RatFunc.X : RatFunc ℚ) ^ (8 * k)) *
          LaurentPolynomial.T ((2 * k : ℕ) : ℤ) *
        LaurentPolynomial.invert (ppsMInv (toComparison (twistPoly k))) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [twistPoly]
  | one =>
    have hm := C_X_mul_C_inv_ppsTwPInvPos
    have key := twistOne_inv_identity_ppsTwPInvPos _ _ _ _
      (show (LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) : ComparisonRing) ^ 2 *
        LaurentPolynomial.C (RatFunc.X : RatFunc ℚ)⁻¹ ^ 2 = 1 by rw [← mul_pow, hm, one_pow])
      T_one_mul_T_neg_one_ppsTwPInvPos
    rw [twistPoly_one_eq_explicit, T_natCast_ppsTwPInvPos]
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_neg,
      toComparison_C_X_ppsTwPInvPos, toComparison_X_ppsTwPInvPos, ppsMInv_C, ppsMInv_T, twQBar_X,
      LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
    linear_combination key
  | more k ih0 ih1 =>
    have hrec : twistPoly (k + 2) =
        zetaMoebiusM * twistPoly (k + 1) - C (X ^ 4) * (C (X ^ 2) + X) ^ 4 * twistPoly k := by
      rw [twistPoly]
    have hC : ∀ n : ℕ, LaurentPolynomial.C ((RatFunc.X : RatFunc ℚ) ^ n) =
        (LaurentPolynomial.C RatFunc.X : ComparisonRing) ^ n := fun n ↦ map_pow _ _ _
    have hZ := pps_zetaMoebiusM_inv
    have hW := pps_twistWeight_inv
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, T_natCast_ppsTwPInvPos, hC] at hZ
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, T_natCast_ppsTwPInvPos, hC] at hW
    rw [T_natCast_ppsTwPInvPos, hC] at ih0 ih1 ⊢
    rw [hrec]
    generalize (C (X ^ 4) * (C (X ^ 2) + X) ^ 4 : ℤ[X][X]) = W at hW ⊢
    simp only [map_sub, map_mul]
    linear_combination (toComparison (twistPoly (k + 1))) * hZ +
      (LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) ^ 8 * LaurentPolynomial.T 1 ^ 2 *
        LaurentPolynomial.invert (ppsMInv (toComparison zetaMoebiusM))) * ih1 -
      (toComparison (twistPoly k)) * hW -
      (LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) ^ 16 * LaurentPolynomial.T 1 ^ 4 *
        LaurentPolynomial.invert (ppsMInv (toComparison W))) * ih0

end AJConjecture
