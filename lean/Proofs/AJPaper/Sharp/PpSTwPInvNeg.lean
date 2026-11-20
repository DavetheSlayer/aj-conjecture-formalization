import Mathlib
import AJTwist.Quantum.TwQTwistPolyNeg
import AJPaper.Sharp.PpSTwPInvPos

/-!
# The polynomials `C_b` under simultaneous inversion (Unit PpS, node `PpS_TwPInvNeg`)

The companion of `pps_twistPoly_inv` for the filling polynomials of negative index:

`C_b(M, L) = M^(8b-2) L^(2b-1) C_b(M⁻¹, L⁻¹)` for `b ≥ 1`   (`pps_twistPolyNeg_inv`).

Proof route: induction along the recurrence of `AJTwist.Quantum.TwQTwistPolyNeg`:
`C_1 = L + M⁶` (`twistPolyNeg_one`), `C_2 = Ẑ C_1 - M⁴ (M² + L)³` (`twistPolyNeg_two`),
`C_(k+3) = Ẑ C_(k+2) - M⁴ (M² + L)⁴ C_(k+1)` (`twistPolyNeg_add_three`), with
`pps_zetaMoebiusM_inv`, `pps_twistWeight_inv` and
`M⁴ (M² + L)³ = M¹⁴ L³ · (M⁴ (M² + L)³)(M⁻¹, L⁻¹)`.

Checked symbolically for `b ≤ 4` (`SCR/S/py/s01_sym.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The image of `M` in the comparison ring. -/
private theorem toComparison_C_X_ppsTwPInvNeg :
    toComparison (C X) = LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) := by
  simp [toComparison]

/-- The image of `L` in the comparison ring. -/
private theorem toComparison_X_ppsTwPInvNeg : toComparison X = LaurentPolynomial.T 1 := by
  simp [toComparison]

/-- `M · M⁻¹ = 1` in the comparison ring. -/
private theorem C_X_mul_C_inv_ppsTwPInvNeg :
    (LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) : ComparisonRing) *
      LaurentPolynomial.C (RatFunc.X : RatFunc ℚ)⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ RatFunc.X_ne_zero, map_one]

/-- `L · L⁻¹ = 1` in the comparison ring. -/
private theorem T_one_mul_T_neg_one_ppsTwPInvNeg :
    (LaurentPolynomial.T 1 : ComparisonRing) * LaurentPolynomial.T (-1) = 1 := by
  rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

/-- `L^n` in the comparison ring. -/
private theorem T_natCast_ppsTwPInvNeg (n : ℕ) :
    (LaurentPolynomial.T (n : ℤ) : ComparisonRing) = LaurentPolynomial.T 1 ^ n := by
  rw [LaurentPolynomial.T_pow, mul_one]

/-- `x² (x + l)³ = x⁷ l³ · x⁻² (x⁻¹ + l⁻¹)³` in a commutative ring (`x = M²`). -/
private theorem weightThree_inv_identity_ppsTwPInvNeg {R : Type*} [CommRing R] (x xi l li : R)
    (hx : x * xi = 1) (hl : l * li = 1) :
    x ^ 2 * (x + l) ^ 3 = x ^ 7 * l ^ 3 * (xi ^ 2 * (xi + li) ^ 3) := by
  rw [show x ^ 7 * l ^ 3 * (xi ^ 2 * (xi + li) ^ 3) =
    x ^ 2 * (x * xi) ^ 2 * (x * xi * l + x * (l * li)) ^ 3 by ring, hx, hl]
  ring

/-- `C_1(m, l) = m⁶ l C_1(m⁻¹, l⁻¹)` in a commutative ring. -/
private theorem negOne_inv_identity_ppsTwPInvNeg {R : Type*} [CommRing R] (m mi l li : R)
    (hm : m * mi = 1) (hl : l * li = 1) : l + m ^ 6 = m ^ 6 * l * (li + mi ^ 6) := by
  rw [show m ^ 6 * l * (li + mi ^ 6) = m ^ 6 * (l * li) + (m * mi) ^ 6 * l by ring, hm, hl]
  ring

/-- The symmetry of `C_1`. -/
private theorem twistPolyNeg_one_inv_ppsTwPInvNeg :
    toComparison (twistPolyNeg 1) =
      LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) ^ 6 * LaurentPolynomial.T 1 *
        LaurentPolynomial.invert (ppsMInv (toComparison (twistPolyNeg 1))) := by
  have key := negOne_inv_identity_ppsTwPInvNeg _ _ _ _ C_X_mul_C_inv_ppsTwPInvNeg
    T_one_mul_T_neg_one_ppsTwPInvNeg
  rw [twistPolyNeg_one]
  simp only [map_add, map_pow, toComparison_C_X_ppsTwPInvNeg, toComparison_X_ppsTwPInvNeg,
    ppsMInv_C, ppsMInv_T, twQBar_X, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
  exact key

/-- The weight of the first step: `M⁴ (M² + L)³ = M¹⁴ L³ · (M⁴ (M² + L)³)(M⁻¹, L⁻¹)`. -/
private theorem twistWeightThree_inv_ppsTwPInvNeg :
    toComparison (C (X ^ 4) * (C (X ^ 2) + X) ^ 3) =
      LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) ^ 14 * LaurentPolynomial.T 1 ^ 3 *
        LaurentPolynomial.invert
          (ppsMInv (toComparison (C (X ^ 4) * (C (X ^ 2) + X) ^ 3))) := by
  have hm := C_X_mul_C_inv_ppsTwPInvNeg
  have key := weightThree_inv_identity_ppsTwPInvNeg _ _ _ _
    (show (LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) : ComparisonRing) ^ 2 *
      LaurentPolynomial.C (RatFunc.X : RatFunc ℚ)⁻¹ ^ 2 = 1 by rw [← mul_pow, hm, one_pow])
    T_one_mul_T_neg_one_ppsTwPInvNeg
  simp only [map_add, map_mul, map_pow, toComparison_C_X_ppsTwPInvNeg,
    toComparison_X_ppsTwPInvNeg, ppsMInv_C, ppsMInv_T, twQBar_X, LaurentPolynomial.invert_C,
    LaurentPolynomial.invert_T]
  linear_combination key

/-- The symmetry of `C_(n+1)` with the exponents `8n + 6` and `2n + 1`. -/
private theorem twistPolyNeg_succ_inv_ppsTwPInvNeg (n : ℕ) :
    toComparison (twistPolyNeg (n + 1)) =
      LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) ^ (8 * n + 6) *
          LaurentPolynomial.T 1 ^ (2 * n + 1) *
        LaurentPolynomial.invert (ppsMInv (toComparison (twistPolyNeg (n + 1)))) := by
  have hC : ∀ n : ℕ, LaurentPolynomial.C ((RatFunc.X : RatFunc ℚ) ^ n) =
      (LaurentPolynomial.C RatFunc.X : ComparisonRing) ^ n := fun n ↦ map_pow _ _ _
  have hZ := pps_zetaMoebiusM_inv
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, T_natCast_ppsTwPInvNeg, hC] at hZ
  induction n using Nat.twoStepInduction with
  | zero =>
    have h := twistPolyNeg_one_inv_ppsTwPInvNeg
    linear_combination h
  | one =>
    have h1 := twistPolyNeg_one_inv_ppsTwPInvNeg
    have hW := twistWeightThree_inv_ppsTwPInvNeg
    rw [show twistPolyNeg (1 + 1) = twistPolyNeg 2 from rfl, twistPolyNeg_two]
    generalize (C (X ^ 4) * (C (X ^ 2) + X) ^ 3 : ℤ[X][X]) = W at hW ⊢
    simp only [map_sub, map_mul]
    linear_combination (toComparison (twistPolyNeg 1)) * hZ +
      (LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) ^ 8 * LaurentPolynomial.T 1 ^ 2 *
        LaurentPolynomial.invert (ppsMInv (toComparison zetaMoebiusM))) * h1 - hW
  | more n ih0 ih1 =>
    have hrec : twistPolyNeg (n + 2 + 1) = zetaMoebiusM * twistPolyNeg (n + 1 + 1) -
        C (X ^ 4) * (C (X ^ 2) + X) ^ 4 * twistPolyNeg (n + 1) := twistPolyNeg_add_three n
    have hW := pps_twistWeight_inv
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, T_natCast_ppsTwPInvNeg, hC] at hW
    rw [hrec]
    generalize (C (X ^ 4) * (C (X ^ 2) + X) ^ 4 : ℤ[X][X]) = W at hW ⊢
    simp only [map_sub, map_mul]
    linear_combination (toComparison (twistPolyNeg (n + 1 + 1))) * hZ +
      (LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) ^ 8 * LaurentPolynomial.T 1 ^ 2 *
        LaurentPolynomial.invert (ppsMInv (toComparison zetaMoebiusM))) * ih1 -
      (toComparison (twistPolyNeg (n + 1))) * hW -
      (LaurentPolynomial.C (RatFunc.X : RatFunc ℚ) ^ 16 * LaurentPolynomial.T 1 ^ 4 *
        LaurentPolynomial.invert (ppsMInv (toComparison W))) * ih0

/-- **Inversion symmetry of `C_b`**: `C_b(M, L) = M^(8b-2) L^(2b-1) C_b(M⁻¹, L⁻¹)` in
`ℚ(M)[L, L⁻¹]`, for `b ≥ 1`. -/
theorem pps_twistPolyNeg_inv (b : ℕ) (hb : 1 ≤ b) :
    toComparison (twistPolyNeg b) =
      LaurentPolynomial.C ((RatFunc.X : RatFunc ℚ) ^ (8 * b - 2)) *
          LaurentPolynomial.T ((2 * b - 1 : ℕ) : ℤ) *
        LaurentPolynomial.invert (ppsMInv (toComparison (twistPolyNeg b))) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = n + 1 := ⟨b - 1, by omega⟩
  rw [show 8 * (n + 1) - 2 = 8 * n + 6 by omega, show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
    T_natCast_ppsTwPInvNeg, map_pow]
  exact twistPolyNeg_succ_inv_ppsTwPInvNeg n

end AJConjecture
