import Mathlib
import AJTwist.Knot.TwKSourceOp

/-!
# From the twists `ℓ ≤ 0` to all twists by the Cayley–Hamilton theorem

Let `M` be an invertible matrix over a field and `L₁, L₂` two linear maps on matrices. If
`L₁ (M ^ n) = L₂ (M ^ n)` for every `n : ℕ`, then also for every `n : ℤ`: by the Cayley–Hamilton
theorem `M⁻¹` is a polynomial in `M`, hence so is every negative power
(`map_zpow_eq_of_forall_pow`). With `M = (halfTwist c false) ^ 2` (the cabled negative full
twist), `L₁ = twSrcOp r s σ c` and `L₂ Y = ptrTail (Λ_C · (Y · Σ^{-2(r-1)s} · clasp_σ))`, the
band-and-clasp identity for the twists `ℓ = -n ≤ 0`, which is what the Morse isotopy proves with
negative full twists only (the beads `t` of the library), gives the identity for every `ℓ ∈ ℤ`.
No knot theory is used in this file.
-/

noncomputable section

namespace AJConjecture

/-- The inverse of an invertible matrix over a field is a polynomial in the matrix
(Cayley–Hamilton). -/
private theorem exists_aeval_eq_inv_twKCayley {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι F) (hM : IsUnit M.det) :
    ∃ q : Polynomial F, M⁻¹ = Polynomial.aeval M q := by
  have hc : M.charpoly.coeff 0 ≠ 0 := by
    intro h0
    have hdet := M.det_eq_sign_charpoly_coeff
    rw [h0, mul_zero] at hdet
    exact hM.ne_zero hdet
  have hCH := M.aeval_self_charpoly
  rw [← Polynomial.divX_mul_X_add M.charpoly, map_add, map_mul, Polynomial.aeval_X,
    Polynomial.aeval_C] at hCH
  refine ⟨Polynomial.C (-(M.charpoly.coeff 0)⁻¹) * M.charpoly.divX, Matrix.inv_eq_left_inv ?_⟩
  rw [map_mul, Polynomial.aeval_C, mul_assoc, eq_neg_of_add_eq_zero_left hCH, ← map_neg,
    ← map_mul, neg_mul_neg, inv_mul_cancel₀ hc, map_one]

/-- Two linear maps that agree on the natural powers of a matrix agree on the polynomials in
it. -/
private theorem map_aeval_eq_of_forall_pow_twKCayley {F : Type*} [Field F] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {V : Type*} [AddCommGroup V] [Module F V]
    (L₁ L₂ : Matrix ι ι F →ₗ[F] V) (M : Matrix ι ι F) (h : ∀ n : ℕ, L₁ (M ^ n) = L₂ (M ^ n))
    (p : Polynomial F) : L₁ (Polynomial.aeval M p) = L₂ (Polynomial.aeval M p) := by
  rw [Polynomial.aeval_eq_sum_range, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, map_smul, h]

/-- Two linear maps that agree on the natural powers of an invertible matrix agree on its
integer powers. -/
theorem map_zpow_eq_of_forall_pow {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module F V] (L₁ L₂ : Matrix ι ι F →ₗ[F] V) (M : Matrix ι ι F)
    (hM : IsUnit M.det) (h : ∀ n : ℕ, L₁ (M ^ n) = L₂ (M ^ n)) (z : ℤ) :
    L₁ (M ^ z) = L₂ (M ^ z) := by
  obtain ⟨q, hq⟩ := exists_aeval_eq_inv_twKCayley M hM
  rcases z with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact h n
  · rw [zpow_negSucc, ← Matrix.inv_pow', hq, ← map_pow]
    exact map_aeval_eq_of_forall_pow_twKCayley L₁ L₂ M h _

/-- The cabled half twists of opposite signs are inverse to each other. -/
theorem halfTwist_mul_halfTwist_not (c : ℕ) (s : Bool) :
    halfTwist c s * halfTwist c (!s) = 1 := by
  rw [halfTwist, halfTwist, cableGen_eq_thickCross, cableGen_eq_thickCross]
  cases s
  · exact braidMatrix_thickGen_inv_mul (2 * c) c c (c * 0)
  · exact braidMatrix_thickGen_mul_inv (2 * c) c c (c * 0)

/-- The positive full twist is the right inverse of the negative full twist. -/
private theorem halfTwist_false_sq_mul_true_sq_twKCayley (c : ℕ) :
    halfTwist c false ^ 2 * halfTwist c true ^ 2 = 1 := by
  have h1 : halfTwist c false * halfTwist c true = 1 := halfTwist_mul_halfTwist_not c false
  rw [pow_two, pow_two, mul_assoc, ← mul_assoc (halfTwist c false) (halfTwist c true), h1,
    one_mul, h1]

/-- The even cabled half twists are the integer powers of the negative full twist. -/
theorem halfTwistZ_two_mul (c : ℕ) (ℓ : ℤ) :
    halfTwistZ c (2 * ℓ) = (halfTwist c false ^ 2) ^ (-ℓ) := by
  rcases le_or_gt 0 ℓ with hl | hl
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hl
    rw [halfTwistZ, ite_eq_left (by omega), show (2 * (n : ℤ)).toNat = 2 * n by omega,
      Matrix.zpow_neg_natCast, ← Matrix.inv_pow',
      Matrix.inv_eq_right_inv (halfTwist_false_sq_mul_true_sq_twKCayley c), pow_mul]
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = -ℓ := ⟨(-ℓ).toNat, Int.toNat_of_nonneg (by omega)⟩
    rw [halfTwistZ, ite_eq_right (by omega), show (-(2 * ℓ)).toNat = 2 * n by omega, ← hn,
      zpow_natCast, pow_mul]

/-- The band-and-clasp identity for the half line `ℓ = -n ≤ 0` implies it for every twist. -/
theorem twSrcOp_eq_of_halfLine {r s : ℕ} (h : IsTorusPair r s) (σ : Bool) (c : ℕ)
    (hl : ∀ n : ℕ, twSrcOp r s σ c (halfTwistZ c (-(2 * (n : ℤ)))) =
      ptrTail c (2 * c) (longKnotOp (torusPairKnot r s h) (2 * c) *
        (halfTwistZ c (-(2 * (n : ℤ)) - 2 * (((r - 1) * s : ℕ) : ℤ)) * claspSOp c σ)))
    (ℓ : ℤ) :
    twSrcOp r s σ c (halfTwistZ c (2 * ℓ)) =
      ptrTail c (2 * c) (longKnotOp (torusPairKnot r s h) (2 * c) *
        (halfTwistZ c (2 * ℓ - 2 * (((r - 1) * s : ℕ) : ℤ)) * claspSOp c σ)) := by
  have hU : IsUnit (halfTwist c false ^ 2).det :=
    Matrix.isUnit_det_of_right_inverse (halfTwist_false_sq_mul_true_sq_twKCayley c)
  have hsplit : ∀ z : ℤ, halfTwistZ c (2 * z - 2 * (((r - 1) * s : ℕ) : ℤ)) =
      (halfTwist c false ^ 2) ^ (-z) * (halfTwist c false ^ 2) ^ ((r - 1) * s) := by
    intro z
    rw [← mul_sub, halfTwistZ_two_mul, neg_sub, sub_eq_add_neg, add_comm,
      Matrix.zpow_add hU, zpow_natCast]
  let L₁ : SkMat (2 * c) (2 * c) →ₗ[RatFunc ℚ] SkMat c c :=
    { toFun := twSrcOp r s σ c
      map_add' := twSrcOp_add r s σ c
      map_smul' := twSrcOp_smul r s σ c }
  let L₂ : SkMat (2 * c) (2 * c) →ₗ[RatFunc ℚ] SkMat c c :=
    { toFun := fun Y ↦ ptrTail c (2 * c) (longKnotOp (torusPairKnot r s h) (2 * c) *
        (Y * (halfTwist c false ^ 2) ^ ((r - 1) * s) * claspSOp c σ))
      map_add' := fun Y Z ↦ by
        simp only [Matrix.add_mul, Matrix.mul_add, ptrTail_add]
      map_smul' := fun a Y ↦ by
        simp only [Matrix.smul_mul, Matrix.mul_smul, ptrTail_smul, RingHom.id_apply] }
  have hagree : ∀ n : ℕ, L₁ ((halfTwist c false ^ 2) ^ n) = L₂ ((halfTwist c false ^ 2) ^ n) := by
    intro n
    have h1 := hl n
    have h2 := halfTwistZ_two_mul c (-(n : ℤ))
    have h3 := hsplit (-(n : ℤ))
    rw [neg_neg, zpow_natCast] at h2 h3
    rw [mul_neg] at h2 h3
    rw [h2, h3] at h1
    exact h1
  have key := map_zpow_eq_of_forall_pow L₁ L₂ _ hU hagree (-ℓ)
  rw [halfTwistZ_two_mul, hsplit]
  exact key

end AJConjecture
