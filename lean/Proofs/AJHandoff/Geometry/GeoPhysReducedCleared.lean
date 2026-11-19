import Mathlib
import AJConjecture.FieldActionBridge
import AJConjecture.QAlgQParamBasic
import AJHandoff.Geometry.GeoKernelFormula
import AJHandoff.Geometry.GeoPhysDefs

/-!
# The reduced formula with cleared denominators, evaluated at complex points (G-PHYS)

With `q = t⁴`, the clasp decomposition `[N] F_N = ∑_{n<N} claspAlgCoeff N n · u_n` and Zheng's
product form of the clasp coefficient give

  `(t^{2N} - t^{-2N}) F_N = ∑_{n<N} ∑_{i<N-n} t^{4N²-2N-2-4N(n+i)} Z_{n,i} Ĥ_n(t²)`,

`Z_{n,i} = ∏_{r=1}^{n} (1 - q^{i+r})(1 - q^{N-i-r})/(1 - q^r)`. Multiplying by
`D = ∏_{r=1}^{N-1} (1 - q^r)` turns this into an identity of Laurent polynomials, which can be
evaluated at every `t ∈ ℂˣ`; dividing by `D(t)` again gives the identity of complex numbers at
every `t ≠ 0` with `t^{4r} ≠ 1` for `1 ≤ r < N` (`geo_reduced_eval_identity`).
-/

open LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The Laurent polynomial
`Ĥ_n(t²) = t^{-8an(n+1)} ∑_k t^{4ak(2k+1)} (t^{2(4k+1)} - t^{-2(4k+1)})`. -/
def geoHatLaurent (a n : ℕ) : ℤ[T;T⁻¹] :=
  T (-(8 * (a : ℤ) * n * (n + 1))) *
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      T (4 * (a : ℤ) * k * (2 * k + 1)) * (T (2 * (4 * k + 1)) - T (-(2 * (4 * k + 1))))

/-- The common denominator `D = ∏_{r=1}^{N-1} (1 - t^{4r})`. -/
def geoClaspDenLaurent (N : ℕ) : ℤ[T;T⁻¹] :=
  ∏ r ∈ Finset.Icc 1 (N - 1), (1 - T (4 * (r : ℤ)))

/-- The numerator `D · Z_{n,i}` as a Laurent polynomial. -/
def geoClaspNumLaurent (N n i : ℕ) : ℤ[T;T⁻¹] :=
  (∏ r ∈ Finset.Icc 1 n,
      (1 - T (4 * ((i + r : ℕ) : ℤ))) * (1 - T (4 * ((N - i - r : ℕ) : ℤ)))) *
    ∏ r ∈ Finset.Ioc n (N - 1), (1 - T (4 * (r : ℤ)))

/-- Clearing the denominators of a product of quotients by `1 - y^r`. -/
theorem geo_prod_one_sub_pow_mul_prod_div {K : Type*} [Field K] (y : K) (A : ℕ → K) {n M : ℕ}
    (hnM : n ≤ M) (hy : ∀ r ∈ Finset.Icc 1 n, 1 - y ^ r ≠ 0) :
    (∏ r ∈ Finset.Icc 1 M, (1 - y ^ r)) * ∏ r ∈ Finset.Icc 1 n, (A r / (1 - y ^ r)) =
      (∏ r ∈ Finset.Icc 1 n, A r) * ∏ r ∈ Finset.Ioc n M, (1 - y ^ r) := by
  have hsplit : ∏ r ∈ Finset.Icc 1 M, (1 - y ^ r) =
      (∏ r ∈ Finset.Icc 1 n, (1 - y ^ r)) * ∏ r ∈ Finset.Ioc n M, (1 - y ^ r) := by
    rw [show Finset.Icc 1 M = Finset.Ioc 0 M from Finset.Icc_add_one_left_eq_Ioc 0 M,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_add_one_left_eq_Ioc 0 n,
      Finset.prod_Ioc_consecutive _ (Nat.zero_le n) hnM]
  have hne : ∏ r ∈ Finset.Icc 1 n, (1 - y ^ r) ≠ 0 := Finset.prod_ne_zero_iff.mpr hy
  rw [hsplit, Finset.prod_div_distrib]
  field_simp

/-- `t² - t⁻² ≠ 0` in `ℚ(t)`. -/
theorem geo_ratFuncX_sq_sub_inv_ne_zero :
    (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ) ≠ 0 := by
  intro h
  have h2 : (2 : ℤ) = -2 := ratFuncX_zpow_injective (sub_eq_zero.mp h)
  omega

/-- The Laurent form of `Ĥ_n` maps to `(t² - t⁻²) u_n`. -/
theorem laurentToField_geoHatLaurent (a n : ℕ) :
    laurentToField (geoHatLaurent a n) =
      ((RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) * torusOddColor a n := by
  have hne := geo_ratFuncX_sq_sub_inv_ne_zero
  simp only [geoHatLaurent, torusOddColor, quantumInt, map_mul, map_sum, map_sub,
    laurentToField_T, qParam_zpow_eq_ratFuncX_zpow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [show ∀ c d e f : RatFunc ℚ, c * (d * (e * (f / c))) = d * (e * (c * (f / c))) from
    fun c d e f ↦ by ring, mul_div_cancel₀ _ hne]
  ring_nf

/-- `1 - t^{4m}` maps to `1 - q^m`. -/
theorem laurentToField_one_sub_T_four_mul (m : ℕ) :
    laurentToField (1 - T (4 * (m : ℤ))) = 1 - qParam ^ m := by
  rw [map_sub, map_one, laurentToField_T, ← zpow_natCast qParam, qParam_zpow_eq_ratFuncX_zpow]

/-- The numerator Laurent polynomial is `D · Z_{n,i}` in `ℚ(t)`. -/
theorem laurentToField_geoClaspNumLaurent {N n i : ℕ} (h : n + i < N) :
    laurentToField (geoClaspNumLaurent N n i) =
      laurentToField (geoClaspDenLaurent N) *
        ∏ r ∈ Finset.Icc 1 n,
          ((1 - qParam ^ (i + r)) * (1 - qParam ^ (N - i - r)) / (1 - qParam ^ r)) := by
  have hy : ∀ r ∈ Finset.Icc 1 n, 1 - qParam ^ r ≠ 0 := fun r hr ↦ by
    have := one_sub_qParam_zpow_ne_zero (n := (r : ℤ)) (by have := (Finset.mem_Icc.mp hr).1; omega)
    rwa [zpow_natCast] at this
  simp only [geoClaspNumLaurent, geoClaspDenLaurent, map_mul, map_prod,
    laurentToField_one_sub_T_four_mul]
  rw [geo_prod_one_sub_pow_mul_prod_div qParam _ (by omega) hy]

/-- `[N] F_N` as a double sum of Zheng's products against the odd colours. -/
theorem geo_quantumInt_mul_torusReducedFormula_eq_double_sum (a N : ℕ) :
    quantumInt N * torusReducedFormula a N =
      ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        (RatFunc.X : RatFunc ℚ) ^ (4 * (N : ℤ) ^ 2 - 2 * N - 2) * ((qParam ^ N)⁻¹) ^ (n + i) *
          (∏ r ∈ Finset.Icc 1 n,
            ((1 - qParam ^ (i + r)) * (1 - qParam ^ (N - i - r)) / (1 - qParam ^ r))) *
          torusOddColor a n := by
  rw [claspAlg_quantumInt_mul_torusReducedFormula]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn' := Finset.mem_range.mp hn
  rw [geo_claspAlgCoeff_eq_coeff hn', geo_coeff_claspGen hn', Finset.mul_sum, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  rw [← geo_qBinom_mul_eq_zhengProduct (by omega : n + i < N), pow_add]
  ring

/-- The identity of Laurent polynomials obtained by clearing the denominators. -/
theorem geo_reduced_cleared_laurent (a N : ℕ) (P : LaurentPolynomial ℤ)
    (hP : laurentToField P = torusReducedFormula a N) :
    geoClaspDenLaurent N * (T (2 * (N : ℤ)) - T (-(2 * (N : ℤ)))) * P =
      ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        T (4 * (N : ℤ) ^ 2 - 2 * N - 2 - 4 * N * (n + i)) * geoClaspNumLaurent N n i *
          geoHatLaurent a n := by
  apply laurentToField_injective
  have hne := geo_ratFuncX_sq_sub_inv_ne_zero
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hq : (RatFunc.X : RatFunc ℚ) ^ (2 * (N : ℤ)) - RatFunc.X ^ (-(2 * (N : ℤ))) =
      (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) * quantumInt N := by
    rw [quantumInt, mul_div_cancel₀ _ hne]
  rw [map_mul, map_mul, map_sub, laurentToField_T, laurentToField_T, hq, hP, mul_assoc,
    mul_assoc, geo_quantumInt_mul_torusReducedFormula_eq_double_sum, map_sum, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hni : n + i < N := by
    have := Finset.mem_range.mp hi
    omega
  rw [map_mul, map_mul, laurentToField_T, laurentToField_geoClaspNumLaurent hni,
    laurentToField_geoHatLaurent]
  have hexp : (RatFunc.X : RatFunc ℚ) ^ (4 * (N : ℤ) ^ 2 - 2 * N - 2 - 4 * N * (n + i)) =
      RatFunc.X ^ (4 * (N : ℤ) ^ 2 - 2 * N - 2) * ((qParam ^ N)⁻¹) ^ (n + i) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg_one, ← zpow_mul, ← zpow_mul,
      qParam_zpow_eq_ratFuncX_zpow, ← zpow_add₀ hX]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- Evaluation of `T m` at `t ∈ ℂˣ`. -/
theorem geo_eval₂_T_complex {t : ℂ} (ht : t ≠ 0) (m : ℤ) :
    eval₂ (Int.castRingHom ℂ) (Units.mk0 t ht) (T m) = t ^ m := by
  rw [eval₂_T, Units.val_zpow_eq_zpow_val, Units.val_mk0]

/-- Evaluation of `1 - t^{4m}`. -/
theorem geo_eval₂_one_sub_T_four_mul {t : ℂ} (ht : t ≠ 0) (m : ℕ) :
    eval₂ (Int.castRingHom ℂ) (Units.mk0 t ht) (1 - T (4 * (m : ℤ))) = 1 - (t ^ 4) ^ m := by
  rw [map_sub, map_one, geo_eval₂_T_complex, ← pow_mul, ← zpow_natCast]
  push_cast
  rfl

/-- Evaluation of the Laurent form of `Ĥ_n` at `t` is `Ĥ_n(t²)`. -/
theorem geo_eval₂_geoHatLaurent {t : ℂ} (ht : t ≠ 0) (a n : ℕ) :
    eval₂ (Int.castRingHom ℂ) (Units.mk0 t ht) (geoHatLaurent a n) = geoHatInput a n (t ^ 2) := by
  have h2 : ∀ m : ℤ, (t ^ 2) ^ m = t ^ (2 * m) := fun m ↦ by
    rw [← zpow_natCast, ← zpow_mul]
    norm_cast
  simp only [geoHatLaurent, geoHatInput, map_mul, map_sum, map_sub, geo_eval₂_T_complex, h2]
  ring_nf

/-- Evaluation of the numerator Laurent polynomial. -/
theorem geo_eval₂_geoClaspNumLaurent {t : ℂ} (ht : t ≠ 0) {N n i : ℕ} (h : n + i < N)
    (hU : ∀ r ∈ Finset.Icc 1 (N - 1), 1 - t ^ (4 * r) ≠ 0) :
    eval₂ (Int.castRingHom ℂ) (Units.mk0 t ht) (geoClaspNumLaurent N n i) =
      eval₂ (Int.castRingHom ℂ) (Units.mk0 t ht) (geoClaspDenLaurent N) *
        ∏ r ∈ Finset.Icc 1 n,
          ((1 - t ^ (4 * (i + r))) * (1 - t ^ (4 * (N - i - r))) / (1 - t ^ (4 * r))) := by
  have hy : ∀ r ∈ Finset.Icc 1 n, 1 - (t ^ 4) ^ r ≠ 0 := fun r hr ↦ by
    have hr' := Finset.mem_Icc.mp hr
    rw [← pow_mul]
    exact hU r (Finset.mem_Icc.mpr ⟨hr'.1, by omega⟩)
  simp only [geoClaspNumLaurent, geoClaspDenLaurent, map_mul, map_prod,
    geo_eval₂_one_sub_T_four_mul, pow_mul]
  rw [geo_prod_one_sub_pow_mul_prod_div (t ^ 4) _ (by omega) hy]

/-- The reduced formula at a complex point `t ≠ 0` with `t^{4r} ≠ 1` for `1 ≤ r < N`. -/
theorem geo_reduced_eval_identity (a N : ℕ) (P : LaurentPolynomial ℤ)
    (hP : laurentToField P = torusReducedFormula a N) {t : ℂ} (ht : t ≠ 0)
    (hU : ∀ r ∈ Finset.Icc 1 (N - 1), 1 - t ^ (4 * r) ≠ 0) :
    (t ^ (2 * (N : ℤ)) - t ^ (-(2 * (N : ℤ)))) *
        eval₂ (Int.castRingHom ℂ) (Units.mk0 t ht) P =
      ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        t ^ (4 * (N : ℤ) ^ 2 - 2 * N - 2 - 4 * N * (n + i)) *
          (∏ r ∈ Finset.Icc 1 n,
            ((1 - t ^ (4 * (i + r))) * (1 - t ^ (4 * (N - i - r))) / (1 - t ^ (4 * r)))) *
          geoHatInput a n (t ^ 2) := by
  have h := congrArg (eval₂ (Int.castRingHom ℂ) (Units.mk0 t ht))
    (geo_reduced_cleared_laurent a N P hP)
  have hD : eval₂ (Int.castRingHom ℂ) (Units.mk0 t ht) (geoClaspDenLaurent N) ≠ 0 := by
    simp only [geoClaspDenLaurent, map_prod, geo_eval₂_one_sub_T_four_mul]
    refine Finset.prod_ne_zero_iff.mpr fun r hr ↦ ?_
    rw [← pow_mul]
    exact hU r hr
  have hsum : eval₂ (Int.castRingHom ℂ) (Units.mk0 t ht)
      (∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        T (4 * (N : ℤ) ^ 2 - 2 * N - 2 - 4 * N * (n + i)) * geoClaspNumLaurent N n i *
          geoHatLaurent a n) =
      eval₂ (Int.castRingHom ℂ) (Units.mk0 t ht) (geoClaspDenLaurent N) *
        ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
          t ^ (4 * (N : ℤ) ^ 2 - 2 * N - 2 - 4 * N * (n + i)) *
            (∏ r ∈ Finset.Icc 1 n,
              ((1 - t ^ (4 * (i + r))) * (1 - t ^ (4 * (N - i - r))) / (1 - t ^ (4 * r)))) *
            geoHatInput a n (t ^ 2) := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hni : n + i < N := by
      have := Finset.mem_range.mp hi
      omega
    rw [map_mul, map_mul, geo_eval₂_T_complex, geo_eval₂_geoClaspNumLaurent ht hni hU,
      geo_eval₂_geoHatLaurent]
    ring
  rw [hsum, map_mul, map_mul, map_sub, geo_eval₂_T_complex, geo_eval₂_T_complex, mul_assoc] at h
  exact mul_left_cancel₀ hD h

end AJConjecture
