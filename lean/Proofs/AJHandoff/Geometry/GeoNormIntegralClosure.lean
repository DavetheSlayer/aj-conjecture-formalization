import Mathlib
import AJHandoff.Geometry.GeoNormIntClosed

/-!
# The normalization of the Laurent curve `E` (G-NORM, crux)

The Laurent coordinate ring `ℚ[M^{±1}, L^{±1}]/(E)` (`GeoLaurentE`; inverting `M` inverts `L`)
embeds into the function field `K_W = ℚ(Y² = X³ - X)` by `M ↦ Y/(-X(1 + X))`,
`L ↦ ((1 - X)/(1 + X))²`; call the image `geoLaurentImage`. Its integral closure in `K_W` is
`ℚ[X, Y, Y⁻¹]` (`geoPuncturedImage`), the coordinate ring of `Y² = X³ - X` minus the four points
`Y = 0` and `∞`. So the normalization of the Laurent curve is the elliptic curve minus the four
punctures `r = 0, 1, -1, ∞`; adding them gives the smooth projective model (`GeoNormModel`).

Route. `geoLaurentImage ⊆ geoPuncturedImage`: `M ↦ -(X - 1)/Y`, `M⁻¹ ↦ -X(X + 1)/Y`,
`1/(1 ± X) = ∓X(X ∓ 1)... /Y²`. Integrality of `X = -r`, `Y = M r(1 - r)`, `Y⁻¹` over the image:
`x r² + (1 - x) r + 1 = 0`, `x s² - (x + 1) s + 2 = 0` for `s = 1 - r`, with `x = M²` a unit, give
monic equations for `r`, `1/r`, `s`, `1/s`. `geoPuncturedImage` is integrally closed
(`geo_isIntegrallyClosed_awayY` transported along the injective map `Localization.Away Y → K_W`).
`ν*` is injective because `K_W` is a field and `GeoLaurentE` maps isomorphically onto its image
(compare `geo_chart_equiv`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The Laurent coordinate ring `ℚ[M^{±1}, L^{±1}]/(E)`. -/
abbrev GeoLaurentE : Type := Localization.Away geoMer

/-- The function field of `Y² = X³ - X` over `ℚ`. -/
abbrev GeoKW : Type := geoWeierstrass.toAffine.FunctionField

/-- `X` in `K_W`. -/
def geoKX : GeoKW := algebraMap _ GeoKW geoWX

/-- `Y` in `K_W`. -/
def geoKY : GeoKW := algebraMap _ GeoKW geoWY

/-- The image of `M` under the normalization map: `Y/(-X(1 + X))`. -/
def geoNuM : GeoKW := geoKY / (-(geoKX * (1 + geoKX)))

/-- The image of `L` under the normalization map: `((1 - X)/(1 + X))²`. -/
def geoNuL : GeoKW := ((1 - geoKX) / (1 + geoKX)) ^ 2

/-- The image `ℚ[ν*M^{±1}, ν*L^{±1}]` of the Laurent coordinate ring. -/
def geoLaurentImage : Subalgebra ℚ GeoKW :=
  Algebra.adjoin ℚ {geoNuM, geoNuM⁻¹, geoNuL, geoNuL⁻¹}

/-- The coordinate ring `ℚ[X, Y, Y⁻¹]` of `Y² = X³ - X` minus `{Y = 0} ∪ {∞}`, inside `K_W`. -/
def geoPuncturedImage : Subalgebra ℚ GeoKW :=
  Algebra.adjoin ℚ {geoKX, geoKY, geoKY⁻¹}

/-- A subalgebra `S` of a field that contains the image of an injective map `ν : R → K`, contains
`(ν s)⁻¹`, and consists of quotients `ν a / ν s ^ k`, is the localization of `R` away from `s`. -/
private theorem geo_isLocalization_of_subalgebra {R K : Type*} [CommRing R] [Field K]
    [Algebra ℚ K] (ν : R →+* K) (hν : Function.Injective ν) (s : R) (S : Subalgebra ℚ K)
    (hmem : ∀ a, ν a ∈ S) (hinv : (ν s)⁻¹ ∈ S) (hs : ν s ≠ 0)
    (hsurj : ∀ z ∈ S, ∃ a : R, ∃ k : ℕ, z * ν s ^ k = ν a) :
    @IsLocalization R _ (Submonoid.powers s) S _ (ν.codRestrict S hmem).toAlgebra := by
  let _ : Algebra R S := (ν.codRestrict S hmem).toAlgebra
  have hu : IsUnit (algebraMap R S s) :=
    IsUnit.of_mul_eq_one (⟨_, hinv⟩ : S) (Subtype.ext (mul_inv_cancel₀ hs))
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [map_pow]
    exact hu.pow k
  · rintro ⟨z, hz⟩
    obtain ⟨a, k, h⟩ := hsurj z hz
    refine ⟨⟨a, ⟨s ^ k, k, rfl⟩⟩, Subtype.ext ?_⟩
    change z * ν (s ^ k) = ν a
    rw [map_pow, h]
  · intro x y h
    refine ⟨1, ?_⟩
    rw [hν (congrArg Subtype.val h)]

/-- Under the hypotheses of `geo_isLocalization_of_subalgebra`, `R[1/s]` is isomorphic to `S`
compatibly with `ν`. -/
private theorem geo_exists_equiv_away {R K : Type*} [CommRing R] [Field K] [Algebra ℚ K]
    (ν : R →+* K) (hν : Function.Injective ν) (s : R) (S : Subalgebra ℚ K)
    (hmem : ∀ a, ν a ∈ S) (hinv : (ν s)⁻¹ ∈ S) (hs : ν s ≠ 0)
    (hsurj : ∀ z ∈ S, ∃ a : R, ∃ k : ℕ, z * ν s ^ k = ν a) :
    ∃ e : Localization.Away s ≃+* S, ∀ a, (e (algebraMap R _ a) : K) = ν a := by
  let _ : Algebra R S := (ν.codRestrict S hmem).toAlgebra
  have := geo_isLocalization_of_subalgebra ν hν s S hmem hinv hs hsurj
  refine ⟨(IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) S).toRingEquiv,
    fun a ↦ ?_⟩
  change ((IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) S)
    (algebraMap R _ a) : K) = ν a
  rw [AlgEquiv.commutes]
  rfl

/-- If every generator of `Algebra.adjoin ℚ T` is a quotient `ν a / ν s ^ k`, so is every element
of the adjoined algebra. -/
private theorem geo_adjoin_quotients {R K : Type*} [CommRing R] [Algebra ℚ R] [Field K]
    [Algebra ℚ K] (ν : R →+* K) (s : R) (T : Set K)
    (hT : ∀ t ∈ T, ∃ a : R, ∃ k : ℕ, t * ν s ^ k = ν a) :
    ∀ z ∈ Algebra.adjoin ℚ T, ∃ a : R, ∃ k : ℕ, z * ν s ^ k = ν a := by
  intro z hz
  induction hz using Algebra.adjoin_induction with
  | mem t ht => exact hT t ht
  | algebraMap q =>
    refine ⟨algebraMap ℚ R q, 0, ?_⟩
    rw [pow_zero, mul_one, ← RingHom.comp_apply, RingHom.ext_rat (ν.comp (algebraMap ℚ R))]
  | add x y _ _ hx hy =>
    obtain ⟨a, k, ha⟩ := hx
    obtain ⟨b, l, hb⟩ := hy
    refine ⟨a * s ^ l + b * s ^ k, k + l, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← ha, ← hb]
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨a, k, ha⟩ := hx
    obtain ⟨b, l, hb⟩ := hy
    refine ⟨a * b, k + l, ?_⟩
    rw [map_mul, ← ha, ← hb]
    ring

/-- A ring map out of `ℚ[X][Y]/(f)` lands in a subalgebra containing the images of `X` and `Y`. -/
private theorem geo_mem_of_adjoinRoot {K : Type*} [Field K] [Algebra ℚ K] {f : ℚ[X][X]}
    (g : AdjoinRoot f →+* K) (S : Subalgebra ℚ K) (hX : g (AdjoinRoot.of f X) ∈ S)
    (hr : g (AdjoinRoot.root f) ∈ S) (a : AdjoinRoot f) : g a ∈ S := by
  have hpoly : ∀ p : ℚ[X], g (AdjoinRoot.of f p) ∈ S := by
    intro p
    refine Polynomial.induction_on p (fun c ↦ ?_) (fun p q hp hq ↦ ?_) (fun n c h ↦ ?_)
    · rw [← RingHom.comp_apply, ← RingHom.comp_apply,
        RingHom.ext_rat ((g.comp (AdjoinRoot.of f)).comp C) (algebraMap ℚ K)]
      exact S.algebraMap_mem c
    · rw [map_add, map_add]
      exact add_mem hp hq
    · rw [pow_succ, ← mul_assoc, map_mul, map_mul]
      exact mul_mem h hX
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  refine Polynomial.induction_on p (fun c ↦ ?_) (fun p q hp hq ↦ ?_) (fun n c h ↦ ?_)
  · rw [AdjoinRoot.mk_C]
    exact hpoly c
  · rw [map_add, map_add]
    exact add_mem hp hq
  · rw [pow_succ, ← mul_assoc, map_mul, map_mul, AdjoinRoot.mk_X]
    exact mul_mem h hr

/-- The relation `Y² = X³ - X` in the coordinate ring. -/
private theorem geoKW_coord_rel : geoWY ^ 2 = geoWX ^ 3 - geoWX := by
  have heq : geoWeierstrass.toAffine.polynomial = X ^ 2 - C (X ^ 3 - X) := by
    simp [WeierstrassCurve.Affine.polynomial, geoWeierstrass]
    ring
  have h : (X ^ 2 - C (X ^ 3 - X) : ℚ[X][X]).eval₂
      (AdjoinRoot.of geoWeierstrass.toAffine.polynomial)
      (AdjoinRoot.root geoWeierstrass.toAffine.polynomial) = 0 := by
    rw [← heq]
    exact AdjoinRoot.eval₂_root _
  simp only [eval₂_sub, eval₂_C, eval₂_pow, eval₂_X, map_sub, map_pow] at h
  exact sub_eq_zero.mp h

/-- The relation `Y² = X³ - X` in `K_W`. -/
private theorem geoKW_rel : geoKY ^ 2 = geoKX ^ 3 - geoKX := by
  have h := congrArg (algebraMap _ GeoKW) geoKW_coord_rel
  simpa only [map_sub, map_pow, geoKX, geoKY] using h

/-- `Y ≠ 0` in `K_W`. -/
private theorem geoKY_ne_zero : geoKY ≠ 0 := by
  have hinj := AdjoinRoot.of.injective_of_degree_ne_zero
    (f := geoWeierstrass.toAffine.polynomial)
    (by rw [WeierstrassCurve.Affine.degree_polynomial]; decide)
  intro h
  have hY : geoWY = 0 := (map_eq_zero_iff _ (IsFractionRing.injective _ GeoKW)).mp h
  have h1 := geoKW_coord_rel
  rw [hY] at h1
  have h2 : AdjoinRoot.of geoWeierstrass.toAffine.polynomial (X * (X ^ 2 - 1)) =
      AdjoinRoot.of geoWeierstrass.toAffine.polynomial 0 := by
    rw [map_zero, map_mul, map_sub, map_pow, map_one]
    change geoWX * (geoWX ^ 2 - 1) = 0
    linear_combination -h1
  have h3 := congrArg (eval 2) (hinj h2)
  norm_num at h3

/-- `X`, `X - 1` and `1 + X` are nonzero in `K_W`. -/
private theorem geoKX_ne_zero : geoKX ≠ 0 ∧ geoKX - 1 ≠ 0 ∧ 1 + geoKX ≠ 0 := by
  have h : geoKX * (geoKX - 1) * (1 + geoKX) ≠ 0 := by
    rw [show geoKX * (geoKX - 1) * (1 + geoKX) = geoKY ^ 2 by linear_combination -geoKW_rel]
    exact pow_ne_zero 2 geoKY_ne_zero
  exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul h), right_ne_zero_of_mul (left_ne_zero_of_mul h),
    right_ne_zero_of_mul h⟩

/-- `Y⁻¹` lies in `ℚ[X, Y, Y⁻¹]`. -/
private theorem geoKY_inv_mem : geoKY⁻¹ ∈ geoPuncturedImage :=
  Algebra.subset_adjoin (by simp)

/-- `X` lies in `ℚ[X, Y, Y⁻¹]`. -/
private theorem geoKX_mem : geoKX ∈ geoPuncturedImage :=
  Algebra.subset_adjoin (by simp)

/-- `Y` lies in `ℚ[X, Y, Y⁻¹]`. -/
private theorem geoKY_mem : geoKY ∈ geoPuncturedImage :=
  Algebra.subset_adjoin (by simp)

/-- The coordinate ring maps into `ℚ[X, Y, Y⁻¹]`. -/
private theorem geoPunctured_mem (b : geoWeierstrass.toAffine.CoordinateRing) :
    algebraMap _ GeoKW b ∈ geoPuncturedImage :=
  geo_mem_of_adjoinRoot (algebraMap _ GeoKW) geoPuncturedImage geoKX_mem geoKY_mem b

/-- Every element of `ℚ[X, Y, Y⁻¹]` is `b / Y ^ k`. -/
private theorem geoPunctured_surj : ∀ z ∈ geoPuncturedImage,
    ∃ b : geoWeierstrass.toAffine.CoordinateRing, ∃ k : ℕ,
      z * algebraMap _ GeoKW geoWY ^ k = algebraMap _ GeoKW b := by
  refine geo_adjoin_quotients _ _ _ fun t ht ↦ ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl
  · exact ⟨geoWX, 0, by rw [pow_zero, mul_one]; rfl⟩
  · exact ⟨geoWY, 0, by rw [pow_zero, mul_one]; rfl⟩
  · exact ⟨1, 1, by rw [pow_one, map_one]; exact inv_mul_cancel₀ geoKY_ne_zero⟩

/-- The defining relation of `E` in its coordinate ring. -/
private theorem geoLaurent_coord_rel :
    geoLong ^ 2 - (geoMer ^ 4 - 4 * geoMer ^ 2 + 1) * geoLong + geoMer ^ 4 = 0 := by
  have heq : geoExtraFactorℚ = X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) := by
    simp [geoExtraFactorℚ, extraFactor]
  have h : (X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) : ℚ[X][X]).eval₂
      (AdjoinRoot.of geoExtraFactorℚ) (AdjoinRoot.root geoExtraFactorℚ) = 0 := by
    rw [← heq]
    exact AdjoinRoot.eval₂_root _
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, eval₂_one, map_sub,
    map_add, map_pow, map_mul, map_one, map_ofNat] at h
  simpa [geoMer, geoLong] using h

/-- `ν*M = Y/(-X(1 + X))` is nonzero. -/
private theorem geoNuM_ne_zero : geoNuM ≠ 0 := by
  obtain ⟨h0, -, h2⟩ := geoKX_ne_zero
  exact div_ne_zero geoKY_ne_zero (neg_ne_zero.mpr (mul_ne_zero h0 h2))

/-- The image of the Laurent ring lies in `ℚ[X, Y, Y⁻¹]`: `ν*M = -(X - 1)/Y`,
`ν*M⁻¹ = -X(X + 1)/Y`, `ν*L = X²(X - 1)⁴/Y⁴`, `ν*L⁻¹ = X²(X + 1)⁴/Y⁴`. -/
private theorem geoLaurent_le_punctured : geoLaurentImage ≤ geoPuncturedImage := by
  obtain ⟨h0, h1, h2⟩ := geoKX_ne_zero
  have hY := geoKY_ne_zero
  have hrel := geoKW_rel
  have h1' : 1 - geoKX ≠ 0 := fun h ↦ h1 (by linear_combination -h)
  have hX := geoKX_mem
  have hYi := geoKY_inv_mem
  rw [geoLaurentImage, Algebra.adjoin_le_iff]
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · have h : geoNuM = -(geoKX - 1) / geoKY := by
      rw [geoNuM, div_eq_div_iff (neg_ne_zero.mpr (mul_ne_zero h0 h2)) hY]
      linear_combination hrel
    rw [h, div_eq_mul_inv]
    exact mul_mem (neg_mem (sub_mem hX (one_mem _))) hYi
  · rw [geoNuM, inv_div, div_eq_mul_inv]
    exact mul_mem (neg_mem (mul_mem hX (add_mem (one_mem _) hX))) hYi
  · have h : geoNuL = geoKX ^ 2 * (geoKX - 1) ^ 4 / geoKY ^ 4 := by
      rw [geoNuL, div_pow, div_eq_div_iff (pow_ne_zero 2 h2) (pow_ne_zero 4 hY)]
      linear_combination (1 - geoKX) ^ 2 * (geoKY ^ 2 + geoKX ^ 3 - geoKX) * hrel
    rw [h, div_eq_mul_inv, ← inv_pow]
    exact mul_mem (mul_mem (pow_mem hX 2) (pow_mem (sub_mem hX (one_mem _)) 4)) (pow_mem hYi 4)
  · have h : geoNuL⁻¹ = geoKX ^ 2 * (1 + geoKX) ^ 4 / geoKY ^ 4 := by
      rw [geoNuL, ← inv_pow, inv_div, div_pow,
        div_eq_div_iff (pow_ne_zero 2 h1') (pow_ne_zero 4 hY)]
      linear_combination (1 + geoKX) ^ 2 * (geoKY ^ 2 + geoKX ^ 3 - geoKX) * hrel
    rw [h, div_eq_mul_inv, ← inv_pow]
    exact mul_mem (mul_mem (pow_mem hX 2) (pow_mem (add_mem (one_mem _) hX) 4)) (pow_mem hYi 4)

/-- With `x = (ν*M)²`, the parameter `X = -r` satisfies `x X² - (1 - x) X + 1 = 0`. -/
private theorem geoKX_master : geoNuM ^ 2 * geoKX ^ 2 - (1 - geoNuM ^ 2) * geoKX + 1 = 0 := by
  obtain ⟨h0, -, h2⟩ := geoKX_ne_zero
  have hx : geoNuM ^ 2 * (geoKX * (1 + geoKX)) = geoKX - 1 := by
    rw [geoNuM, div_pow, neg_sq, div_mul_eq_mul_div,
      div_eq_iff (pow_ne_zero 2 (mul_ne_zero h0 h2))]
    linear_combination geoKX * (1 + geoKX) * geoKW_rel
  linear_combination hx

/-- `ν*M` as an element of the Laurent image. -/
private def geoNuMA : geoLaurentImage := ⟨geoNuM, Algebra.subset_adjoin (by simp)⟩

/-- `(ν*M)⁻¹` as an element of the Laurent image. -/
private def geoNuMinvA : geoLaurentImage := ⟨geoNuM⁻¹, Algebra.subset_adjoin (by simp)⟩

/-- `X` is integral over the Laurent image. -/
private theorem geoKX_isIntegral : IsIntegral geoLaurentImage geoKX := by
  have hinv : geoNuM⁻¹ * geoNuM = 1 := inv_mul_cancel₀ geoNuM_ne_zero
  refine ⟨X ^ 2 - C ((1 - geoNuMA ^ 2) * geoNuMinvA ^ 2) * X + C (geoNuMinvA ^ 2), by monicity!,
    ?_⟩
  rw [eval₂_add, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X_pow, eval₂_X]
  change geoKX ^ 2 - (1 - geoNuM ^ 2) * geoNuM⁻¹ ^ 2 * geoKX + geoNuM⁻¹ ^ 2 = 0
  linear_combination geoNuM⁻¹ ^ 2 * geoKX_master - geoKX ^ 2 * (1 + geoNuM⁻¹ * geoNuM) * hinv

/-- `X⁻¹` is integral over the Laurent image. -/
private theorem geoKX_inv_isIntegral : IsIntegral geoLaurentImage geoKX⁻¹ := by
  have hinv : geoKX⁻¹ * geoKX = 1 := inv_mul_cancel₀ geoKX_ne_zero.1
  refine ⟨X ^ 2 - C (1 - geoNuMA ^ 2) * X + C (geoNuMA ^ 2), by monicity!, ?_⟩
  rw [eval₂_add, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X_pow, eval₂_X]
  change geoKX⁻¹ ^ 2 - (1 - geoNuM ^ 2) * geoKX⁻¹ + geoNuM ^ 2 = 0
  linear_combination geoKX⁻¹ ^ 2 * geoKX_master -
    (-(1 - geoNuM ^ 2) * geoKX⁻¹ + geoNuM ^ 2 * (1 + geoKX⁻¹ * geoKX)) * hinv

/-- `(1 + X)⁻¹` is integral over the Laurent image. -/
private theorem geoKX_one_add_inv_isIntegral : IsIntegral geoLaurentImage (1 + geoKX)⁻¹ := by
  have hinv : (1 + geoKX)⁻¹ * (1 + geoKX) = 1 := inv_mul_cancel₀ geoKX_ne_zero.2.2
  refine ⟨X ^ 2 - C ((geoNuMA ^ 2 + 1) * algebraMap ℚ _ (1 / 2)) * X +
    C (geoNuMA ^ 2 * algebraMap ℚ _ (1 / 2)), by monicity!, ?_⟩
  rw [eval₂_add, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X_pow, eval₂_X]
  change (1 + geoKX)⁻¹ ^ 2 - (geoNuM ^ 2 + 1) * algebraMap ℚ GeoKW (1 / 2) * (1 + geoKX)⁻¹ +
    geoNuM ^ 2 * algebraMap ℚ GeoKW (1 / 2) = 0
  rw [map_div₀, map_one, map_ofNat]
  have : CharZero GeoKW := charZero_of_injective_algebraMap (algebraMap ℚ GeoKW).injective
  linear_combination (1 / 2) * (1 + geoKX)⁻¹ ^ 2 * geoKX_master +
    ((geoNuM ^ 2 + 1) / 2 * (1 + geoKX)⁻¹ - geoNuM ^ 2 / 2 * (1 + (1 + geoKX)⁻¹ * (1 + geoKX))) *
      hinv

/-- `ℚ[X, Y, Y⁻¹]` is integral over the Laurent image. -/
private theorem geoPunctured_le_integralClosure :
    geoPuncturedImage ≤ (integralClosure geoLaurentImage GeoKW).restrictScalars ℚ := by
  obtain ⟨h0, -, h2⟩ := geoKX_ne_zero
  have hX := geoKX_isIntegral
  have hM : IsIntegral geoLaurentImage geoNuM := isIntegral_algebraMap (x := geoNuMA)
  have hMi : IsIntegral geoLaurentImage geoNuM⁻¹ := isIntegral_algebraMap (x := geoNuMinvA)
  have hYeq : geoKY = geoNuM * (-(geoKX * (1 + geoKX))) := by
    rw [geoNuM, div_mul_cancel₀ _ (neg_ne_zero.mpr (mul_ne_zero h0 h2))]
  rw [geoPuncturedImage, Algebra.adjoin_le_iff]
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl
  · exact hX
  · change IsIntegral _ geoKY
    rw [hYeq]
    exact hM.mul (hX.mul (isIntegral_one.add hX)).neg
  · change IsIntegral _ geoKY⁻¹
    rw [hYeq, mul_inv, inv_neg, mul_inv]
    exact hMi.mul (geoKX_inv_isIntegral.mul geoKX_one_add_inv_isIntegral).neg

/-- `ℚ[X, Y, Y⁻¹]` is integrally closed in `K_W`: it is the localization of the integrally closed
coordinate ring at `Y`. -/
private theorem geoPunctured_mem_of_isIntegral {z : GeoKW} (hz : IsIntegral geoPuncturedImage z) :
    z ∈ geoPuncturedImage := by
  let _ : Algebra geoWeierstrass.toAffine.CoordinateRing geoPuncturedImage :=
    ((algebraMap _ GeoKW).codRestrict geoPuncturedImage geoPunctured_mem).toAlgebra
  have : IsLocalization (Submonoid.powers geoWY) geoPuncturedImage :=
    geo_isLocalization_of_subalgebra (algebraMap _ GeoKW) (IsFractionRing.injective _ _) geoWY
      geoPuncturedImage geoPunctured_mem geoKY_inv_mem geoKY_ne_zero geoPunctured_surj
  have : IsScalarTower geoWeierstrass.toAffine.CoordinateRing geoPuncturedImage GeoKW :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers geoWY) z hz
  have := geo_isIntegrallyClosed_coordinateRing
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hk
  rw [Submonoid.smul_def, Algebra.smul_def, map_pow] at hb
  have hz' : z = algebraMap _ GeoKW b * geoKY⁻¹ ^ k := by
    rw [hb, inv_pow, mul_comm, ← mul_assoc]
    change z = (geoKY ^ k)⁻¹ * geoKY ^ k * z
    rw [inv_mul_cancel₀ (pow_ne_zero k geoKY_ne_zero), one_mul]
  rw [hz']
  exact mul_mem (geoPunctured_mem b) (pow_mem geoKY_inv_mem k)

/-- The normalization map `ν*` is an isomorphism of `GeoLaurentE` onto its image. -/
theorem geo_laurent_equiv :
    ∃ e : GeoLaurentE ≃+* geoLaurentImage,
      (e (algebraMap GeoCoordE GeoLaurentE geoMer) : GeoKW) = geoNuM ∧
        (e (algebraMap GeoCoordE GeoLaurentE geoLong) : GeoKW) = geoNuL := by
  obtain ⟨eK, hM, hL, -⟩ := geo_functionField_equiv
  obtain ⟨h0, -, h2⟩ := geoKX_ne_zero
  let ν : GeoCoordE →+* GeoKW := eK.toRingHom.comp (algebraMap GeoCoordE GeoFunFieldE)
  have hνinj : Function.Injective ν := eK.injective.comp (IsFractionRing.injective _ _)
  have hνM : ν geoMer = geoNuM := by
    rw [geoNuM, eq_div_iff (neg_ne_zero.mpr (mul_ne_zero h0 h2))]
    exact hM
  have hνL : ν geoLong = geoNuL := by
    rw [geoNuL, div_pow, eq_div_iff (pow_ne_zero 2 h2)]
    exact hL
  have hrel : geoNuL ^ 2 - (geoNuM ^ 4 - 4 * geoNuM ^ 2 + 1) * geoNuL + geoNuM ^ 4 = 0 := by
    have h := congrArg ν geoLaurent_coord_rel
    simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat, map_zero, hνM,
      hνL] at h
    exact h
  have hL0 : geoNuL ≠ 0 := by
    intro h
    rw [h] at hrel
    exact pow_ne_zero 4 geoNuM_ne_zero (by linear_combination hrel)
  have hgen : ∀ t ∈ ({geoNuM, geoNuM⁻¹, geoNuL, geoNuL⁻¹} : Set GeoKW), t ∈ geoLaurentImage :=
    fun t ht ↦ Algebra.subset_adjoin ht
  have hmem : ∀ a, ν a ∈ geoLaurentImage :=
    geo_mem_of_adjoinRoot ν geoLaurentImage
      (by change ν geoMer ∈ _; rw [hνM]; exact hgen _ (by simp))
      (by change ν geoLong ∈ _; rw [hνL]; exact hgen _ (by simp))
  have hsurj : ∀ z ∈ geoLaurentImage, ∃ a : GeoCoordE, ∃ k : ℕ, z * ν geoMer ^ k = ν a := by
    refine geo_adjoin_quotients _ _ _ fun t ht ↦ ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨geoMer, 0, by rw [pow_zero, mul_one, hνM]⟩
    · exact ⟨1, 1, by rw [pow_one, map_one, hνM]; exact inv_mul_cancel₀ geoNuM_ne_zero⟩
    · exact ⟨geoLong, 0, by rw [pow_zero, mul_one, hνL]⟩
    · refine ⟨-(geoLong - (geoMer ^ 4 - 4 * geoMer ^ 2 + 1)), 4, ?_⟩
      simp only [map_neg, map_sub, map_add, map_pow, map_mul, map_one, map_ofNat, hνM, hνL]
      rw [inv_mul_eq_iff_eq_mul₀ hL0]
      linear_combination hrel
  obtain ⟨e, he⟩ := geo_exists_equiv_away ν hνinj geoMer geoLaurentImage hmem
    (by rw [hνM]; exact hgen _ (by simp)) (by rw [hνM]; exact geoNuM_ne_zero) hsurj
  exact ⟨e, by rw [he, hνM], by rw [he, hνL]⟩

/-- `ℚ[X, Y]/(Y² - X³ + X)[1/Y]` is isomorphic to `geoPuncturedImage`. -/
theorem geo_punctured_equiv :
    ∃ e : Localization.Away geoWY ≃+* geoPuncturedImage,
      (e (algebraMap _ (Localization.Away geoWY) geoWX) : GeoKW) = geoKX ∧
        (e (algebraMap _ (Localization.Away geoWY) geoWY) : GeoKW) = geoKY := by
  obtain ⟨e, he⟩ := geo_exists_equiv_away (algebraMap _ GeoKW) (IsFractionRing.injective _ _)
    geoWY geoPuncturedImage geoPunctured_mem geoKY_inv_mem geoKY_ne_zero geoPunctured_surj
  exact ⟨e, he geoWX, he geoWY⟩

/-- The integral closure of the Laurent coordinate ring of `E` in its function field is the
coordinate ring of the elliptic curve minus the four punctures. -/
theorem geo_integralClosure_laurent :
    (integralClosure geoLaurentImage GeoKW).restrictScalars ℚ = geoPuncturedImage := by
  refine le_antisymm (fun z hz ↦ ?_) geoPunctured_le_integralClosure
  have hz' : IsIntegral geoLaurentImage z := hz
  let _ : Algebra geoLaurentImage geoPuncturedImage :=
    (Subalgebra.inclusion geoLaurent_le_punctured).toRingHom.toAlgebra
  have : IsScalarTower geoLaurentImage geoPuncturedImage GeoKW :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  exact geoPunctured_mem_of_isIntegral hz'.tower_top

end AJConjecture
