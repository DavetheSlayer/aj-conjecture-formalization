import Mathlib
import AJHandoff.Geometry.GeoCurveFunctionField

/-!
# The coordinate ring of `Y² = X³ - X` is integrally closed (G-NORM, crux)

`ℚ[X, Y]/(Y² - X³ + X)` is integrally closed, and so is its localization at `Y`, the coordinate
ring of `Y² = X³ - X` minus the three points with `Y = 0` (the point at infinity is not affine).

Route. The coordinate ring `A` is free over `ℚ[X]` with basis `1, Y`
(`WeierstrassCurve.Affine.CoordinateRing.basis`), so `Frac A = ℚ(X)(Y)` is quadratic over `ℚ(X)`.
An element `f = a + bY` (`a, b ∈ ℚ(X)`) integral over `A` is integral over `ℚ[X]`; its trace `2a`
and norm `a² - b²(X³ - X)` are integral over the integrally closed `ℚ[X]`, hence lie in `ℚ[X]`
(`Algebra.isIntegral_trace`, `Algebra.isIntegral_norm`). So `a ∈ ℚ[X]` and
`b²(X³ - X) ∈ ℚ[X]`; as `X³ - X` is squarefree, `b ∈ ℚ[X]` (if `b = c/d` in lowest terms with
`d` nonconstant, `d² ∣ X³ - X`). Localizations of integrally closed domains are integrally closed.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The structure map `ℚ[X] → ℚ[X, Y]/(Y² - X³ + X)` is injective. -/
private theorem geoW_algebraMap_injective :
    Function.Injective (algebraMap ℚ[X] geoWeierstrass.toAffine.CoordinateRing) :=
  AdjoinRoot.of.injective_of_degree_ne_zero
    (by rw [WeierstrassCurve.Affine.degree_polynomial]; decide)

/-- The relation `Y² = X³ - X` with `X³ - X` written through the structure map. -/
private theorem geoW_Y_sq :
    geoWY ^ 2 = algebraMap ℚ[X] geoWeierstrass.toAffine.CoordinateRing (X ^ 3 - X) := by
  have heq : geoWeierstrass.toAffine.polynomial = X ^ 2 - C (X ^ 3 - X) := by
    simp [WeierstrassCurve.Affine.polynomial, geoWeierstrass]
    ring
  have h : (X ^ 2 - C (X ^ 3 - X) : ℚ[X][X]).eval₂
      (AdjoinRoot.of geoWeierstrass.toAffine.polynomial)
      (AdjoinRoot.root geoWeierstrass.toAffine.polynomial) = 0 := by
    rw [← heq]
    exact AdjoinRoot.eval₂_root _
  simp only [eval₂_sub, eval₂_C, eval₂_pow, eval₂_X] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact sub_eq_zero.mp h

/-- The hyperelliptic involution `Y ↦ -Y` of the coordinate ring. -/
private def geoWSigma : geoWeierstrass.toAffine.CoordinateRing →+*
    geoWeierstrass.toAffine.CoordinateRing :=
  AdjoinRoot.lift (algebraMap ℚ[X] _) (-geoWY) (by
    have heq : geoWeierstrass.toAffine.polynomial = X ^ 2 - C (X ^ 3 - X) := by
      simp [WeierstrassCurve.Affine.polynomial, geoWeierstrass]
      ring
    have key : ∀ q : ℚ[X][X], q = X ^ 2 - C (X ^ 3 - X) →
        q.eval₂ (algebraMap ℚ[X] geoWeierstrass.toAffine.CoordinateRing) (-geoWY) = 0 := by
      rintro q rfl
      simp only [eval₂_sub, eval₂_C, eval₂_pow, eval₂_X, neg_sq, geoW_Y_sq, sub_self]
    exact key _ heq)

/-- The involution fixes `ℚ[X]`. -/
private theorem geoWSigma_algebraMap (p : ℚ[X]) :
    geoWSigma (algebraMap ℚ[X] _ p) = algebraMap ℚ[X] _ p := by
  simp only [geoWSigma, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]

/-- The involution sends `Y` to `-Y`. -/
private theorem geoWSigma_Y : geoWSigma geoWY = -geoWY := by
  simp only [geoWSigma, geoWY, AdjoinRoot.lift_root]

/-- The involution squares to the identity. -/
private theorem geoWSigma_comp : geoWSigma.comp geoWSigma = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · ext p
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [← AdjoinRoot.algebraMap_eq, geoWSigma_algebraMap, geoWSigma_algebraMap]
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [← AdjoinRoot.algebraMap_eq, geoWSigma_algebraMap, geoWSigma_algebraMap]
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [← geoWY, geoWSigma_Y, map_neg, geoWSigma_Y, neg_neg]

/-- The involution as a ring automorphism. -/
private def geoWSigmaEquiv : geoWeierstrass.toAffine.CoordinateRing ≃+*
    geoWeierstrass.toAffine.CoordinateRing :=
  RingEquiv.ofRingHom geoWSigma geoWSigma geoWSigma_comp geoWSigma_comp

/-- The involution extended to the function field, as a `ℚ[X]`-algebra automorphism. -/
private def geoWSigmaK : geoWeierstrass.toAffine.FunctionField ≃ₐ[ℚ[X]]
    geoWeierstrass.toAffine.FunctionField :=
  AlgEquiv.ofRingEquiv (f := IsFractionRing.ringEquivOfRingEquiv geoWSigmaEquiv) (by
    intro p
    rw [IsScalarTower.algebraMap_apply ℚ[X] geoWeierstrass.toAffine.CoordinateRing,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact congrArg _ (geoWSigma_algebraMap p))

/-- The extended involution on elements coming from the coordinate ring. -/
private theorem geoWSigmaK_algebraMap (w : geoWeierstrass.toAffine.CoordinateRing) :
    geoWSigmaK (algebraMap _ geoWeierstrass.toAffine.FunctionField w) =
      algebraMap _ geoWeierstrass.toAffine.FunctionField (geoWSigma w) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap geoWSigmaEquiv w

/-- The structure map `ℚ[X] → ℚ(W)` is injective. -/
private theorem geoWK_algebraMap_injective :
    Function.Injective (algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField) := by
  rw [IsScalarTower.algebraMap_eq ℚ[X] geoWeierstrass.toAffine.CoordinateRing
    geoWeierstrass.toAffine.FunctionField, RingHom.coe_comp]
  exact (IsFractionRing.injective geoWeierstrass.toAffine.CoordinateRing
    geoWeierstrass.toAffine.FunctionField).comp geoW_algebraMap_injective

/-- A quotient `a/c` of polynomials that is integral over `ℚ[X]` inside `ℚ(W)` is a polynomial:
`c ∣ a`. -/
private theorem geo_dvd_of_isIntegral_div {a c : ℚ[X]} (hc : c ≠ 0)
    (h : IsIntegral ℚ[X] (algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField a /
      algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField c)) : c ∣ a := by
  let φ : FractionRing ℚ[X] →ₐ[ℚ[X]] geoWeierstrass.toAffine.FunctionField :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId ℚ[X] _) geoWK_algebraMap_injective
  have hφ : φ (algebraMap ℚ[X] (FractionRing ℚ[X]) a / algebraMap _ (FractionRing ℚ[X]) c) =
      algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField a /
        algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField c := by
    rw [map_div₀, AlgHom.commutes, AlgHom.commutes]
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  rw [← hφ, isIntegral_algHom_iff φ hφinj] at h
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  refine ⟨y, IsFractionRing.injective ℚ[X] (FractionRing ℚ[X]) ?_⟩
  have hc' : algebraMap ℚ[X] (FractionRing ℚ[X]) c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hc
  rw [eq_div_iff hc'] at hy
  rw [map_mul, ← hy, mul_comm]

/-- `X³ - X` is squarefree. -/
private theorem geo_squarefree_X_cube_sub_X : Squarefree (X ^ 3 - X : ℚ[X]) := by
  refine Polynomial.Separable.squarefree
    ⟨C (1 / 2) * (-9 * X), C (1 / 2) * (3 * X ^ 2 - 2), ?_⟩
  have h2 : C (1 / 2 : ℚ) * 2 = 1 := by
    rw [← map_ofNat C 2, ← C_mul]
    norm_num
  have hd : derivative (X ^ 3 - X : ℚ[X]) = 3 * X ^ 2 - 1 := by
    rw [derivative_sub, derivative_X_pow, derivative_X, ← map_ofNat C 3]
    norm_num
  rw [hd]
  linear_combination h2

/-- `ℚ[X, Y]/(Y² - X³ + X)` is integral over `ℚ[X]`. -/
private instance geoW_isIntegral : Algebra.IsIntegral ℚ[X] geoWeierstrass.toAffine.CoordinateRing :=
  have : Module.Finite ℚ[X] geoWeierstrass.toAffine.CoordinateRing :=
    Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis _)
  Algebra.IsIntegral.of_finite _ _

/-- Every element of the coordinate ring is `a + bY` with `a, b ∈ ℚ[X]`. -/
private theorem geoW_exists_basis (w : geoWeierstrass.toAffine.CoordinateRing) :
    ∃ a b : ℚ[X], w = algebraMap ℚ[X] _ a + algebraMap ℚ[X] _ b * geoWY := by
  obtain ⟨a, b, h⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq w
  refine ⟨a, b, ?_⟩
  rw [← h, Algebra.smul_def, Algebra.smul_def, mul_one]
  rfl

/-- The key local step: if `(a + bY)/π` is integral over the coordinate ring for a prime
`π ∈ ℚ[X]`, then `π` divides `a` and `b` (trace `2a/π`, norm `(a² - b²(X³ - X))/π²`, and
`X³ - X` squarefree). -/
private theorem geo_dvd_of_isIntegral_div_prime {π : ℚ[X]} (hπ : Prime π) (a b : ℚ[X])
    (h : IsIntegral geoWeierstrass.toAffine.CoordinateRing
      (algebraMap _ geoWeierstrass.toAffine.FunctionField
        (algebraMap ℚ[X] _ a + algebraMap ℚ[X] _ b * geoWY) /
          algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField π)) :
    π ∣ a ∧ π ∣ b := by
  set i := algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField with hi
  set yK := algebraMap _ geoWeierstrass.toAffine.FunctionField geoWY with hyK
  have hj (p : ℚ[X]) : algebraMap _ geoWeierstrass.toAffine.FunctionField
      (algebraMap ℚ[X] geoWeierstrass.toAffine.CoordinateRing p) = i p :=
    (IsScalarTower.algebraMap_apply _ _ _ p).symm
  have hY : yK ^ 2 = i (X ^ 3 - X) := by
    rw [hyK, ← map_pow, geoW_Y_sq, hj]
  have hπ0 : i π ≠ 0 := (map_ne_zero_iff _ geoWK_algebraMap_injective).mpr hπ.ne_zero
  have hR := isIntegral_trans (R := ℚ[X]) _ h
  have hσ := hR.map geoWSigmaK
  rw [map_div₀, geoWSigmaK_algebraMap, AlgEquiv.commutes, map_add, map_mul, geoWSigma_algebraMap,
    geoWSigma_algebraMap, geoWSigma_Y] at hσ
  simp only [map_add, map_mul, map_neg, hj] at hR hσ
  rw [← hyK] at hR hσ
  rw [← hi] at hσ
  have hsum := hR.add hσ
  rw [← add_div, show i a + i b * yK + (i a + i b * -yK) = i (2 * a) by
    rw [map_mul, map_ofNat]; ring] at hsum
  have hπa : π ∣ a := by
    have h2 := geo_dvd_of_isIntegral_div hπ.ne_zero hsum
    have h3 : π ∣ C (1 / 2) * (2 * a) := dvd_mul_of_dvd_right h2 _
    rwa [← mul_assoc, ← map_ofNat C 2, ← C_mul, show (1 / 2 : ℚ) * 2 = 1 by norm_num, C_1,
      one_mul] at h3
  have hprod := hR.mul hσ
  rw [div_mul_div_comm, show (i a + i b * yK) * (i a + i b * -yK) =
      i (a ^ 2 - b ^ 2 * (X ^ 3 - X)) by
    rw [map_sub, map_mul, map_pow, map_pow, ← hY]; ring, ← map_mul] at hprod
  have hπ2 := geo_dvd_of_isIntegral_div (mul_ne_zero hπ.ne_zero hπ.ne_zero) hprod
  refine ⟨hπa, ?_⟩
  by_contra hb
  have hcop : IsCoprime (π * π) (b ^ 2) := by
    rw [← sq]
    exact ((Prime.coprime_iff_not_dvd hπ).mpr hb).pow
  have hπf : π * π ∣ b ^ 2 * (X ^ 3 - X) := by
    have ha2 : π * π ∣ a ^ 2 := by rw [sq]; exact mul_dvd_mul hπa hπa
    have := dvd_sub ha2 hπ2
    rwa [sub_sub_cancel] at this
  exact hπ.not_isUnit (geo_squarefree_X_cube_sub_X π (hcop.dvd_of_dvd_mul_left hπf))

/-- Every element of `ℚ(W)` is `w/c` with `w` in the coordinate ring and `0 ≠ c ∈ ℚ[X]`
(multiply numerator and denominator by the conjugate of the denominator). -/
private theorem geoWK_exists_div (z : geoWeierstrass.toAffine.FunctionField) :
    ∃ (w : geoWeierstrass.toAffine.CoordinateRing) (c : ℚ[X]), c ≠ 0 ∧
      z = algebraMap _ geoWeierstrass.toAffine.FunctionField w /
        algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField c := by
  obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective
    (A := geoWeierstrass.toAffine.CoordinateRing) z
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  obtain ⟨p, q, rfl⟩ := geoW_exists_basis v
  have hnorm : (algebraMap ℚ[X] _ p + algebraMap ℚ[X] _ q * geoWY) *
      geoWSigma (algebraMap ℚ[X] _ p + algebraMap ℚ[X] _ q * geoWY) =
        algebraMap ℚ[X] geoWeierstrass.toAffine.CoordinateRing (p ^ 2 - q ^ 2 * (X ^ 3 - X)) := by
    rw [map_add, map_mul, geoWSigma_algebraMap, geoWSigma_algebraMap, geoWSigma_Y, map_sub,
      map_mul, map_pow, map_pow, ← geoW_Y_sq]
    ring
  have hσ0 : geoWSigma (algebraMap ℚ[X] _ p + algebraMap ℚ[X] _ q * geoWY) ≠ 0 := by
    intro h
    apply hv0
    have := congrArg geoWSigma h
    rwa [← RingHom.comp_apply, geoWSigma_comp, RingHom.id_apply, map_zero] at this
  have hc : p ^ 2 - q ^ 2 * (X ^ 3 - X) ≠ 0 := by
    intro h
    rw [h, map_zero] at hnorm
    exact mul_ne_zero hv0 hσ0 hnorm
  refine ⟨u * geoWSigma (algebraMap ℚ[X] _ p + algebraMap ℚ[X] _ q * geoWY), _, hc, ?_⟩
  have hjv : algebraMap _ geoWeierstrass.toAffine.FunctionField
      (algebraMap ℚ[X] _ p + algebraMap ℚ[X] _ q * geoWY) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hv0
  have hjσ : algebraMap _ geoWeierstrass.toAffine.FunctionField
      (geoWSigma (algebraMap ℚ[X] _ p + algebraMap ℚ[X] _ q * geoWY)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hσ0
  rw [IsScalarTower.algebraMap_apply ℚ[X] geoWeierstrass.toAffine.CoordinateRing
    geoWeierstrass.toAffine.FunctionField, ← hnorm, map_mul, map_mul, mul_div_mul_right _ _ hjσ]

/-- If `w/c` is integral over the coordinate ring, it lies in the coordinate ring (induction on
the prime factorisation of `c`). -/
private theorem geo_mem_of_isIntegral_div (c : ℚ[X]) : c ≠ 0 →
    ∀ w : geoWeierstrass.toAffine.CoordinateRing,
      IsIntegral geoWeierstrass.toAffine.CoordinateRing
        (algebraMap _ geoWeierstrass.toAffine.FunctionField w /
          algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField c) →
      ∃ y, algebraMap geoWeierstrass.toAffine.CoordinateRing
          geoWeierstrass.toAffine.FunctionField y =
        algebraMap _ geoWeierstrass.toAffine.FunctionField w /
          algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField c := by
  induction c using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h ↦ absurd rfl h
  | h₂ c hc =>
    intro _ w _
    obtain ⟨d, hd⟩ := hc.exists_right_inv
    refine ⟨w * algebraMap ℚ[X] _ d, ?_⟩
    have hcd : algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField c *
        algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField d = 1 := by
      rw [← map_mul, hd, map_one]
    have hc0 : algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField c ≠ 0 :=
      left_ne_zero_of_mul_eq_one hcd
    rw [map_mul, ← IsScalarTower.algebraMap_apply, eq_div_iff hc0, mul_assoc,
      mul_comm _ (algebraMap _ _ c), hcd, mul_one]
  | h₃ c π hc hπ ih =>
    intro _ w hw
    have hw' : IsIntegral geoWeierstrass.toAffine.CoordinateRing
        (algebraMap _ geoWeierstrass.toAffine.FunctionField w /
          algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField π) := by
      have hc0 : algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField c ≠ 0 :=
        (map_ne_zero_iff _ geoWK_algebraMap_injective).mpr hc
      have := hw.mul (isIntegral_algebraMap (x := algebraMap ℚ[X] _ c))
      rwa [← IsScalarTower.algebraMap_apply, map_mul, div_mul_eq_mul_div, mul_div_mul_right _ _ hc0]
        at this
    obtain ⟨a, b, rfl⟩ := geoW_exists_basis w
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := geo_dvd_of_isIntegral_div_prime hπ a b hw'
    have hπ0 : algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField π ≠ 0 :=
      (map_ne_zero_iff _ geoWK_algebraMap_injective).mpr hπ.ne_zero
    have heq : algebraMap _ geoWeierstrass.toAffine.FunctionField
        (algebraMap ℚ[X] _ (π * a') + algebraMap ℚ[X] _ (π * b') * geoWY) /
          algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField (π * c) =
        algebraMap _ geoWeierstrass.toAffine.FunctionField
          (algebraMap ℚ[X] _ a' + algebraMap ℚ[X] _ b' * geoWY) /
            algebraMap ℚ[X] geoWeierstrass.toAffine.FunctionField c := by
      rw [show algebraMap ℚ[X] geoWeierstrass.toAffine.CoordinateRing (π * a') +
          algebraMap ℚ[X] _ (π * b') * geoWY = algebraMap ℚ[X] _ π *
            (algebraMap ℚ[X] _ a' + algebraMap ℚ[X] _ b' * geoWY) by
        rw [map_mul, map_mul]; ring, map_mul, map_mul, ← IsScalarTower.algebraMap_apply,
        mul_div_mul_left _ _ hπ0]
    rw [heq] at hw ⊢
    exact ih hc _ hw

/-- `ℚ[X, Y]/(Y² - X³ + X)` is integrally closed. -/
theorem geo_isIntegrallyClosed_coordinateRing :
    IsIntegrallyClosed geoWeierstrass.toAffine.CoordinateRing := by
  rw [isIntegrallyClosed_iff geoWeierstrass.toAffine.FunctionField]
  intro z hz
  obtain ⟨w, c, hc, rfl⟩ := geoWK_exists_div z
  exact geo_mem_of_isIntegral_div c hc w hz

/-- `ℚ[X, Y]/(Y² - X³ + X) [1/Y]` is integrally closed. -/
theorem geo_isIntegrallyClosed_awayY : IsIntegrallyClosed (Localization.Away geoWY) := by
  have := geo_isIntegrallyClosed_coordinateRing
  have hY : geoWY ≠ 0 := by
    intro h
    have h2 := geoW_Y_sq
    rw [h, zero_pow two_ne_zero, eq_comm, ← map_zero (algebraMap ℚ[X] _)] at h2
    have h3 := congrArg (eval 2) (geoW_algebraMap_injective h2)
    norm_num at h3
  exact isIntegrallyClosed_of_isLocalization _ (Submonoid.powers geoWY)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hY)

end AJConjecture
