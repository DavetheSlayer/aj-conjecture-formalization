import Mathlib
import AJConjecture.ExtraFactorIrreducible
import AJHandoff.Geometry.GeoCurveWeierstrass

/-!
# The function field of `E` is the function field of `Y² = X³ - X` (G-CURVE, crux)

`GeoCoordE = ℚ[M, L]/(E)` is the coordinate ring of the extra curve over `ℚ` (`E` is irreducible
over `ℚ`, from `irreducible_extraFactor_map` over `ℂ`), and `GeoFunFieldE` its fraction field.
The birational map of `GeoCurveWeierstrass` is an isomorphism of the localized coordinate rings

  `ℚ[M, L]/(E) [1/(M(M² - 1))] ≅ ℚ[X, Y]/(Y² - X³ + X) [1/(Y(X² + 1))]`,

`M ↦ Y/(-X(1 + X))`, `L ↦ ((1 - X)/(1 + X))²`, with inverse `X ↦ -r`, `Y ↦ M r(1 - r)`,
`r = (M² + L)/(M²(M² - 1))`; hence an isomorphism of function fields.

Route. Define both ring homomorphisms with `AdjoinRoot.lift` and `IsLocalization.Away.lift`: the
relations are the identities of `GeoCurveParam` in the target ring, and the inverted elements map
to units (`X(X - 1)(X + 1) = Y²`; with `x = M²`, on `E` one has
`(L + x)(x² - 3x + 1 - L) = x(x - 1)²` and `(x² - 2x - L)(L + 2x - 1) = 2x(x - 1)²`, so the
numerators of `r` and `1 - r` are units once `M(M² - 1)` is). Check both composites on generators
(`AdjoinRoot.algHom_ext`, `IsLocalization.ringHom_ext`). The function field iso follows from
`IsFractionRing` of the localizations (`IsLocalization.isFractionRing...`/
`FractionRing.algEquiv`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `E` with rational coefficients, as a polynomial in `L` over `ℚ[M]`. -/
abbrev geoExtraFactorℚ : ℚ[X][X] :=
  extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℚ))

/-- `E` is monic in `L` over `ℚ[M]`. -/
private theorem geo_extraFactorℚ_monic : geoExtraFactorℚ.Monic := by
  have hlin : (C (X ^ 4 - 4 * X ^ 2 + 1 : ℤ[X]) * X).degree < ((2 : ℕ) : WithBot ℕ) :=
    (degree_C_mul_X_le _).trans_lt (by norm_num)
  refine Monic.map _ ((monic_X_pow_sub hlin).add_of_left ?_)
  rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  exact degree_C_le.trans_lt (by norm_num)

/-- `E` is irreducible in `ℚ[M][L]`, descending from its irreducibility over `ℂ`. -/
private theorem geo_irreducible_extraFactorℚ : Irreducible geoExtraFactorℚ := by
  refine geo_extraFactorℚ_monic.irreducible_of_irreducible_map
    (Polynomial.mapRingHom (algebraMap ℚ ℂ)) _ ?_
  rw [Polynomial.map_map]
  convert irreducible_extraFactor_map using 2
  ext <;> simp

/-- `E` is prime in `ℚ[M][L]`. -/
theorem geo_prime_extraFactorℚ : Prime geoExtraFactorℚ :=
  geo_irreducible_extraFactorℚ.prime

/-- The coordinate ring `ℚ[M, L]/(E)` of the extra curve. -/
abbrev GeoCoordE : Type := AdjoinRoot geoExtraFactorℚ

instance : IsDomain GeoCoordE := AdjoinRoot.isDomain_of_prime geo_prime_extraFactorℚ

/-- The meridian coordinate `M`. -/
def geoMer : GeoCoordE := AdjoinRoot.of geoExtraFactorℚ Polynomial.X

/-- The longitude coordinate `L`. -/
def geoLong : GeoCoordE := AdjoinRoot.root geoExtraFactorℚ

/-- The function field `ℚ(E)`. -/
abbrev GeoFunFieldE : Type := FractionRing GeoCoordE

/-- The chart of `E` where `M(M² - 1)` is invertible (the torus minus the two nodes). -/
abbrev GeoChartE : Type := Localization.Away (geoMer * (geoMer ^ 2 - 1))

/-- The coordinate `X` on `Y² = X³ - X`. -/
def geoWX : geoWeierstrass.toAffine.CoordinateRing := AdjoinRoot.of _ Polynomial.X

/-- The coordinate `Y` on `Y² = X³ - X`. -/
def geoWY : geoWeierstrass.toAffine.CoordinateRing := AdjoinRoot.root _

/-- The chart of `Y² = X³ - X` where `Y(X² + 1)` is invertible. -/
abbrev GeoChartW : Type := Localization.Away (geoWY * (geoWX ^ 2 + 1))

/-- The defining relation of `E` in its coordinate ring. -/
private theorem geo_coordE_rel :
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

/-- The defining relation `Y² = X³ - X` in the coordinate ring of the Weierstrass curve. -/
private theorem geo_coordW_rel : geoWY ^ 2 = geoWX ^ 3 - geoWX := by
  have heq : geoWeierstrass.toAffine.polynomial = X ^ 2 - C (X ^ 3 - X) := by
    simp [WeierstrassCurve.Affine.polynomial, geoWeierstrass]
    ring
  have h : (X ^ 2 - C (X ^ 3 - X) : ℚ[X][X]).eval₂
      (AdjoinRoot.of geoWeierstrass.toAffine.polynomial)
      (AdjoinRoot.root geoWeierstrass.toAffine.polynomial) = 0 := by
    rw [← heq]
    exact AdjoinRoot.eval₂_root _
  simp only [eval₂_sub, eval₂_C, eval₂_pow, eval₂_X, map_sub, map_pow] at h
  simp only [geoWX, geoWY]
  linear_combination h

/-- In the chart of `E`, `x r (1 - r) = 1 + r`. -/
private theorem geo_cert_chartE_param {R : Type*} [CommRing R] (M L v r : R)
    (hE : L ^ 2 - (M ^ 4 - 4 * M ^ 2 + 1) * L + M ^ 4 = 0) (hv : M * (M ^ 2 - 1) * v = 1)
    (hr : r = (M ^ 2 + L) * (M ^ 2 - 1) * v ^ 2) :
    M ^ 2 * r * (1 - r) = 1 + r := by
  subst hr
  linear_combination (-M^6*v^4 + 2*M^4*v^4 - M^2*v^4) * hE +
    (-L*M^7*v^3 + 3*L*M^5*v^3 - L*M^4*v^2 - 3*L*M^3*v^3 + 2*L*M^2*v^2 + L*M*v^3 - L*v^2 + M^3*v
      - M*v + 1) * hv

/-- In the chart of `E`, `x² r² = L`. -/
private theorem geo_cert_chartE_long {R : Type*} [CommRing R] (M L v r : R)
    (hE : L ^ 2 - (M ^ 4 - 4 * M ^ 2 + 1) * L + M ^ 4 = 0) (hv : M * (M ^ 2 - 1) * v = 1)
    (hr : r = (M ^ 2 + L) * (M ^ 2 - 1) * v ^ 2) :
    M ^ 4 * r ^ 2 = L := by
  subst hr
  linear_combination (M^8*v^4 - 2*M^6*v^4 + M^4*v^4) * hE +
    (L*M^9*v^3 - 3*L*M^7*v^3 + L*M^6*v^2 + 3*L*M^5*v^3 - 2*L*M^4*v^2 - L*M^3*v^3 + L*M^3*v
      + L*M^2*v^2 - L*M*v + L) * hv

/-- In the chart of `E`, an explicit inverse of `r`. -/
private theorem geo_cert_chartE_inv_r {R : Type*} [CommRing R] (M L v r : R)
    (hE : L ^ 2 - (M ^ 4 - 4 * M ^ 2 + 1) * L + M ^ 4 = 0) (hv : M * (M ^ 2 - 1) * v = 1)
    (hr : r = (M ^ 2 + L) * (M ^ 2 - 1) * v ^ 2) :
    r * ((M ^ 4 - 3 * M ^ 2 + 1 - L) * M * v) = 1 := by
  subst hr
  linear_combination (-M^3*v^3 + M*v^3) * hE +
    (M^6*v^2 - 2*M^4*v^2 + M^3*v + M^2*v^2 - M*v + 1) * hv

/-- In the chart of `E`, an explicit inverse of `1 - r` (up to `2`). -/
private theorem geo_cert_chartE_inv_one_sub_r {R : Type*} [CommRing R] (M L v r : R)
    (hE : L ^ 2 - (M ^ 4 - 4 * M ^ 2 + 1) * L + M ^ 4 = 0) (hv : M * (M ^ 2 - 1) * v = 1)
    (hr : r = (M ^ 2 + L) * (M ^ 2 - 1) * v ^ 2) :
    (1 - r) * ((L + 2 * M ^ 2 - 1) * M * v) = 2 := by
  subst hr
  linear_combination (-M^3*v^3 + M*v^3) * hE +
    (-L*M^4*v^2 + L*M^2*v^2 - L*M*v - M^4*v^2 + M^2*v^2 - M*v + 2) * hv

/-- In the chart of `E`, an explicit inverse of `r² + 1` (up to `2`). -/
private theorem geo_cert_chartE_inv_sq_add_one {R : Type*} [CommRing R] (M L v r : R)
    (hE : L ^ 2 - (M ^ 4 - 4 * M ^ 2 + 1) * L + M ^ 4 = 0) (hv : M * (M ^ 2 - 1) * v = 1)
    (hr : r = (M ^ 2 + L) * (M ^ 2 - 1) * v ^ 2) :
    (r ^ 2 + 1) * (M * v * ((M ^ 4 - 3 * M ^ 2 + 1 - L) * M * v) * ((L + 2 * M ^ 2
      - 1) * M * v)) = 2 := by
  subst hr
  linear_combination (-L^2*M^7*v^7 + 2*L^2*M^5*v^7 - L^2*M^3*v^7 - 3*L*M^9*v^7 + 7*L*M^7*v^7
      - 5*L*M^5*v^7 + L*M^3*v^7 - M^15*v^7 + 5*M^13*v^7 - 12*M^11*v^7 + 15*M^9*v^7 - 9*M^7*v^7
      + 2*M^5*v^7) * hE +
    (L^2*M^12*v^6 - 3*L^2*M^10*v^6 + L^2*M^9*v^5 + 3*L^2*M^8*v^6 - 2*L^2*M^7*v^5 - L^2*M^6*v^6
      + L^2*M^6*v^4 + L^2*M^5*v^5 - L^2*M^4*v^4 + L^2*M^3*v^3 - L*M^16*v^6 + 8*L*M^14*v^6
      - L*M^13*v^5 - 20*L*M^12*v^6 + 7*L*M^11*v^5 + 22*L*M^10*v^6 - L*M^10*v^4 - 13*L*M^9*v^5
      - 11*L*M^8*v^6 + 6*L*M^8*v^4 + 9*L*M^7*v^5 - L*M^7*v^3 + 2*L*M^6*v^6 - 7*L*M^6*v^4
      - 2*L*M^5*v^5 + 5*L*M^5*v^3 + 2*L*M^4*v^4 - 2*L*M^3*v^3 + M^16*v^6 - 2*M^14*v^6 + M^13*v^5
      - M^12*v^6 - M^11*v^5 + 5*M^10*v^6 + M^10*v^4 - 2*M^9*v^5 - 4*M^8*v^6 + 3*M^7*v^5 + M^7*v^3
      + M^6*v^6 - 2*M^6*v^4 + 2*M^6*v^2 - M^5*v^5 + M^5*v^3 + M^4*v^4 - 4*M^4*v^2 - M^3*v^3
      + 2*M^3*v + 2*M^2*v^2 - 2*M*v + 2) * hv

/-- In the chart of `W`, the images of `M` and `L` satisfy `E`. -/
private theorem geo_cert_chartW_rel {R : Type*} [CommRing R] (x y w m l : R)
    (hW : y ^ 2 = x ^ 3 - x) (hw : y * (x ^ 2 + 1) * w = 1) (hm : m = -(x - 1) * (x ^ 2 + 1) * w)
    (hl : l = x ^ 2 * (x - 1) ^ 4 * (x ^ 2 + 1) ^ 4 * w ^ 4) :
    l ^ 2 - (m ^ 4 - 4 * m ^ 2 + 1) * l + m ^ 4 = 0 := by
  subst hm hl
  linear_combination (-w^8*x^25 + 8*w^8*x^24 - 36*w^8*x^23 - w^8*x^22*y^2 + 120*w^8*x^22
      + 4*w^8*x^21*y^2 - 322*w^8*x^21 - 13*w^8*x^20*y^2 + 728*w^8*x^20 + 32*w^8*x^19*y^2
      - 1428*w^8*x^19 - 63*w^8*x^18*y^2 + 2472*w^8*x^18 + 108*w^8*x^17*y^2 - 3823*w^8*x^17
      - 155*w^8*x^16*y^2 + 5328*w^8*x^16 + 192*w^8*x^15*y^2 - 6728*w^8*x^15 - 202*w^8*x^14*y^2
      + 7728*w^8*x^14 + 168*w^8*x^13*y^2 - 8092*w^8*x^13 - 98*w^8*x^12*y^2 + 7728*w^8*x^12
      - 6728*w^8*x^11 + 98*w^8*x^10*y^2 + 5328*w^8*x^10 - 168*w^8*x^9*y^2 - 3823*w^8*x^9
      + 202*w^8*x^8*y^2 + 2472*w^8*x^8 - 192*w^8*x^7*y^2 - 1428*w^8*x^7 + 155*w^8*x^6*y^2
      + 728*w^8*x^6 - 108*w^8*x^5*y^2 - 322*w^8*x^5 + 63*w^8*x^4*y^2 + 120*w^8*x^4
      - 32*w^8*x^3*y^2 - 36*w^8*x^3 + 13*w^8*x^2*y^2 + 8*w^8*x^2 - 4*w^8*x*y^2 - w^8*x
      + w^8*y^2) * hW +
    (-4*w^7*x^22*y + 24*w^7*x^21*y + w^7*x^20*y^3 - 88*w^7*x^20*y - 4*w^7*x^19*y^3
      + 248*w^7*x^19*y + 12*w^7*x^18*y^3 - 564*w^7*x^18*y - 28*w^7*x^17*y^3 + 1088*w^7*x^17*y
      + 51*w^7*x^16*y^3 - 1824*w^7*x^16*y - 80*w^7*x^15*y^3 + 2688*w^7*x^15*y + 104*w^7*x^14*y^3
      - 3528*w^7*x^14*y - 112*w^7*x^13*y^3 + 4144*w^7*x^13*y + 98*w^7*x^12*y^3 - 4368*w^7*x^12*y
      - 56*w^7*x^11*y^3 + 4144*w^7*x^11*y - 3528*w^7*x^10*y + 56*w^7*x^9*y^3 + 2688*w^7*x^9*y
      - 98*w^7*x^8*y^3 - 1824*w^7*x^8*y + 112*w^7*x^7*y^3 + 1088*w^7*x^7*y - 104*w^7*x^6*y^3
      - 564*w^7*x^6*y + 80*w^7*x^5*y^3 + 248*w^7*x^5*y - 51*w^7*x^4*y^3 - 88*w^7*x^4*y
      + 28*w^7*x^3*y^3 + 24*w^7*x^3*y - 12*w^7*x^2*y^3 - 4*w^7*x^2*y + 4*w^7*x*y^3 - w^7*y^3
      - 4*w^6*x^20 + 24*w^6*x^19 + w^6*x^18*y^2 - 84*w^6*x^18 - 4*w^6*x^17*y^2 + 224*w^6*x^17
      + 11*w^6*x^16*y^2 - 480*w^6*x^16 - 24*w^6*x^15*y^2 + 864*w^6*x^15 + 40*w^6*x^14*y^2
      - 1344*w^6*x^14 - 56*w^6*x^13*y^2 + 1824*w^6*x^13 + 64*w^6*x^12*y^2 - 2184*w^6*x^12
      - 56*w^6*x^11*y^2 + 2320*w^6*x^11 + 34*w^6*x^10*y^2 - 2184*w^6*x^10 + 1824*w^6*x^9
      - 34*w^6*x^8*y^2 - 1344*w^6*x^8 + 56*w^6*x^7*y^2 + 864*w^6*x^7 - 64*w^6*x^6*y^2
      - 480*w^6*x^6 + 56*w^6*x^5*y^2 + 224*w^6*x^5 - 40*w^6*x^4*y^2 - 84*w^6*x^4 + 24*w^6*x^3*y^2
      + 24*w^6*x^3 - 11*w^6*x^2*y^2 - 4*w^6*x^2 + 4*w^6*x*y^2 - w^6*y^2 + w^5*x^16*y
      - 4*w^5*x^15*y + 10*w^5*x^14*y - 20*w^5*x^13*y + 30*w^5*x^12*y - 36*w^5*x^11*y
      + 34*w^5*x^10*y - 20*w^5*x^9*y + 20*w^5*x^7*y - 34*w^5*x^6*y + 36*w^5*x^5*y - 30*w^5*x^4*y
      + 20*w^5*x^3*y - 10*w^5*x^2*y + 4*w^5*x*y - w^5*y + w^4*x^14 - 4*w^4*x^13 + 9*w^4*x^12
      - 16*w^4*x^11 + 21*w^4*x^10 - 20*w^4*x^9 + 13*w^4*x^8 - 13*w^4*x^6 + 20*w^4*x^5 - 21*w^4*x^4
      + 16*w^4*x^3 - 9*w^4*x^2 + 4*w^4*x - w^4) * hw

/-- In the chart of `W`, an explicit inverse of `M(M² - 1)`. -/
private theorem geo_cert_chartW_inv {R : Type*} [CommRing R] (x y w m : R)
    (hW : y ^ 2 = x ^ 3 - x) (hw : y * (x ^ 2 + 1) * w = 1)
    (hm : m = -(x - 1) * (x ^ 2 + 1) * w) :
    m * (m ^ 2 - 1) * (x ^ 2 * (x + 1) ^ 2 * (x ^ 2 + 1) * y * w ^ 2) = 1 := by
  subst hm
  linear_combination (w^5*x^12*y - w^5*x^11*y - w^5*x^10*y^3 + 3*w^5*x^10*y - 3*w^5*x^9*y
      - 5*w^5*x^8*y^3 + 2*w^5*x^8*y - 2*w^5*x^7*y - 10*w^5*x^6*y^3 - 2*w^5*x^6*y + 2*w^5*x^5*y
      - 10*w^5*x^4*y^3 - 3*w^5*x^4*y + 3*w^5*x^3*y - 5*w^5*x^2*y^3 - w^5*x^2*y + w^5*x*y
      - w^5*y^3) * hW +
    (-w^4*x^11*y^2 - w^4*x^10*y^2 - 2*w^4*x^9*y^2 + w^4*x^8*y^4 - 2*w^4*x^8*y^2 + 4*w^4*x^6*y^4
      + 2*w^4*x^5*y^2 + 6*w^4*x^4*y^4 + 2*w^4*x^4*y^2 + w^4*x^3*y^2 + 4*w^4*x^2*y^4 + w^4*x^2*y^2
      + w^4*y^4 - w^3*x^9*y - w^3*x^8*y - w^3*x^7*y + w^3*x^6*y^3 - w^3*x^6*y + w^3*x^5*y
      + 3*w^3*x^4*y^3 + w^3*x^4*y + w^3*x^3*y + 3*w^3*x^2*y^3 + w^3*x^2*y + w^3*y^3 + w^2*x^4*y^2
      + 2*w^2*x^2*y^2 + w^2*y^2 + w*x^2*y + w*y + 1) * hw

/-- In the chart of `W`, the image of `r` is `-X` after clearing denominators. -/
private theorem geo_cert_chartW_param {R : Type*} [CommRing R] (x y w m l : R)
    (hW : y ^ 2 = x ^ 3 - x) (hw : y * (x ^ 2 + 1) * w = 1) (hm : m = -(x - 1) * (x ^ 2 + 1) * w)
    (hl : l = x ^ 2 * (x - 1) ^ 4 * (x ^ 2 + 1) ^ 4 * w ^ 4) :
    -((m ^ 2 + l) * (m ^ 2 - 1)) = (m * (m ^ 2 - 1)) ^ 2 * x := by
  subst hm hl
  linear_combination (w^6*x^17 - 5*w^6*x^16 - w^6*x^15*y^2 + 16*w^6*x^15 + 3*w^6*x^14*y^2
      - 40*w^6*x^14 - 9*w^6*x^13*y^2 + 80*w^6*x^13 + 19*w^6*x^12*y^2 - 136*w^6*x^12
      - 33*w^6*x^11*y^2 + 200*w^6*x^11 + 51*w^6*x^10*y^2 - 256*w^6*x^10 - 65*w^6*x^9*y^2
      + 290*w^6*x^9 + 75*w^6*x^8*y^2 - 290*w^6*x^8 - 75*w^6*x^7*y^2 + 256*w^6*x^7 + 65*w^6*x^6*y^2
      - 200*w^6*x^6 - 51*w^6*x^5*y^2 + 136*w^6*x^5 + 33*w^6*x^4*y^2 - 80*w^6*x^4 - 19*w^6*x^3*y^2
      + 40*w^6*x^3 + 9*w^6*x^2*y^2 - 16*w^6*x^2 - 3*w^6*x*y^2 + 5*w^6*x + w^6*y^2 - w^6) * hW +
    (-w^5*x^16*y + 2*w^5*x^15*y - 2*w^5*x^14*y + w^5*x^13*y^3 - 2*w^5*x^13*y - 3*w^5*x^12*y^3
      + 18*w^5*x^12*y + 8*w^5*x^11*y^3 - 46*w^5*x^11*y - 16*w^5*x^10*y^3 + 86*w^5*x^10*y
      + 25*w^5*x^9*y^3 - 130*w^5*x^9*y - 35*w^5*x^8*y^3 + 160*w^5*x^8*y + 40*w^5*x^7*y^3
      - 170*w^5*x^7*y - 40*w^5*x^6*y^3 + 154*w^5*x^6*y + 35*w^5*x^5*y^3 - 118*w^5*x^5*y
      - 25*w^5*x^4*y^3 + 78*w^5*x^4*y + 16*w^5*x^3*y^3 - 42*w^5*x^3*y - 8*w^5*x^2*y^3
      + 18*w^5*x^2*y + 3*w^5*x*y^3 - 6*w^5*x*y - w^5*y^3 + w^5*y - w^4*x^14 + 2*w^4*x^13
      - w^4*x^12 + w^4*x^11*y^2 - 4*w^4*x^11 - 3*w^4*x^10*y^2 + 19*w^4*x^10 + 7*w^4*x^9*y^2
      - 42*w^4*x^9 - 13*w^4*x^8*y^2 + 67*w^4*x^8 + 18*w^4*x^7*y^2 - 88*w^4*x^7 - 22*w^4*x^6*y^2
      + 93*w^4*x^6 + 22*w^4*x^5*y^2 - 82*w^4*x^5 - 18*w^4*x^4*y^2 + 61*w^4*x^4 + 13*w^4*x^3*y^2
      - 36*w^4*x^3 - 7*w^4*x^2*y^2 + 17*w^4*x^2 + 3*w^4*x*y^2 - 6*w^4*x - w^4*y^2 + w^4
      + w^3*x^9*y - 3*w^3*x^8*y + 6*w^3*x^7*y - 10*w^3*x^6*y + 12*w^3*x^5*y - 12*w^3*x^4*y
      + 10*w^3*x^3*y - 6*w^3*x^2*y + 3*w^3*x*y - w^3*y + w^2*x^7 - 3*w^2*x^6 + 5*w^2*x^5
      - 7*w^2*x^4 + 7*w^2*x^3 - 5*w^2*x^2 + 3*w^2*x - w^2) * hw

/-- `E` over `ℚ` written out as a bivariate polynomial. -/
private theorem geo_extraFactorℚ_eq :
    geoExtraFactorℚ = X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) := by
  simp [geoExtraFactorℚ, extraFactor]

/-- The Weierstrass polynomial of `Y² = X³ - X`. -/
private theorem geo_weierstrass_polynomial_eq :
    geoWeierstrass.toAffine.polynomial = X ^ 2 - C (X ^ 3 - X) := by
  simp [WeierstrassCurve.Affine.polynomial, geoWeierstrass]
  ring

/-- The inverse of `M(M² - 1)` in the chart of `E`. -/
private def geoVE : GeoChartE := IsLocalization.Away.invSelf (geoMer * (geoMer ^ 2 - 1))

/-- `M` in the chart of `E`. -/
private def geoME : GeoChartE := algebraMap GeoCoordE GeoChartE geoMer

/-- `L` in the chart of `E`. -/
private def geoLE : GeoChartE := algebraMap GeoCoordE GeoChartE geoLong

/-- The parameter `r = (M² + L)/(M²(M² - 1))` in the chart of `E`. -/
private def geoRE : GeoChartE := (geoME ^ 2 + geoLE) * (geoME ^ 2 - 1) * geoVE ^ 2

/-- The image `M r (1 - r)` of `Y` in the chart of `E`. -/
private def geoYE : GeoChartE := geoME * geoRE * (1 - geoRE)

/-- The relation `E = 0` in the chart of `E`. -/
private theorem geo_chartE_rel :
    geoLE ^ 2 - (geoME ^ 4 - 4 * geoME ^ 2 + 1) * geoLE + geoME ^ 4 = 0 := by
  have h := congrArg (algebraMap GeoCoordE GeoChartE) geo_coordE_rel
  simpa only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat, map_zero, geoME,
    geoLE] using h

/-- `M(M² - 1) v = 1` in the chart of `E`. -/
private theorem geo_chartE_inv : geoME * (geoME ^ 2 - 1) * geoVE = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := GeoChartE) (geoMer * (geoMer ^ 2 - 1))
  simpa only [map_sub, map_mul, map_pow, map_one, geoME, geoVE] using h

/-- The inverse of `Y(X² + 1)` in the chart of `W`. -/
private def geoWW : GeoChartW := IsLocalization.Away.invSelf (geoWY * (geoWX ^ 2 + 1))

/-- `X` in the chart of `W`. -/
private def geoXC : GeoChartW := algebraMap _ GeoChartW geoWX

/-- `Y` in the chart of `W`. -/
private def geoYC : GeoChartW := algebraMap _ GeoChartW geoWY

/-- The image `-(X - 1)/Y` of `M` in the chart of `W`. -/
private def geoMC : GeoChartW := -(geoXC - 1) * (geoXC ^ 2 + 1) * geoWW

/-- The image `((1 - X)/(1 + X))²` of `L` in the chart of `W`. -/
private def geoLC : GeoChartW := geoXC ^ 2 * (geoXC - 1) ^ 4 * (geoXC ^ 2 + 1) ^ 4 * geoWW ^ 4

/-- The relation `Y² = X³ - X` in the chart of `W`. -/
private theorem geo_chartW_rel : geoYC ^ 2 = geoXC ^ 3 - geoXC := by
  have h := congrArg (algebraMap _ GeoChartW) geo_coordW_rel
  simpa only [map_sub, map_pow, geoXC, geoYC] using h

/-- `Y(X² + 1) w = 1` in the chart of `W`. -/
private theorem geo_chartW_inv : geoYC * (geoXC ^ 2 + 1) * geoWW = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := GeoChartW) (geoWY * (geoWX ^ 2 + 1))
  simpa only [map_add, map_mul, map_pow, map_one, geoXC, geoYC, geoWW] using h

/-- `2` is a unit in any `ℚ`-algebra. -/
private theorem geo_isUnit_two {A : Type*} [CommRing A] [Algebra ℚ A] : IsUnit (2 : A) := by
  have h := (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : ℚ) ≠ 0)).map (algebraMap ℚ A)
  simpa only [map_ofNat] using h

/-- The map `ℚ[M] → GeoChartW`, `M ↦ -(X - 1)/Y`. -/
private def geoPhi0 : ℚ[X] →+* GeoChartW := Polynomial.eval₂RingHom (algebraMap ℚ GeoChartW) geoMC

/-- The images of `M` and `L` in the chart of `W` satisfy `E`. -/
private theorem geoPhi_root : geoExtraFactorℚ.eval₂ geoPhi0 geoLC = 0 := by
  rw [geo_extraFactorℚ_eq]
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, geoPhi0,
    coe_eval₂RingHom, eval₂_one, eval₂_ofNat]
  exact geo_cert_chartW_rel geoXC geoYC geoWW geoMC geoLC geo_chartW_rel geo_chartW_inv rfl rfl

/-- The ring map `ℚ[M, L]/(E) → GeoChartW`. -/
private def geoPhi : GeoCoordE →+* GeoChartW := AdjoinRoot.lift geoPhi0 geoLC geoPhi_root

/-- `geoPhi` sends `M` to `-(X - 1)/Y`. -/
private theorem geoPhi_mer : geoPhi geoMer = geoMC := by
  simp [geoPhi, geoMer, AdjoinRoot.lift_of, geoPhi0]

/-- `geoPhi` sends `L` to `((1 - X)/(1 + X))²`. -/
private theorem geoPhi_long : geoPhi geoLong = geoLC := by
  simp [geoPhi, geoLong, AdjoinRoot.lift_root]

/-- `geoPhi` sends `M(M² - 1)` to a unit. -/
private theorem geoPhi_isUnit : IsUnit (geoPhi (geoMer * (geoMer ^ 2 - 1))) := by
  rw [map_mul, map_sub, map_pow, map_one, geoPhi_mer]
  exact IsUnit.of_mul_eq_one _
    (geo_cert_chartW_inv geoXC geoYC geoWW geoMC geo_chartW_rel geo_chartW_inv rfl)

/-- The ring map of charts `GeoChartE → GeoChartW`. -/
private def geoPhiC : GeoChartE →+* GeoChartW := IsLocalization.Away.lift _ geoPhi_isUnit

/-- The map `ℚ[X] → GeoChartE`, `X ↦ -r`. -/
private def geoPsi0 : ℚ[X] →+* GeoChartE :=
  Polynomial.eval₂RingHom (algebraMap ℚ GeoChartE) (-geoRE)

/-- The images of `X` and `Y` in the chart of `E` satisfy `Y² = X³ - X`. -/
private theorem geoPsi_root : geoWeierstrass.toAffine.polynomial.eval₂ geoPsi0 geoYE = 0 := by
  rw [geo_weierstrass_polynomial_eq]
  simp only [eval₂_sub, eval₂_C, eval₂_pow, eval₂_X, geoPsi0, coe_eval₂RingHom]
  have h5 := geo_cert_chartE_param geoME geoLE geoVE geoRE geo_chartE_rel geo_chartE_inv rfl
  simp only [geoYE]
  linear_combination (geoRE * (1 - geoRE)) * h5

/-- The ring map `ℚ[X, Y]/(Y² - X³ + X) → GeoChartE`. -/
private def geoPsi : geoWeierstrass.toAffine.CoordinateRing →+* GeoChartE :=
  AdjoinRoot.lift geoPsi0 geoYE geoPsi_root

/-- `geoPsi` sends `X` to `-r`. -/
private theorem geoPsi_X : geoPsi geoWX = -geoRE := by
  simp [geoPsi, geoWX, AdjoinRoot.lift_of, geoPsi0]

/-- `geoPsi` sends `Y` to `M r (1 - r)`. -/
private theorem geoPsi_Y : geoPsi geoWY = geoYE := by
  simp [geoPsi, geoWY, AdjoinRoot.lift_root]

/-- `geoPsi` sends `Y(X² + 1)` to a unit. -/
private theorem geoPsi_isUnit : IsUnit (geoPsi (geoWY * (geoWX ^ 2 + 1))) := by
  have hv := geo_chartE_inv
  have hM : IsUnit geoME := IsUnit.of_mul_eq_one ((geoME ^ 2 - 1) * geoVE) (by
    linear_combination hv)
  have hr : IsUnit geoRE := IsUnit.of_mul_eq_one _
    (geo_cert_chartE_inv_r geoME geoLE geoVE geoRE geo_chartE_rel hv rfl)
  have h1r : IsUnit (1 - geoRE) := isUnit_of_mul_isUnit_left
    ((geo_cert_chartE_inv_one_sub_r geoME geoLE geoVE geoRE geo_chartE_rel hv rfl).symm ▸
      geo_isUnit_two)
  have hsq : IsUnit (geoRE ^ 2 + 1) := isUnit_of_mul_isUnit_left
    ((geo_cert_chartE_inv_sq_add_one geoME geoLE geoVE geoRE geo_chartE_rel hv rfl).symm ▸
      geo_isUnit_two)
  rw [map_mul, map_add, map_pow, map_one, geoPsi_X, geoPsi_Y, neg_sq]
  exact ((hM.mul hr).mul h1r).mul hsq

/-- The ring map of charts `GeoChartW → GeoChartE`. -/
private def geoPsiC : GeoChartW →+* GeoChartE := IsLocalization.Away.lift _ geoPsi_isUnit

/-- `geoPhiC (M) = -(X - 1)/Y`. -/
private theorem geoPhiC_mer : geoPhiC geoME = geoMC := by
  rw [geoME, geoPhiC, IsLocalization.Away.lift_eq, geoPhi_mer]

/-- `geoPhiC (L) = ((1 - X)/(1 + X))²`. -/
private theorem geoPhiC_long : geoPhiC geoLE = geoLC := by
  rw [geoLE, geoPhiC, IsLocalization.Away.lift_eq, geoPhi_long]

/-- `geoPhiC` respects the inverse of `M(M² - 1)`. -/
private theorem geoPhiC_inv : geoMC * (geoMC ^ 2 - 1) * geoPhiC geoVE = 1 := by
  have h := congrArg geoPhiC geo_chartE_inv
  simpa only [map_mul, map_sub, map_pow, map_one, geoPhiC_mer] using h

/-- `geoPsiC (X) = -r`. -/
private theorem geoPsiC_X : geoPsiC geoXC = -geoRE := by
  rw [geoXC, geoPsiC, IsLocalization.Away.lift_eq, geoPsi_X]

/-- `geoPsiC (Y) = M r (1 - r)`. -/
private theorem geoPsiC_Y : geoPsiC geoYC = geoYE := by
  rw [geoYC, geoPsiC, IsLocalization.Away.lift_eq, geoPsi_Y]

/-- `geoPsiC` respects the inverse of `Y(X² + 1)`. -/
private theorem geoPsiC_inv : geoYE * ((-geoRE) ^ 2 + 1) * geoPsiC geoWW = 1 := by
  have h := congrArg geoPsiC geo_chartW_inv
  simpa only [map_mul, map_add, map_pow, map_one, geoPsiC_X, geoPsiC_Y] using h

/-- The image of `r` under `geoPhiC` is `-X`. -/
private theorem geoPhiC_r : geoPhiC geoRE = -geoXC := by
  have h := geoPhiC_inv
  have h3 :=
    geo_cert_chartW_param geoXC geoYC geoWW geoMC geoLC geo_chartW_rel geo_chartW_inv rfl rfl
  simp only [geoRE, map_mul, map_add, map_sub, map_pow, map_one, geoPhiC_mer, geoPhiC_long]
  linear_combination -geoPhiC geoVE ^ 2 * h3 -
    geoXC * (geoMC * (geoMC ^ 2 - 1) * geoPhiC geoVE + 1) * h

/-- Two ring maps out of `ℚ[X]` agree on constants. -/
private theorem geo_ringHom_C_eq {S : Type*} [Semiring S] (f g : ℚ[X] →+* S) (a : ℚ) :
    f (C a) = g (C a) :=
  DFunLike.congr_fun (RingHom.ext_rat (f.comp C) (g.comp C)) a

/-- The image of `L` under the chart composite, as a ring identity. -/
private theorem geo_chartE_long_aux {R : Type*} [CommRing R] (M L r w : R)
    (h5 : M ^ 2 * r * (1 - r) = 1 + r) (h4 : M ^ 4 * r ^ 2 = L)
    (hw : M * r * (1 - r) * ((-r) ^ 2 + 1) * w = 1) :
    (-r) ^ 2 * (-r - 1) ^ 4 * ((-r) ^ 2 + 1) ^ 4 * w ^ 4 = L := by
  linear_combination
    -r ^ 2 * ((r + 1) ^ 3 + (r + 1) ^ 2 * (M ^ 2 * r * (1 - r)) +
      (r + 1) * (M ^ 2 * r * (1 - r)) ^ 2 + (M ^ 2 * r * (1 - r)) ^ 3) *
      ((-r) ^ 2 + 1) ^ 4 * w ^ 4 * h5 +
    r ^ 2 * M ^ 4 * ((M * r * (1 - r) * ((-r) ^ 2 + 1) * w) ^ 3 +
      (M * r * (1 - r) * ((-r) ^ 2 + 1) * w) ^ 2 + M * r * (1 - r) * ((-r) ^ 2 + 1) * w + 1) * hw +
    h4

/-- `geoPsiC ∘ geoPhiC = id`. -/
private theorem geoPsiC_comp_geoPhiC : geoPsiC.comp geoPhiC = RingHom.id GeoChartE := by
  have hw := geoPsiC_inv
  have h5 := geo_cert_chartE_param geoME geoLE geoVE geoRE geo_chartE_rel geo_chartE_inv rfl
  have h4 := geo_cert_chartE_long geoME geoLE geoVE geoRE geo_chartE_rel geo_chartE_inv rfl
  rw [geoYE] at hw
  apply IsLocalization.ringHom_ext (Submonoid.powers (geoMer * (geoMer ^ 2 - 1)))
  apply AdjoinRoot.ringHom_ext
  · refine Polynomial.ringHom_ext (fun a ↦ geo_ringHom_C_eq _ _ a) ?_
    show geoPsiC (geoPhiC geoME) = geoME
    simp only [geoPhiC_mer, geoMC, map_mul, map_neg, map_sub, map_add, map_pow, map_one,
      geoPsiC_X]
    linear_combination geoME * hw - ((-geoRE) ^ 2 + 1) * geoPsiC geoWW * h5
  · show geoPsiC (geoPhiC geoLE) = geoLE
    rw [geoPhiC_long, geoLC]
    simp only [map_mul, map_sub, map_add, map_pow, map_one, geoPsiC_X]
    exact geo_chartE_long_aux geoME geoLE geoRE _ h5 h4 hw

/-- `geoPhiC ∘ geoPsiC = id`. -/
private theorem geoPhiC_comp_geoPsiC : geoPhiC.comp geoPsiC = RingHom.id GeoChartW := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (geoWY * (geoWX ^ 2 + 1)))
  apply AdjoinRoot.ringHom_ext
  · refine Polynomial.ringHom_ext (fun a ↦ geo_ringHom_C_eq _ _ a) ?_
    show geoPhiC (geoPsiC geoXC) = geoXC
    rw [geoPsiC_X, map_neg, geoPhiC_r, neg_neg]
  · show geoPhiC (geoPsiC geoYC) = geoYC
    simp only [geoPsiC_Y, geoYE, map_mul, map_sub, map_one, geoPhiC_mer, geoPhiC_r, geoMC]
    linear_combination -(geoXC ^ 2 + 1) * geoWW * geo_chartW_rel + geoYC * geo_chartW_inv

/-- The isomorphism of charts. -/
private def geoChartEquiv : GeoChartE ≃+* GeoChartW :=
  RingEquiv.ofRingHom geoPhiC geoPsiC geoPhiC_comp_geoPsiC geoPsiC_comp_geoPhiC

/-- The chart isomorphism sends `M` to `Y/(-X(1 + X))`. -/
private theorem geoChartEquiv_mer : geoChartEquiv geoME * (-(geoXC * (1 + geoXC))) = geoYC := by
  show geoPhiC geoME * _ = _
  rw [geoPhiC_mer, geoMC]
  linear_combination -(geoXC ^ 2 + 1) * geoWW * geo_chartW_rel + geoYC * geo_chartW_inv

/-- The chart isomorphism sends `L` to `((1 - X)/(1 + X))²`. -/
private theorem geoChartEquiv_long :
    geoChartEquiv geoLE * (1 + geoXC) ^ 2 = (1 - geoXC) ^ 2 := by
  show geoPhiC geoLE * _ = _
  rw [geoPhiC_long, geoLC]
  linear_combination -(geoXC - 1) ^ 2 * (geoXC ^ 3 - geoXC + geoYC ^ 2) * (geoXC ^ 2 + 1) ^ 4 *
      geoWW ^ 4 * geo_chartW_rel + (geoXC - 1) ^ 2 * ((geoYC * (geoXC ^ 2 + 1) * geoWW) ^ 3 +
      (geoYC * (geoXC ^ 2 + 1) * geoWW) ^ 2 + geoYC * (geoXC ^ 2 + 1) * geoWW + 1) * geo_chartW_inv

/-- `X(X² - 1) ≠ 0` in `ℚ[X]`. -/
private theorem geo_X_mul_X_sq_sub_one_ne_zero : (X * (X ^ 2 - 1) : ℚ[X]) ≠ 0 := by
  intro h
  have h2 := congrArg (eval 2) h
  norm_num at h2

/-- `M(M² - 1) ≠ 0` in the coordinate ring of `E`, so its powers are non-zero-divisors. -/
private theorem geo_chartE_le_nonZeroDivisors :
    Submonoid.powers (geoMer * (geoMer ^ 2 - 1)) ≤ nonZeroDivisors GeoCoordE := by
  apply powers_le_nonZeroDivisors_of_noZeroDivisors
  have hdeg : geoExtraFactorℚ.degree = 2 := by
    rw [geo_extraFactorℚ_eq]
    compute_degree!
  have hinj := AdjoinRoot.of.injective_of_degree_ne_zero (f := geoExtraFactorℚ)
    (by rw [hdeg]; decide)
  have heq : geoMer * (geoMer ^ 2 - 1) = AdjoinRoot.of geoExtraFactorℚ (X * (X ^ 2 - 1)) := by
    simp [geoMer]
  rw [heq]
  exact fun h ↦ geo_X_mul_X_sq_sub_one_ne_zero (hinj (h.trans (map_zero _).symm))

/-- `Y(X² + 1) ≠ 0` in the coordinate ring of `W`, so its powers are non-zero-divisors. -/
private theorem geo_chartW_le_nonZeroDivisors :
    Submonoid.powers (geoWY * (geoWX ^ 2 + 1)) ≤
      nonZeroDivisors geoWeierstrass.toAffine.CoordinateRing := by
  apply powers_le_nonZeroDivisors_of_noZeroDivisors
  have hinj := AdjoinRoot.of.injective_of_degree_ne_zero
    (f := geoWeierstrass.toAffine.polynomial)
    (by rw [WeierstrassCurve.Affine.degree_polynomial]; decide)
  have hY : geoWY ≠ 0 := by
    intro h
    have h2 : AdjoinRoot.of geoWeierstrass.toAffine.polynomial (X * (X ^ 2 - 1)) = 0 := by
      have h1 := geo_coordW_rel
      rw [h] at h1
      have h3 : geoWX * (geoWX ^ 2 - 1) = 0 := by linear_combination -h1
      rw [map_mul, map_sub, map_pow, map_one]
      exact h3
    exact geo_X_mul_X_sq_sub_one_ne_zero (hinj (h2.trans (map_zero _).symm))
  have hX : geoWX ^ 2 + 1 ≠ 0 := by
    intro h
    have h2 : AdjoinRoot.of geoWeierstrass.toAffine.polynomial (X ^ 2 + 1) = 0 := by
      rw [map_add, map_pow, map_one]
      exact h
    have h3 := congrArg (eval 0) (hinj (h2.trans (map_zero _).symm))
    norm_num at h3
  exact mul_ne_zero hY hX

/-- The two charts are isomorphic: `M ↦ Y/(-X(1 + X))`, `L ↦ ((1 - X)/(1 + X))²`. -/
theorem geo_chart_equiv :
    ∃ e : GeoChartE ≃+* GeoChartW,
      e (algebraMap GeoCoordE GeoChartE geoMer) *
          (-(algebraMap _ GeoChartW geoWX * (1 + algebraMap _ GeoChartW geoWX))) =
        algebraMap _ GeoChartW geoWY ∧
      e (algebraMap GeoCoordE GeoChartE geoLong) * (1 + algebraMap _ GeoChartW geoWX) ^ 2 =
        (1 - algebraMap _ GeoChartW geoWX) ^ 2 :=
  ⟨geoChartEquiv, geoChartEquiv_mer, geoChartEquiv_long⟩

/-- The function field of `E` is the function field of `Y² = X³ - X`, by the same formulas; the
inverse sends `X ↦ -r` and `Y ↦ M r (1 - r)` with `r = (M² + L)/(M²(M² - 1))`. -/
theorem geo_functionField_equiv :
    ∃ e : GeoFunFieldE ≃+* geoWeierstrass.toAffine.FunctionField,
      e (algebraMap GeoCoordE GeoFunFieldE geoMer) *
          (-(algebraMap _ geoWeierstrass.toAffine.FunctionField geoWX *
            (1 + algebraMap _ geoWeierstrass.toAffine.FunctionField geoWX))) =
        algebraMap _ geoWeierstrass.toAffine.FunctionField geoWY ∧
      e (algebraMap GeoCoordE GeoFunFieldE geoLong) *
          (1 + algebraMap _ geoWeierstrass.toAffine.FunctionField geoWX) ^ 2 =
        (1 - algebraMap _ geoWeierstrass.toAffine.FunctionField geoWX) ^ 2 ∧
      e.symm (algebraMap _ _ geoWX) =
        -((algebraMap GeoCoordE GeoFunFieldE geoMer ^ 2 + algebraMap _ _ geoLong) /
          (algebraMap GeoCoordE GeoFunFieldE geoMer ^ 2 *
            (algebraMap GeoCoordE GeoFunFieldE geoMer ^ 2 - 1))) := by
  let _ : Algebra GeoChartE GeoFunFieldE :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ geo_chartE_le_nonZeroDivisors
  have : IsScalarTower GeoCoordE GeoChartE GeoFunFieldE :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ geo_chartE_le_nonZeroDivisors
  have : IsFractionRing GeoChartE GeoFunFieldE :=
    IsFractionRing.isFractionRing_of_isLocalization _ _ _ geo_chartE_le_nonZeroDivisors
  let _ : Algebra GeoChartW geoWeierstrass.toAffine.FunctionField :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ geo_chartW_le_nonZeroDivisors
  have : IsScalarTower geoWeierstrass.toAffine.CoordinateRing GeoChartW
      geoWeierstrass.toAffine.FunctionField :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ geo_chartW_le_nonZeroDivisors
  have : IsFractionRing GeoChartW geoWeierstrass.toAffine.FunctionField :=
    IsFractionRing.isFractionRing_of_isLocalization _ _ _ geo_chartW_le_nonZeroDivisors
  have hA (a : GeoCoordE) : algebraMap GeoCoordE GeoFunFieldE a =
      algebraMap GeoChartE GeoFunFieldE (algebraMap GeoCoordE GeoChartE a) :=
    IsScalarTower.algebraMap_apply _ _ _ a
  have hB (b : geoWeierstrass.toAffine.CoordinateRing) :
      algebraMap _ geoWeierstrass.toAffine.FunctionField b =
        algebraMap GeoChartW geoWeierstrass.toAffine.FunctionField
          (algebraMap _ GeoChartW b) :=
    IsScalarTower.algebraMap_apply _ _ _ b
  refine ⟨IsFractionRing.ringEquivOfRingEquiv geoChartEquiv, ?_, ?_, ?_⟩
  · have h := congrArg (algebraMap GeoChartW geoWeierstrass.toAffine.FunctionField)
      geoChartEquiv_mer
    simp only [map_mul, map_neg, map_add, map_one] at h
    rw [hA, IsFractionRing.ringEquivOfRingEquiv_algebraMap, hB, hB]
    exact h
  · have h := congrArg (algebraMap GeoChartW geoWeierstrass.toAffine.FunctionField)
      geoChartEquiv_long
    simp only [map_mul, map_sub, map_add, map_pow, map_one] at h
    rw [hA, IsFractionRing.ringEquivOfRingEquiv_algebraMap, hB]
    exact h
  · rw [IsFractionRing.ringEquivOfRingEquiv_symm, hB,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap, hA, hA]
    change algebraMap GeoChartE GeoFunFieldE (geoPsiC geoXC) = _
    have hv := congrArg (algebraMap GeoChartE GeoFunFieldE) geo_chartE_inv
    simp only [map_mul, map_sub, map_pow, map_one] at hv
    rw [geoPsiC_X, geoRE]
    simp only [map_neg, map_mul, map_add, map_sub, map_pow, map_one, geoME, geoLE] at hv ⊢
    set m := algebraMap GeoChartE GeoFunFieldE (algebraMap GeoCoordE GeoChartE geoMer)
    set l := algebraMap GeoChartE GeoFunFieldE (algebraMap GeoCoordE GeoChartE geoLong)
    set v := algebraMap GeoChartE GeoFunFieldE geoVE
    have hm : m ≠ 0 := fun h ↦ by simp [h] at hv
    have hm1 : m ^ 2 - 1 ≠ 0 := fun h ↦ by simp [h] at hv
    rw [neg_inj, eq_div_iff (mul_ne_zero (pow_ne_zero 2 hm) hm1)]
    linear_combination (m ^ 2 + l) * (m * (m ^ 2 - 1) * v + 1) * hv

end AJConjecture
