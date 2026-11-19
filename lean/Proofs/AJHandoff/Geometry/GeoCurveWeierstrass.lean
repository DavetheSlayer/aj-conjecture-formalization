import Mathlib
import AJHandoff.Geometry.GeoCurveParam

/-!
# The elliptic curve `Y² = X³ - X` and the birational map from `E` (G-CURVE)

`geoWeierstrass` is the short Weierstrass curve `Y² = X³ - X` over `ℚ`: discriminant `64`,
elliptic, `j = 1728`. On the smooth torus locus of `E` the map `(M, L) ↦ (X, Y) = (-r, M r(1 - r))`
lands on `Y² = X³ - X` with `Y ≠ 0`, `X² ≠ -1`, and is inverted by
`(X, Y) ↦ (M, L) = (Y/(-X(1 + X)), ((1 - X)/(1 + X))²)`. Both compositions are the identity on
these nonempty open sets.

Route. `Δ = -16(4a₄³ + 27a₆²) = 64`, `c₄ = -48a₄ = 48`, `j = c₄³/Δ = 1728` by `norm_num` after
unfolding. The point maps: `Y² = M²r²(1 - r)² = x r²(1 - r)² = r(1 - r)(1 + r) = X³ - X` with
`x = (1 + r)/(r(1 - r))` (`geo_curveR_spec`); the inverse uses `r = -X` and
`geo_mem_smoothTorusLocus_of_param`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The Weierstrass curve `Y² = X³ - X` over `ℚ`. -/
def geoWeierstrass : WeierstrassCurve ℚ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -1, a₆ := 0 }

/-- Its discriminant is `64`. -/
theorem geoWeierstrass_Δ : geoWeierstrass.Δ = 64 := by
  simp only [geoWeierstrass, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

/-- `Y² = X³ - X` is an elliptic curve over `ℚ`. -/
instance geoWeierstrass_isElliptic : geoWeierstrass.IsElliptic :=
  ⟨by rw [geoWeierstrass_Δ]; exact isUnit_iff_ne_zero.mpr (by norm_num)⟩

/-- `j(Y² = X³ - X) = 1728`. -/
theorem geoWeierstrass_j : geoWeierstrass.j = 1728 := by
  rw [WeierstrassCurve.j_eq, geoWeierstrass_Δ]
  simp only [geoWeierstrass, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  norm_num

/-- The affine equation of `geoWeierstrass` over `ℂ` is `Y² = X³ - X`. -/
theorem geoWeierstrass_equation_iff (X Y : ℂ) :
    (geoWeierstrass.baseChange ℂ).toAffine.Equation X Y ↔ Y ^ 2 = X ^ 3 - X := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [geoWeierstrass, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, map_neg,
    map_one]
  constructor <;> intro h <;> linear_combination h

/-- The map `(M, L) ↦ (X, Y) = (-r, M r (1 - r))`. -/
def geoToWeierstrass (p : ℂ × ℂ) : ℂ × ℂ :=
  (-geoCurveR p, p.1 * geoCurveR p * (1 - geoCurveR p))

/-- The map `(X, Y) ↦ (M, L) = (Y/(-X(1 + X)), ((1 - X)/(1 + X))²)`. -/
def geoFromWeierstrass (q : ℂ × ℂ) : ℂ × ℂ :=
  (q.2 / (-(q.1 * (1 + q.1))), ((1 - q.1) / (1 + q.1)) ^ 2)

/-- The open set `Y ≠ 0`, `X² ≠ -1` of `Y² = X³ - X` (the complement of the three points with
`Y = 0` and of the four points over the nodes). -/
def GeoWeierstrassOpen : Set (ℂ × ℂ) :=
  {q | q.2 ^ 2 = q.1 ^ 3 - q.1 ∧ q.2 ≠ 0 ∧ q.1 ^ 2 ≠ -1}

/-- `E` and `Y² = X³ - X` are birational: the two maps are mutually inverse bijections between
the smooth torus locus and `GeoWeierstrassOpen`. -/
theorem geo_weierstrass_birational :
    Set.BijOn geoToWeierstrass GeoSmoothTorusLocus GeoWeierstrassOpen ∧
      Set.InvOn geoFromWeierstrass geoToWeierstrass GeoSmoothTorusLocus GeoWeierstrassOpen := by
  have hmaps : Set.MapsTo geoToWeierstrass GeoSmoothTorusLocus GeoWeierstrassOpen := by
    intro p hp
    obtain ⟨h0, h1, -, hi, hX, -⟩ := geo_curveR_spec hp
    have hM0 : p.1 ≠ 0 := hp.2.1
    have h1' : 1 - geoCurveR p ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    refine ⟨?_, mul_ne_zero (mul_ne_zero hM0 h0) h1', fun h ↦ hi (by simpa [geoToWeierstrass]
      using h)⟩
    simp only [geoToWeierstrass]
    have hX' : p.1 ^ 2 * (geoCurveR p * (1 - geoCurveR p)) = 1 + geoCurveR p := by
      rw [hX]; unfold geoX; field_simp
    linear_combination geoCurveR p * (1 - geoCurveR p) * hX'
  have hleft : Set.LeftInvOn geoFromWeierstrass geoToWeierstrass GeoSmoothTorusLocus := by
    intro p hp
    obtain ⟨h0, h1, -, -, -, hL⟩ := geo_curveR_spec hp
    have h1' : 1 - geoCurveR p ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    obtain ⟨M, L⟩ := p
    simp only [geoFromWeierstrass, geoToWeierstrass, Prod.mk.injEq]
    simp only at hL ⊢
    generalize geoCurveR (M, L) = r at *
    subst hL
    refine ⟨?_, ?_⟩
    · rw [div_eq_iff (by simpa [← sub_eq_add_neg] using mul_ne_zero h0 h1')]
      ring
    · simp only [geoL, geoF, sub_neg_eq_add, ← sub_eq_add_neg]
  have hright : Set.RightInvOn geoFromWeierstrass geoToWeierstrass GeoWeierstrassOpen := by
    rintro ⟨X, Y⟩ ⟨hE, hY, hi⟩
    simp only at hE hY hi
    have hXY : X * (X - 1) * (X + 1) ≠ 0 := by
      rw [show X * (X - 1) * (X + 1) = Y ^ 2 by linear_combination -hE]
      exact pow_ne_zero 2 hY
    have hX0 : X ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hXY)
    have hX1 : X - 1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hXY)
    have hX2 : 1 + X ≠ 0 := by rw [add_comm]; exact right_ne_zero_of_mul hXY
    have hM : (Y / -(X * (1 + X))) ^ 2 = geoX (-X) := by
      unfold geoX
      rw [div_pow, div_eq_div_iff (pow_ne_zero 2 (neg_ne_zero.mpr (mul_ne_zero hX0 hX2)))
        (mul_ne_zero (neg_ne_zero.mpr hX0) (by rwa [sub_neg_eq_add]))]
      linear_combination (-X * (1 + X)) * hE
    obtain ⟨-, hr⟩ := geo_mem_smoothTorusLocus_of_param (neg_ne_zero.mpr hX0)
      (fun h ↦ hX2 (by linear_combination -h)) (fun h ↦ hX1 (by linear_combination -h))
      (by rwa [neg_sq]) hM
    have hL : ((1 - X) / (1 + X)) ^ 2 = geoL (-X) := by
      simp only [geoL, geoF, sub_neg_eq_add, ← sub_eq_add_neg]
    simp only [geoFromWeierstrass, geoToWeierstrass, hL, hr, Prod.mk.injEq]
    refine ⟨by ring, ?_⟩
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (neg_ne_zero.mpr (mul_ne_zero hX0 hX2))]
    ring
  have hmaps' : Set.MapsTo geoFromWeierstrass GeoWeierstrassOpen GeoSmoothTorusLocus := by
    rintro ⟨X, Y⟩ ⟨hE, hY, hi⟩
    simp only at hE hY hi
    have hXY : X * (X - 1) * (X + 1) ≠ 0 := by
      rw [show X * (X - 1) * (X + 1) = Y ^ 2 by linear_combination -hE]
      exact pow_ne_zero 2 hY
    have hX0 : X ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hXY)
    have hX1 : X - 1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hXY)
    have hX2 : 1 + X ≠ 0 := by rw [add_comm]; exact right_ne_zero_of_mul hXY
    have hM : (Y / -(X * (1 + X))) ^ 2 = geoX (-X) := by
      unfold geoX
      rw [div_pow, div_eq_div_iff (pow_ne_zero 2 (neg_ne_zero.mpr (mul_ne_zero hX0 hX2)))
        (mul_ne_zero (neg_ne_zero.mpr hX0) (by rwa [sub_neg_eq_add]))]
      linear_combination (-X * (1 + X)) * hE
    have hL : ((1 - X) / (1 + X)) ^ 2 = geoL (-X) := by
      simp only [geoL, geoF, sub_neg_eq_add, ← sub_eq_add_neg]
    simp only [geoFromWeierstrass, hL]
    exact (geo_mem_smoothTorusLocus_of_param (neg_ne_zero.mpr hX0)
      (fun h ↦ hX2 (by linear_combination -h)) (fun h ↦ hX1 (by linear_combination -h))
      (by rwa [neg_sq]) hM).1
  have hinv : Set.InvOn geoFromWeierstrass geoToWeierstrass GeoSmoothTorusLocus
      GeoWeierstrassOpen := ⟨hleft, hright⟩
  exact ⟨hinv.bijOn hmaps hmaps', hinv⟩

/-- Both open sets are nonempty (the point `r = 2`, `M² = x(2) = -3/2`). -/
theorem geo_weierstrassOpen_nonempty :
    GeoSmoothTorusLocus.Nonempty ∧ GeoWeierstrassOpen.Nonempty := by
  obtain ⟨M, hM⟩ := IsAlgClosed.exists_pow_nat_eq (geoX 2) (by norm_num : 0 < 2)
  have h := (geo_mem_smoothTorusLocus_of_param (r := 2) (M := M) two_ne_zero (by norm_num)
    (by norm_num) (by norm_num) hM).1
  exact ⟨⟨_, h⟩, ⟨_, (geo_weierstrass_birational.1.mapsTo h)⟩⟩

end AJConjecture
