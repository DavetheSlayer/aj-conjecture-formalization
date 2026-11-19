import Mathlib
import AJHandoff.Geometry.GeoKernelRatios
import AJHandoff.Geometry.GeoCurveParam

/-!
# The homogeneous channel `Q = -1` maps bijectively onto `E` (G-KERNEL)

On `Q = -1` (so `z = -y`) and `x ≠ 0`, `x² ≠ 1`, the formal critical equations of
`GeoKernelRatios` reduce to `T = y² + (1 - x)y + x = 0` (the second is `-(x + 1)T`), and the
outer shift is `L = x²(x - y)/(y(x + y))`. Every solution of `T = 0` avoids
`y ∈ {0, 1, x, -x, -1}` (where `T = x, 2, 2x, 2x², 2x`), so all denominators and dilogarithm
punctures are absent. The map `y ↦ L` is a bijection from `{T = 0}` onto
`{E_x(L) = L² - (x² - 4x + 1)L + x² = 0}`, with inverse `y = x(L + x²)/(x² + (2x - 1)L)` whose
denominator never vanishes on `E_x = 0` (`Res_L(E_x, d) = 2x³(x - 1)²`). Keeping the full
two-sheeted lift `M² = x`, a point `(M, L)` with `M ≠ 0`, `M⁴ ≠ 1` lies on `E` iff it has a
(unique) channel point; then `r = (M² + L)/(M²(M² - 1)) = 1/y`.

Route. Substitution: `T(y(L)) = 2x³E_x(L)/d²`, shift residual `-2Lx³E_x(L)/d²`, and
`Res_y(T, -Ly(x + y) + x²(x - y)) = 2x³E_x(L)` (checked exactly at three rational points); then
`field_simp`/`linear_combination`.
-/

noncomputable section

namespace AJConjecture

/-- The channel polynomial `T = y² + (1 - x)y + x`. -/
def geoChannelT (x y : ℂ) : ℂ := y ^ 2 + (1 - x) * y + x

/-- The outer shift on the channel, `L = x²(x - y)/(y(x + y))`. -/
def geoChannelL (x y : ℂ) : ℂ := x ^ 2 * (x - y) / (y * (x + y))

/-- The inverse `y = x(L + x²)/(x² + (2x - 1)L)`. -/
def geoChannelY (x L : ℂ) : ℂ := x * (L + x ^ 2) / (x ^ 2 + (2 * x - 1) * L)

/-- Solutions of `T = 0` avoid every puncture. -/
theorem geo_channelT_nondegenerate {x y : ℂ} (hx0 : x ≠ 0) (hx1 : x ^ 2 ≠ 1)
    (hT : geoChannelT x y = 0) :
    y ≠ 0 ∧ y ≠ 1 ∧ y ≠ x ∧ y ≠ -x ∧ y ≠ -1 := by
  unfold geoChannelT at hT
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · exact hx0 (by linear_combination hT)
  · exact two_ne_zero (α := ℂ) (by linear_combination hT)
  · exact hx0 (by linear_combination hT / 2)
  · exact pow_ne_zero 2 hx0 (by linear_combination hT / 2)
  · exact hx0 (by linear_combination hT / 2)

/-- On `Q = -1`, `z = -y`, the two critical equations are equivalent to `T = 0`, and the outer
shift is `geoChannelL`. -/
theorem geo_channel_critical_iff (a : ℕ) {x y : ℂ} (hx0 : x ≠ 0) (hx1 : x ^ 2 ≠ 1)
    (hy : y ≠ 0 ∧ y ≠ 1 ∧ y ≠ x ∧ y ≠ -x ∧ y ≠ -1) :
    (geoRatioQ a 1 x (-1) (-y) = 1 ∧ geoRatioZ 1 x (-1) (-y) = 1 ↔ geoChannelT x y = 0) ∧
      geoRatioX 1 x (-1) (-y) = geoChannelL x y := by
  obtain ⟨hy0, hy1, hyx, hynx, -⟩ := hy
  have hx1' : x + 1 ≠ 0 := fun h ↦ hx1 (by linear_combination (x - 1) * h)
  have hxy : x + y ≠ 0 := fun h ↦ hynx (by linear_combination h)
  obtain ⟨hQ, hZ, hX⟩ := geo_critical_equations a (Q := -1) (z := -y) hx0 (by norm_num)
    (neg_ne_zero.mpr hy0) (fun h ↦ hy1 (by linear_combination -h))
    (fun h ↦ hyx (by linear_combination -h)) (fun h ↦ hynx (by linear_combination h))
    (fun h ↦ hynx (by linear_combination -h))
  have hpow : (-1 : ℂ) ^ (4 * a + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [hQ, hZ, hX, hpow]
  refine ⟨⟨fun h ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩, ?_⟩
  · unfold geoChannelT
    linear_combination h.1
  · unfold geoChannelT at h
    linear_combination h
  · unfold geoChannelT at h
    linear_combination (-(x + 1)) * h
  · unfold geoChannelL
    field_simp
    ring

/-- The denominator of `geoChannelY` does not vanish on `E_x = 0`:
`(2x - 1)² E_x(L) - (2Lx - L - 2x³ + 8x² - 6x + 1) d = 2x³(x - 1)²`. -/
private theorem geo_channel_den_ne_zero {x L : ℂ} (hx0 : x ≠ 0) (hx1 : x ^ 2 ≠ 1)
    (hE : L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2 = 0) : x ^ 2 + (2 * x - 1) * L ≠ 0 := by
  intro hd
  have hx1' : x - 1 ≠ 0 := fun h ↦ hx1 (by linear_combination (x + 1) * h)
  have h : 2 * x ^ 3 * (x - 1) ^ 2 = 0 := by
    linear_combination (2 * x - 1) ^ 2 * hE -
      (2 * L * x - L - 2 * x ^ 3 + 8 * x ^ 2 - 6 * x + 1) * hd
  simp [hx0, hx1'] at h

/-- The outer shift of a channel point lies on `E_x = 0`. -/
private theorem geo_channel_mapsTo_extra {x y : ℂ} (hx0 : x ≠ 0) (hx1 : x ^ 2 ≠ 1)
    (hT : geoChannelT x y = 0) :
    geoChannelL x y ^ 2 - (x ^ 2 - 4 * x + 1) * geoChannelL x y + x ^ 2 = 0 := by
  obtain ⟨hy0, -, -, hynx, -⟩ := geo_channelT_nondegenerate hx0 hx1 hT
  have hxy : x + y ≠ 0 := fun h ↦ hynx (by linear_combination h)
  have key : geoChannelL x y ^ 2 - (x ^ 2 - 4 * x + 1) * geoChannelL x y + x ^ 2 =
      x ^ 2 * (x ^ 3 + x ^ 2 * y - x * y + y ^ 2) * geoChannelT x y / (y * (x + y)) ^ 2 := by
    unfold geoChannelL geoChannelT
    field_simp
    ring
  rw [key, hT, mul_zero, zero_div]

/-- The inverse of a point of `E_x = 0` is a channel point. -/
private theorem geo_channel_T_inv {x L : ℂ} (hx0 : x ≠ 0) (hx1 : x ^ 2 ≠ 1)
    (hE : L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2 = 0) : geoChannelT x (geoChannelY x L) = 0 := by
  have hd := geo_channel_den_ne_zero hx0 hx1 hE
  have hgen : ∀ N D : ℂ, D ≠ 0 →
      geoChannelT x (N / D) = (N ^ 2 + (1 - x) * N * D + x * D ^ 2) / D ^ 2 := fun N D hD ↦ by
    unfold geoChannelT
    field_simp
  have key : geoChannelT x (geoChannelY x L) =
      2 * x ^ 3 * (L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2) / (x ^ 2 + (2 * x - 1) * L) ^ 2 := by
    rw [geoChannelY, hgen _ _ hd]
    congr 1
    ring
  rw [key, hE, mul_zero, zero_div]

/-- `geoChannelL ∘ geoChannelY` is the identity on `E_x = 0`. -/
private theorem geo_channel_L_inv {x L : ℂ} (hx0 : x ≠ 0) (hx1 : x ^ 2 ≠ 1)
    (hE : L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2 = 0) :
    geoChannelL x (geoChannelY x L) = L := by
  have hd := geo_channel_den_ne_zero hx0 hx1 hE
  obtain ⟨hy0, -, -, hynx, -⟩ := geo_channelT_nondegenerate hx0 hx1 (geo_channel_T_inv hx0 hx1 hE)
  have hxy : x + geoChannelY x L ≠ 0 := fun h ↦ hynx (by linear_combination h)
  have hgen : ∀ N D : ℂ, D ≠ 0 → x ^ 2 * (x - N / D) - L * (N / D * (x + N / D)) =
      (x ^ 2 * (x * D - N) * D - L * N * (x * D + N)) / D ^ 2 := fun N D hD ↦ by
    field_simp
  have key : x ^ 2 * (x - geoChannelY x L) - L * (geoChannelY x L * (x + geoChannelY x L)) =
      -2 * L * x ^ 3 * (L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2) /
        (x ^ 2 + (2 * x - 1) * L) ^ 2 := by
    rw [geoChannelY, hgen _ _ hd]
    congr 1
    ring
  rw [hE, mul_zero, zero_div, sub_eq_zero] at key
  rw [geoChannelL, div_eq_iff (mul_ne_zero hy0 hxy), key]

/-- `geoChannelY ∘ geoChannelL` is the identity on the channel. -/
private theorem geo_channel_Y_inv {x y : ℂ} (hx0 : x ≠ 0) (hx1 : x ^ 2 ≠ 1)
    (hT : geoChannelT x y = 0) : geoChannelY x (geoChannelL x y) = y := by
  obtain ⟨hy0, -, -, hynx, -⟩ := geo_channelT_nondegenerate hx0 hx1 hT
  have hxy : x + y ≠ 0 := fun h ↦ hynx (by linear_combination h)
  have hd := geo_channel_den_ne_zero hx0 hx1 (geo_channel_mapsTo_extra hx0 hx1 hT)
  have hl : geoChannelL x y * (y * (x + y)) = x ^ 2 * (x - y) :=
    div_mul_cancel₀ _ (mul_ne_zero hy0 hxy)
  rw [geoChannelY, div_eq_iff hd]
  have h : (x * (geoChannelL x y + x ^ 2) - y * (x ^ 2 + (2 * x - 1) * geoChannelL x y)) *
      (y * (x + y)) = 0 := by
    unfold geoChannelT at hT
    linear_combination (x - 2 * x * y + y) * hl + x ^ 2 * (x - y) * hT
  rcases mul_eq_zero.mp h with h | h
  · linear_combination h
  · exact absurd h (mul_ne_zero hy0 hxy)

/-- Both inclusions: `y ↦ L` is a bijection from the channel onto `E_x = 0`, with inverse
`geoChannelY`, whose denominator does not vanish on `E_x = 0`. -/
theorem geo_channel_bijOn {x : ℂ} (hx0 : x ≠ 0) (hx1 : x ^ 2 ≠ 1) :
    Set.BijOn (geoChannelL x) {y | geoChannelT x y = 0}
        {L | L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2 = 0} ∧
      Set.InvOn (geoChannelY x) (geoChannelL x) {y | geoChannelT x y = 0}
        {L | L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2 = 0} ∧
      ∀ L, L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2 = 0 → x ^ 2 + (2 * x - 1) * L ≠ 0 := by
  have hinv : Set.InvOn (geoChannelY x) (geoChannelL x) {y | geoChannelT x y = 0}
      {L | L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2 = 0} :=
    ⟨fun y hy ↦ geo_channel_Y_inv hx0 hx1 hy, fun L hL ↦ geo_channel_L_inv hx0 hx1 hL⟩
  refine ⟨hinv.bijOn (fun y hy ↦ geo_channel_mapsTo_extra hx0 hx1 hy)
    (fun L hL ↦ geo_channel_T_inv hx0 hx1 hL), hinv,
    fun L hL ↦ geo_channel_den_ne_zero hx0 hx1 hL⟩

/-- The two-sheeted lift `x = M²`: off `M = 0`, `M⁴ = 1`, a point lies on `E` iff it comes from a
unique channel point, and then `r = 1/y`. -/
theorem geo_channel_extraFactor {M L : ℂ} (hM0 : M ≠ 0) (hM1 : M ^ 4 ≠ 1) :
    (evalPoint extraFactorℂ (M, L) = 0 ↔
        ∃! y, geoChannelT (M ^ 2) y = 0 ∧ L = geoChannelL (M ^ 2) y) ∧
      ∀ y, geoChannelT (M ^ 2) y = 0 → L = geoChannelL (M ^ 2) y → geoCurveR (M, L) = 1 / y := by
  have hx0 : M ^ 2 ≠ 0 := pow_ne_zero 2 hM0
  have hx1 : (M ^ 2) ^ 2 ≠ 1 := by rwa [← pow_mul]
  have hE : evalPoint extraFactorℂ (M, L) =
      L ^ 2 - ((M ^ 2) ^ 2 - 4 * M ^ 2 + 1) * L + (M ^ 2) ^ 2 := by
    rw [evalPoint_extraFactorℂ]
    ring
  refine ⟨?_, fun y hT hL ↦ ?_⟩
  · rw [hE]
    constructor
    · intro h
      refine ⟨geoChannelY (M ^ 2) L, ⟨geo_channel_T_inv hx0 hx1 h,
        (geo_channel_L_inv hx0 hx1 h).symm⟩, fun y ⟨hT, hL⟩ ↦ ?_⟩
      rw [hL, geo_channel_Y_inv hx0 hx1 hT]
    · rintro ⟨y, ⟨hT, hL⟩, -⟩
      rw [hL]
      exact geo_channel_mapsTo_extra hx0 hx1 hT
  · obtain ⟨hy0, -, -, hynx, -⟩ := geo_channelT_nondegenerate hx0 hx1 hT
    have hxy : M ^ 2 + y ≠ 0 := fun h ↦ hynx (by linear_combination h)
    have hM1 : M ^ 2 - 1 ≠ 0 := fun h ↦ hx1 (by linear_combination (M ^ 2 + 1) * h)
    rw [geoCurveR, hL]
    simp only
    generalize M ^ 2 = x at *
    have key : (x + geoChannelL x y) * y - 1 * (x * (x - 1)) = x * geoChannelT x y / (x + y) := by
      unfold geoChannelL geoChannelT
      field_simp
      ring
    rw [hT, mul_zero, zero_div, sub_eq_zero] at key
    rw [div_eq_div_iff (mul_ne_zero hx0 hM1) hy0, key]

end AJConjecture
