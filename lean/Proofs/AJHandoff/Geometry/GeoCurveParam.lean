import Mathlib
import AJFamily.Volume.ExtraFactorEval

/-!
# The rational parameter of the extra curve (G-CURVE, point level)

On `E(M, L) = L² - (M⁴ - 4M² + 1)L + M⁴ = 0` put `x = M²` and
`r = (x + L)/(x(x - 1))`, `f = (1 + r)/(1 - r)`. Then `x = f/r = (1 + r)/(r(1 - r))` and
`L = f²`; conversely these formulas, with any square root `M` of `x(r)`, give a point of `E`.
The square curve `E_x(L) = 0` in the `(x, L)` plane is rational with parameter `r`.

The smooth torus locus (`GeoSmoothTorusLocus`) is `E ∩ (ℂ^×)²` minus the two nodes `(±1, -1)`;
on it `r ∉ {0, 1, -1}` and `r² ≠ -1`. The nodes are ordinary, with tangent cones
`v² ± 4uv + 8u²`, and each lifts to the two parameters `r = i` and `r = -i`.

Route: every statement is a rational-function identity after substituting `L² = AL - x²`;
`field_simp` and `linear_combination` with the curve equation. Nonvanishing of `r`, `1 ∓ r` uses
`E(M, -x) = x(x - 1)²`, `E(M, x² - 2x) = 2x(x - 1)²`, `E(M, -x²) = 2x²(x - 1)²`.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- `x(r) = (1 + r)/(r(1 - r))`: the square of the meridian along the curve. -/
def geoX (r : ℂ) : ℂ := (1 + r) / (r * (1 - r))

/-- `f(r) = (1 + r)/(1 - r)`. -/
def geoF (r : ℂ) : ℂ := (1 + r) / (1 - r)

/-- `L(r) = f(r)²`: the longitude along the curve. -/
def geoL (r : ℂ) : ℂ := geoF r ^ 2

/-- The normalization parameter `r = (M² + L)/(M²(M² - 1))` of a point `(M, L)`. -/
def geoCurveR (p : ℂ × ℂ) : ℂ := (p.1 ^ 2 + p.2) / (p.1 ^ 2 * (p.1 ^ 2 - 1))

/-- The smooth torus locus: points of `E = 0` in `(ℂ^×)²` other than the nodes `(±1, -1)`
(on `E`, `M ≠ 0` forces `L ≠ 0`, and `M² = 1` forces `L = -1`). -/
def GeoSmoothTorusLocus : Set (ℂ × ℂ) :=
  {p | evalPoint extraFactorℂ p = 0 ∧ p.1 ≠ 0 ∧ p.1 ^ 2 ≠ 1}

/-- On the square curve with `x ∉ {0, 1}`, the parameter `r = (x + L)/(x(x - 1))` avoids
`0, ±1` and recovers `x = x(r)`, `L = L(r)`. -/
private theorem geo_square_param_of_curve (x L : ℂ)
    (hE : L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2 = 0) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (x + L) / (x * (x - 1)) ≠ 0 ∧ (x + L) / (x * (x - 1)) ≠ 1 ∧
      (x + L) / (x * (x - 1)) ≠ -1 ∧ x = geoX ((x + L) / (x * (x - 1))) ∧
      L = geoL ((x + L) / (x * (x - 1))) := by
  have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hb : x * (x - 1) ≠ 0 := mul_ne_zero hx0 hx1'
  have ha : x + L ≠ 0 := by
    intro h
    obtain rfl : L = -x := by linear_combination h
    exact mul_ne_zero hx0 (pow_ne_zero 2 hx1') (by linear_combination hE)
  have hc : x ^ 2 - 2 * x - L ≠ 0 := by
    intro h
    obtain rfl : L = x ^ 2 - 2 * x := by linear_combination -h
    exact mul_ne_zero (mul_ne_zero two_ne_zero hx0) (pow_ne_zero 2 hx1') (by linear_combination hE)
  have hd : x ^ 2 + L ≠ 0 := by
    intro h
    obtain rfl : L = -x ^ 2 := by linear_combination h
    exact mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hx0)) (pow_ne_zero 2 hx1')
      (by linear_combination hE)
  have h1r : 1 - (x + L) / (x * (x - 1)) = (x ^ 2 - 2 * x - L) / (x * (x - 1)) := by
    field_simp
    ring
  have h1r' : 1 + (x + L) / (x * (x - 1)) = (x ^ 2 + L) / (x * (x - 1)) := by
    field_simp
    ring
  have hr1 : 1 - (x + L) / (x * (x - 1)) ≠ 0 := by rw [h1r]; exact div_ne_zero hc hb
  have hrm1 : 1 + (x + L) / (x * (x - 1)) ≠ 0 := by rw [h1r']; exact div_ne_zero hd hb
  refine ⟨div_ne_zero ha hb, fun h ↦ hr1 (by rw [h]; ring), fun h ↦ hrm1 (by rw [h]; ring), ?_, ?_⟩
  · unfold geoX
    rw [h1r, h1r', eq_div_iff (mul_ne_zero (div_ne_zero ha hb) (div_ne_zero hc hb)),
      div_mul_div_comm, mul_div_assoc', div_eq_div_iff (mul_ne_zero hb hb) hb]
    linear_combination (-x * (x * (x - 1))) * hE
  · unfold geoL geoF
    rw [h1r, h1r', div_div_div_cancel_right₀ hb, div_pow, eq_div_iff (pow_ne_zero 2 hc)]
    linear_combination (L - x ^ 2) * hE

/-- If `r² = -1` then `x(r) = 1`. -/
private theorem geoX_eq_one_of_sq_eq_neg_one {r : ℂ} (h0 : r ≠ 0) (h1 : r ≠ 1)
    (hi : r ^ 2 = -1) : geoX r = 1 := by
  have h1' : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  unfold geoX
  rw [div_eq_one_iff_eq (mul_ne_zero h0 h1')]
  linear_combination hi

/-- For `r ∉ {0, ±1, ±i}`, the point `(x(r), L(r))` lies on the square curve, `x(r) ∉ {0, 1}`,
and `r` is recovered as `(x + L)/(x(x - 1))`. -/
private theorem geo_square_curve_of_param {r : ℂ} (h0 : r ≠ 0) (h1 : r ≠ 1) (hm1 : r ≠ -1)
    (hi : r ^ 2 ≠ -1) :
    geoL r ^ 2 - (geoX r ^ 2 - 4 * geoX r + 1) * geoL r + geoX r ^ 2 = 0 ∧ geoX r ≠ 0 ∧
      geoX r ≠ 1 ∧ (geoX r + geoL r) / (geoX r * (geoX r - 1)) = r := by
  have h1' : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hm1' : 1 + r ≠ 0 := by
    intro h; exact hm1 (by linear_combination h)
  have hi' : 1 + r ^ 2 ≠ 0 := by
    intro h; exact hi (by linear_combination h)
  have hx0 : geoX r ≠ 0 := div_ne_zero hm1' (mul_ne_zero h0 h1')
  have hx1 : geoX r - 1 = (1 + r ^ 2) / (r * (1 - r)) := by
    unfold geoX
    field_simp
    ring
  refine ⟨?_, hx0, fun h ↦ (div_ne_zero hi' (mul_ne_zero h0 h1')) (by rw [← hx1, h]; ring), ?_⟩
  · unfold geoL geoF geoX
    field_simp
    ring
  · rw [hx1]
    unfold geoL geoF geoX
    field_simp
    ring

/-- On the smooth torus locus the parameter avoids `0, ±1, ±i` and recovers `M² = x(r)`,
`L = f(r)²`. -/
theorem geo_curveR_spec {p : ℂ × ℂ} (hp : p ∈ GeoSmoothTorusLocus) :
    geoCurveR p ≠ 0 ∧ geoCurveR p ≠ 1 ∧ geoCurveR p ≠ -1 ∧ geoCurveR p ^ 2 ≠ -1 ∧
      p.1 ^ 2 = geoX (geoCurveR p) ∧ p.2 = geoL (geoCurveR p) := by
  obtain ⟨hE, hM0, hM1⟩ := hp
  rw [evalPoint_extraFactorℂ] at hE
  have hE' : p.2 ^ 2 - ((p.1 ^ 2) ^ 2 - 4 * p.1 ^ 2 + 1) * p.2 + (p.1 ^ 2) ^ 2 = 0 := by
    linear_combination hE
  obtain ⟨h0, h1, hm1, hX, hL⟩ := geo_square_param_of_curve _ _ hE' (pow_ne_zero 2 hM0) hM1
  refine ⟨h0, h1, hm1, fun hi ↦ hM1 ?_, hX, hL⟩
  rw [hX]
  exact geoX_eq_one_of_sq_eq_neg_one h0 h1 hi

/-- Conversely, a parameter `r ∉ {0, ±1, ±i}` and a square root `M` of `x(r)` give a point of the
smooth torus locus with parameter `r`. -/
theorem geo_mem_smoothTorusLocus_of_param {r M : ℂ} (h0 : r ≠ 0) (h1 : r ≠ 1) (hm1 : r ≠ -1)
    (hi : r ^ 2 ≠ -1) (hM : M ^ 2 = geoX r) :
    (M, geoL r) ∈ GeoSmoothTorusLocus ∧ geoCurveR (M, geoL r) = r := by
  obtain ⟨hE, hx0, hx1, hr⟩ := geo_square_curve_of_param h0 h1 hm1 hi
  refine ⟨⟨?_, fun h ↦ hx0 (by rw [← hM, show M = 0 from h]; ring),
    fun h ↦ hx1 (by rw [← hM]; exact h)⟩, ?_⟩
  · rw [evalPoint_extraFactorℂ]
    simp only
    linear_combination hE +
      (-(M ^ 2 + geoX r) * geoL r + 4 * geoL r + M ^ 2 + geoX r) * hM
  · unfold geoCurveR
    simp only
    rw [hM]
    exact hr

/-- The square curve `E_x(L) = L² - (x² - 4x + 1)L + x² = 0` is rational: `r ↦ (x(r), L(r))` is a
bijection from `ℂ ∖ {0, ±1, ±i}` onto its points with `x ∉ {0, 1}` (`x(±i) = 1` is the node),
inverse `(x, L) ↦ (x + L)/(x(x - 1))`; and `x = f/r`, `L = f²`. -/
theorem geo_squareCurve_param :
    Set.BijOn (fun r ↦ (geoX r, geoL r)) {r | r ≠ 0 ∧ r ≠ 1 ∧ r ≠ -1 ∧ r ^ 2 ≠ -1}
        {q : ℂ × ℂ | q.2 ^ 2 - (q.1 ^ 2 - 4 * q.1 + 1) * q.2 + q.1 ^ 2 = 0 ∧ q.1 ≠ 0 ∧ q.1 ≠ 1} ∧
      ∀ r : ℂ, r ≠ 0 → r ≠ 1 → r ≠ -1 → r ^ 2 ≠ -1 → geoX r = geoF r / r ∧
        (geoX r + geoL r) / (geoX r * (geoX r - 1)) = r := by
  refine ⟨⟨fun r ⟨h0, h1, hm1, hi⟩ ↦ ?_, fun r ⟨h0, h1, hm1, hi⟩ r' ⟨h0', h1', hm1', hi'⟩ h ↦ ?_,
    fun q ⟨hE, hx0, hx1⟩ ↦ ?_⟩, fun r h0 h1 hm1 hi ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨hE, hx0, hx1, -⟩ := geo_square_curve_of_param h0 h1 hm1 hi
    exact ⟨hE, hx0, hx1⟩
  · obtain ⟨-, -, -, hr⟩ := geo_square_curve_of_param h0 h1 hm1 hi
    obtain ⟨-, -, -, hr'⟩ := geo_square_curve_of_param h0' h1' hm1' hi'
    simp only [Prod.mk.injEq] at h
    rw [← hr, ← hr', h.1, h.2]
  · obtain ⟨h0, h1, hm1, hX, hL⟩ := geo_square_param_of_curve q.1 q.2 hE hx0 hx1
    refine ⟨(q.1 + q.2) / (q.1 * (q.1 - 1)), ⟨h0, h1, hm1, fun hi ↦ hx1 ?_⟩, ?_⟩
    · rw [hX]
      exact geoX_eq_one_of_sq_eq_neg_one h0 h1 hi
    · simp only
      rw [← hX, ← hL]
  · have h1' : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    unfold geoX geoF
    field_simp
  · exact (geo_square_curve_of_param h0 h1 hm1 hi).2.2.2

/-- The singular points of `E` in `(ℂ^×)²` are exactly the two nodes `(±1, -1)`: both partial
derivatives `∂E/∂L = 2L - (M⁴ - 4M² + 1)` and `∂E/∂M = -(4M³ - 8M)L + 4M³` vanish there and
nowhere else on `E ∩ (ℂ^×)²`. -/
theorem geo_extraFactor_singular_iff {p : ℂ × ℂ} (hp : evalPoint extraFactorℂ p = 0)
    (h0 : p.1 ≠ 0) :
    (2 * p.2 - (p.1 ^ 4 - 4 * p.1 ^ 2 + 1) = 0 ∧
        -(4 * p.1 ^ 3 - 8 * p.1) * p.2 + 4 * p.1 ^ 3 = 0) ↔
      p = (1, -1) ∨ p = (-1, -1) := by
  rw [evalPoint_extraFactorℂ] at hp
  obtain ⟨M, L⟩ := p
  simp only at hp h0 ⊢
  constructor
  · rintro ⟨hA, hB⟩
    have hB' : -(M ^ 2 - 2) * L + M ^ 2 = 0 := by
      have h4 : (4 * M) ≠ 0 := mul_ne_zero (by norm_num) h0
      apply mul_left_cancel₀ h4
      linear_combination hB
    have hsq : (L - M ^ 2) * (L + M ^ 2) = 0 := by linear_combination L * hA - hp
    rcases mul_eq_zero.mp hsq with h | h
    · have hL : L = M ^ 2 := by linear_combination h
      subst hL
      have h3 : M ^ 2 * (M ^ 2 - 3) = 0 := by linear_combination -hB'
      have h3' : M ^ 2 = 3 := by
        rcases mul_eq_zero.mp h3 with h | h
        · exact absurd h (pow_ne_zero 2 h0)
        · linear_combination h
      have : (8 : ℂ) = 0 := by linear_combination hA + (M ^ 2 - 3) * h3'
      norm_num at this
    · have hL : L = -M ^ 2 := by linear_combination h
      subst hL
      have h3 : M ^ 2 * (M ^ 2 - 1) = 0 := by linear_combination hB'
      have h1 : M ^ 2 = 1 := by
        rcases mul_eq_zero.mp h3 with h | h
        · exact absurd h (pow_ne_zero 2 h0)
        · linear_combination h
      have h2 : (M - 1) * (M + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h2 with h | h
      · obtain rfl : M = 1 := by linear_combination h
        left; norm_num
      · obtain rfl : M = -1 := by linear_combination h
        right; norm_num
  · rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      norm_num

/-- The nodes are ordinary: the tangent cone of `E` at `(±1, -1)` is `v² ± 4uv + 8u²`, a binary
quadratic form of discriminant `-16 ≠ 0`. -/
theorem geo_extraFactor_tangentCone (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (u v : ℂ) :
    Tendsto (fun s : ℂ ↦ evalPoint extraFactorℂ (ε + s * u, -1 + s * v) / s ^ 2) (𝓝[≠] 0)
      (𝓝 (v ^ 2 + 4 * ε * u * v + 8 * u ^ 2)) := by
  have hQ : ∀ a₀ a₁ a₂ a₃ : ℂ, Continuous fun s : ℂ ↦ a₃ * s ^ 3 + a₂ * s ^ 2 + a₁ * s + a₀ := by
    intro a₀ a₁ a₂ a₃
    fun_prop
  have hlim := ((hQ (8 * u ^ 2 + 4 * ε * u * v + v ^ 2) (8 * ε * u ^ 3 - 2 * u ^ 2 * v)
    (2 * u ^ 4 - 4 * ε * u ^ 3 * v) (-u ^ 4 * v)).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  have h0 : -u ^ 4 * v * 0 ^ 3 + (2 * u ^ 4 - 4 * ε * u ^ 3 * v) * 0 ^ 2 +
      (8 * ε * u ^ 3 - 2 * u ^ 2 * v) * 0 + (8 * u ^ 2 + 4 * ε * u * v + v ^ 2) =
      v ^ 2 + 4 * ε * u * v + 8 * u ^ 2 := by ring
  rw [h0] at hlim
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun s hs ↦ ?_)
  have hs' : s ≠ 0 := hs
  simp only
  rw [evalPoint_extraFactorℂ, eq_div_iff (pow_ne_zero 2 hs')]
  rcases hε with rfl | rfl <;> simp only <;> ring

/-- Each node has the two branch parameters `r = ±i`: `x(±i) = 1`, `L(±i) = -1`. -/
theorem geo_node_branches :
    geoX Complex.I = 1 ∧ geoX (-Complex.I) = 1 ∧ geoL Complex.I = -1 ∧
      geoL (-Complex.I) = -1 := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have h1 : (1 : ℂ) - Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have h2 : (1 : ℂ) + Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold geoX
    rw [div_eq_one_iff_eq (mul_ne_zero Complex.I_ne_zero h1)]
    linear_combination hI
  · unfold geoX
    rw [div_eq_one_iff_eq (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by simpa using h2))]
    linear_combination hI
  · unfold geoL geoF
    rw [div_pow, div_eq_iff (pow_ne_zero 2 h1)]
    linear_combination 2 * hI
  · unfold geoL geoF
    rw [div_pow, div_eq_iff (pow_ne_zero 2 (by simpa using h2))]
    linear_combination 2 * hI

end AJConjecture
