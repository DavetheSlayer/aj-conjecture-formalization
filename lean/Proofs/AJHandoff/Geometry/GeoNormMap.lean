import Mathlib
import AJHandoff.Geometry.GeoNormModel

/-!
# The normalization map onto the torus part of `E` (G-NORM)

On the punctured model (`Y² = X³ - X`, `Y ≠ 0`) the map
`ν(X, Y) = (M, L) = (Y/(-X(1 + X)), ((1 - X)/(1 + X))²)` is regular and maps onto the torus part
`E ∩ (ℂ^×)²`. It is injective over the smooth points and two-to-one over each node `(±1, -1)`:
the preimages of `(1, -1)` are `(X, Y) = (-i, 1 + i)` (parameter `r = i`) and `(i, 1 - i)`
(parameter `r = -i`), the two normalized branches; similarly for `(-1, -1)` with `Y ↦ -Y`.
At the four punctures `r = 0, 1, -1, ∞` the coordinates leave the torus with
`(ord M, ord L) = (-1, 0), (-1, -4), (1, 4), (1, 0)` on the model; on the `r`-line, where the
cover has ramification index `2`, this is `(ord x, ord L) = (-1, 0), (-1, -2), (1, 2), (1, 0)`,
recorded by the limits in `geo_puncture_orders`.

Route: `GeoCurveWeierstrass` (`geo_weierstrass_birational`) off the nodes; at the nodes solve
`X² = -1`. The limits are elementary.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- The normalization map `(X, Y) ↦ (Y/(-X(1 + X)), ((1 - X)/(1 + X))²)`. -/
def geoNormMap (q : ℂ × ℂ) : ℂ × ℂ :=
  (q.2 / (-(q.1 * (1 + q.1))), ((1 - q.1) / (1 + q.1)) ^ 2)

/-- The punctured model: affine points of `Y² = X³ - X` with `Y ≠ 0`. -/
def GeoPuncturedModel : Set (ℂ × ℂ) :=
  {q | q.2 ^ 2 = q.1 ^ 3 - q.1 ∧ q.2 ≠ 0}

/-- The torus part of `E`: points of `E = 0` with `M ≠ 0` (then `L ≠ 0`). -/
def GeoTorusCurve : Set (ℂ × ℂ) :=
  {p | evalPoint extraFactorℂ p = 0 ∧ p.1 ≠ 0}

/-- On the punctured model `X ∉ {0, ±1}`. -/
private theorem geo_puncturedModel_ne {q : ℂ × ℂ} (hq : q ∈ GeoPuncturedModel) :
    q.1 ≠ 0 ∧ q.1 - 1 ≠ 0 ∧ 1 + q.1 ≠ 0 := by
  obtain ⟨hE, hY⟩ := hq
  have h : q.1 * (q.1 - 1) * (1 + q.1) ≠ 0 := by
    rw [← pow_ne_zero_iff two_ne_zero] at hY
    intro h
    apply hY
    rw [hE]
    linear_combination h
  exact ⟨fun h' ↦ h (by rw [h']; ring), fun h' ↦ h (by rw [h']; ring),
    fun h' ↦ h (by rw [h']; ring)⟩

/-- On the punctured model `M(ν(q))² = (X - 1)/(X(1 + X))`. -/
private theorem geo_normMap_fst_sq {q : ℂ × ℂ} (hq : q ∈ GeoPuncturedModel) :
    (geoNormMap q).1 ^ 2 = (q.1 - 1) / (q.1 * (1 + q.1)) := by
  obtain ⟨h0, h1, h2⟩ := geo_puncturedModel_ne hq
  simp only [geoNormMap]
  rw [div_pow, neg_sq, hq.1]
  field_simp
  ring

/-- `ν` maps the punctured model into the torus part of `E`. -/
private theorem geo_normMap_mapsTo : Set.MapsTo geoNormMap GeoPuncturedModel GeoTorusCurve := by
  intro q hq
  obtain ⟨h0, h1, h2⟩ := geo_puncturedModel_ne hq
  have hM := geo_normMap_fst_sq hq
  refine ⟨?_, ?_⟩
  · rw [evalPoint_extraFactorℂ, show (geoNormMap q).1 ^ 4 = ((geoNormMap q).1 ^ 2) ^ 2 by ring, hM]
    simp only [geoNormMap]
    field_simp
    ring
  · simp only [geoNormMap]
    exact div_ne_zero hq.2 (neg_ne_zero.mpr (mul_ne_zero h0 h2))

/-- `ν` agrees with the birational map `geoFromWeierstrass`. -/
private theorem geo_normMap_eq_fromWeierstrass : geoNormMap = geoFromWeierstrass := rfl

/-- On `E` with `M² = 1` one has `L = -1`. -/
private theorem geo_snd_eq_neg_one_of_sq_eq_one {p : ℂ × ℂ} (hp : p ∈ GeoTorusCurve)
    (h1 : p.1 ^ 2 = 1) : p.2 = -1 := by
  have hE := hp.1
  rw [evalPoint_extraFactorℂ, show p.1 ^ 4 = (p.1 ^ 2) ^ 2 by ring, h1] at hE
  have h : (p.2 + 1) ^ 2 = 0 := by linear_combination hE
  exact eq_neg_of_add_eq_zero_left (pow_eq_zero_iff two_ne_zero |>.mp h)

/-- Over a node `(M, -1)`, `M² = 1`, the fibre of `ν` is `{(X, M(1 - X)) : X² = -1}`. -/
private theorem geo_normMap_mem_node_fiber_iff {p : ℂ × ℂ} (hp : p ∈ GeoTorusCurve)
    (h1 : p.1 ^ 2 = 1) (q : ℂ × ℂ) :
    (q ∈ GeoPuncturedModel ∧ geoNormMap q = p) ↔ q.1 ^ 2 = -1 ∧ q.2 = p.1 * (1 - q.1) := by
  have hL := geo_snd_eq_neg_one_of_sq_eq_one hp h1
  constructor
  · rintro ⟨hq, rfl⟩
    obtain ⟨h0, hm1, hp1⟩ := geo_puncturedModel_ne hq
    have hM := geo_normMap_fst_sq hq
    rw [h1, eq_div_iff (mul_ne_zero h0 hp1)] at hM
    have hX : q.1 ^ 2 = -1 := by linear_combination hM
    refine ⟨hX, ?_⟩
    simp only [geoNormMap]
    field_simp
    linear_combination q.2 * hX
  · rintro ⟨hX, hY⟩
    have hM0 : p.1 ≠ 0 := hp.2
    have hX1 : 1 - q.1 ≠ 0 := by
      intro h
      rw [← sub_eq_zero.mp h] at hX
      norm_num at hX
    have hX1' : 1 + q.1 ≠ 0 := by
      intro h
      rw [eq_neg_of_add_eq_zero_right h] at hX
      norm_num at hX
    have hX0 : q.1 ≠ 0 := by
      rintro h
      rw [h] at hX
      norm_num at hX
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hY]
      linear_combination (1 - q.1) ^ 2 * h1 + (1 - q.1) * hX
    · rw [hY]
      exact mul_ne_zero hM0 hX1
    · obtain ⟨M, L⟩ := p
      obtain ⟨X, Y⟩ := q
      simp only at hX hY hL h1 hX1 hX1' hX0 ⊢
      simp only [geoNormMap, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [div_eq_iff (neg_ne_zero.mpr (mul_ne_zero hX0 hX1')), hY]
        linear_combination M * hX
      · rw [div_pow, div_eq_iff (pow_ne_zero 2 hX1'), hL]
        linear_combination 2 * hX

/-- The fibre of `ν` over a node `(M, -1)`. -/
private theorem geo_normMap_node_fiber_eq {p : ℂ × ℂ} (hp : p ∈ GeoTorusCurve)
    (h1 : p.1 ^ 2 = 1) :
    {q | q ∈ GeoPuncturedModel ∧ geoNormMap q = p} =
      {(Complex.I, p.1 * (1 - Complex.I)), (-Complex.I, p.1 * (1 - -Complex.I))} := by
  ext q
  rw [Set.mem_ofPred_eq, geo_normMap_mem_node_fiber_iff hp h1, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  obtain ⟨X, Y⟩ := q
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hX, rfl⟩
    have h : (X - Complex.I) * (X + Complex.I) = 0 := by
      linear_combination hX - Complex.I_sq
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl ⟨sub_eq_zero.mp h, by rw [sub_eq_zero.mp h]⟩
    · exact Or.inr ⟨eq_neg_of_add_eq_zero_left h, by rw [eq_neg_of_add_eq_zero_left h]⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Complex.I_sq, rfl⟩
    · exact ⟨by rw [neg_sq, Complex.I_sq], rfl⟩

/-- `ν` maps the punctured model onto the torus part of `E`. -/
theorem geo_normMap_mapsTo_surjOn :
    Set.MapsTo geoNormMap GeoPuncturedModel GeoTorusCurve ∧
      Set.SurjOn geoNormMap GeoPuncturedModel GeoTorusCurve := by
  refine ⟨geo_normMap_mapsTo, fun p hp ↦ ?_⟩
  by_cases h1 : p.1 ^ 2 = 1
  · have hq : (Complex.I, p.1 * (1 - Complex.I)) ∈
        {q | q ∈ GeoPuncturedModel ∧ geoNormMap q = p} := by
      rw [geo_normMap_node_fiber_eq hp h1]
      exact Or.inl rfl
    exact ⟨_, hq.1, hq.2⟩
  · have hs : p ∈ GeoSmoothTorusLocus := ⟨hp.1, hp.2, h1⟩
    obtain ⟨hbij, hinv⟩ := geo_weierstrass_birational
    have hw := hbij.mapsTo hs
    exact ⟨geoToWeierstrass p, ⟨hw.1, hw.2.1⟩, hinv.1 hs⟩

/-- `ν` is injective over the smooth points and two-to-one over the nodes. -/
theorem geo_normMap_fiber_ncard {p : ℂ × ℂ} (hp : p ∈ GeoTorusCurve) :
    {q | q ∈ GeoPuncturedModel ∧ geoNormMap q = p}.ncard = if p.1 ^ 2 = 1 then 2 else 1 := by
  split_ifs with h1
  · rw [geo_normMap_node_fiber_eq hp h1, Set.ncard_pair]
    intro h
    have h' := congrArg (fun q : ℂ × ℂ ↦ q.1.im) h
    norm_num at h'
  · rw [Set.ncard_eq_one]
    have hs : p ∈ GeoSmoothTorusLocus := ⟨hp.1, hp.2, h1⟩
    obtain ⟨hbij, hinv⟩ := geo_weierstrass_birational
    refine ⟨geoToWeierstrass p, Set.ext fun q ↦ ⟨?_, ?_⟩⟩
    · rintro ⟨hq, rfl⟩
      obtain ⟨h0, hm1, hp1⟩ := geo_puncturedModel_ne hq
      have hX : q.1 ^ 2 ≠ -1 := by
        intro hX
        apply h1
        rw [geo_normMap_fst_sq hq, div_eq_one_iff_eq (mul_ne_zero h0 hp1)]
        linear_combination -hX
      have hw : q ∈ GeoWeierstrassOpen := ⟨hq.1, hq.2, hX⟩
      rw [Set.mem_singleton_iff, geo_normMap_eq_fromWeierstrass, hinv.2 hw]
    · rintro rfl
      have hw := hbij.mapsTo hs
      exact ⟨⟨hw.1, hw.2.1⟩, hinv.1 hs⟩

/-- The two branches over the node `(1, -1)`: parameters `r = -X = i` and `r = -i`. -/
theorem geo_normMap_node_fiber :
    {q | q ∈ GeoPuncturedModel ∧ geoNormMap q = (1, -1)} =
      {(-Complex.I, 1 + Complex.I), (Complex.I, 1 - Complex.I)} := by
  have hp : ((1 : ℂ), (-1 : ℂ)) ∈ GeoTorusCurve :=
    ⟨by rw [evalPoint_extraFactorℂ]; ring, one_ne_zero⟩
  rw [geo_normMap_node_fiber_eq hp (one_pow 2), Set.pair_comm]
  simp only [one_mul, sub_neg_eq_add]

/-- A limit along a punctured neighbourhood, from a function continuous at the point. -/
private theorem geo_tendsto_punctured_of_eventuallyEq {f g : ℂ → ℂ} {a c : ℂ}
    (hg : ContinuousAt g a) (hc : g a = c) (h : ∀ᶠ r in 𝓝[≠] a, g r = f r) :
    Tendsto f (𝓝[≠] a) (𝓝 c) :=
  hc ▸ (hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h

/-- Eventually `r ≠ b` near `a ≠ b`, along the punctured neighbourhood of `a`. -/
private theorem geo_eventually_ne_punctured {a b : ℂ} (h : a ≠ b) : ∀ᶠ r in 𝓝[≠] a, r ≠ b :=
  (eventually_ne_nhds h).filter_mono nhdsWithin_le_nhds

/-- A limit at `∞`, through `w = 1/r`, from a function continuous at `w = 0`. -/
private theorem geo_tendsto_cocompact_of_inv {f g : ℂ → ℂ} {c : ℂ} (hg : ContinuousAt g 0)
    (hc : g 0 = c) (h : ∀ r : ℂ, r ≠ 0 → r ≠ 1 → g r⁻¹ = f r) :
    Tendsto f (cocompact ℂ) (𝓝 c) := by
  have ht : Tendsto (fun r : ℂ ↦ g r⁻¹) (cocompact ℂ) (𝓝 c) := by
    rw [← hc, ← Metric.cobounded_eq_cocompact]
    exact hg.tendsto.comp tendsto_inv₀_cobounded
  refine ht.congr' ?_
  filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact,
    (isCompact_singleton (x := (1 : ℂ))).compl_mem_cocompact] with r h0 h1
  exact h r h0 h1

/-- The behaviour of `x = M²` and `L` at the four punctures of the `r`-line: simple pole of `x`
at `r = 0, 1`, simple zero at `r = -1, ∞`; `L` is a unit at `0, ∞`, has a double pole at `1` and
a double zero at `-1`. -/
theorem geo_puncture_orders :
    Tendsto (fun r ↦ r * geoX r) (𝓝[≠] 0) (𝓝 1) ∧ Tendsto geoL (𝓝[≠] 0) (𝓝 1) ∧
      Tendsto (fun r ↦ (1 - r) * geoX r) (𝓝[≠] 1) (𝓝 2) ∧
      Tendsto (fun r ↦ (1 - r) ^ 2 * geoL r) (𝓝[≠] 1) (𝓝 4) ∧
      Tendsto (fun r ↦ geoX r / (1 + r)) (𝓝[≠] (-1)) (𝓝 (-1 / 2)) ∧
      Tendsto (fun r ↦ geoL r / (1 + r) ^ 2) (𝓝[≠] (-1)) (𝓝 (1 / 4)) ∧
      Tendsto (fun r ↦ r * geoX r) (cocompact ℂ) (𝓝 (-1)) ∧
      Tendsto geoL (cocompact ℂ) (𝓝 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine geo_tendsto_punctured_of_eventuallyEq (g := fun r ↦ (1 + r) / (1 - r))
      (by fun_prop (disch := norm_num)) (by norm_num) ?_
    filter_upwards [self_mem_nhdsWithin, geo_eventually_ne_punctured (b := 1) zero_ne_one]
      with r (h0 : r ≠ 0) h1
    have h1' : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    simp only [geoX]
    field_simp
  · refine geo_tendsto_punctured_of_eventuallyEq (g := geoL)
      (by unfold geoL geoF; fun_prop (disch := norm_num)) (by simp [geoL, geoF])
      (Eventually.of_forall fun r ↦ rfl)
  · refine geo_tendsto_punctured_of_eventuallyEq (g := fun r ↦ (1 + r) / r)
      (by fun_prop (disch := norm_num)) (by norm_num) ?_
    filter_upwards [self_mem_nhdsWithin, geo_eventually_ne_punctured (b := 0) one_ne_zero]
      with r (h1 : r ≠ 1) h0
    have h1' : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    simp only [geoX]
    field_simp
  · refine geo_tendsto_punctured_of_eventuallyEq (g := fun r ↦ (1 + r) ^ 2)
      (by fun_prop) (by norm_num) ?_
    filter_upwards [self_mem_nhdsWithin] with r (h1 : r ≠ 1)
    have h1' : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    simp only [geoL, geoF]
    field_simp
  · refine geo_tendsto_punctured_of_eventuallyEq (g := fun r ↦ 1 / (r * (1 - r)))
      (by fun_prop (disch := norm_num)) (by norm_num) ?_
    filter_upwards [self_mem_nhdsWithin] with r (h1 : r ≠ -1)
    have h1' : 1 + r ≠ 0 := fun h ↦ h1 (eq_neg_of_add_eq_zero_right h)
    simp only [geoX]
    field_simp
  · refine geo_tendsto_punctured_of_eventuallyEq (g := fun r ↦ 1 / (1 - r) ^ 2)
      (by fun_prop (disch := norm_num)) (by norm_num) ?_
    filter_upwards [self_mem_nhdsWithin] with r (h1 : r ≠ -1)
    have h1' : 1 + r ≠ 0 := fun h ↦ h1 (eq_neg_of_add_eq_zero_right h)
    simp only [geoL, geoF]
    field_simp
  · refine geo_tendsto_cocompact_of_inv (g := fun w ↦ (w + 1) / (w - 1))
      (by fun_prop (disch := norm_num)) (by norm_num) fun r h0 h1 ↦ ?_
    have h1' : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    simp only [geoX]
    field_simp
  · refine geo_tendsto_cocompact_of_inv (g := fun w ↦ ((w + 1) / (w - 1)) ^ 2)
      (by fun_prop (disch := norm_num)) (by norm_num) fun r h0 h1 ↦ ?_
    have h1' : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    simp only [geoL, geoF]
    field_simp

end AJConjecture
