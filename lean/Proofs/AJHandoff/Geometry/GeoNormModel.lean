import Mathlib
import AJHandoff.Geometry.GeoCurveWeierstrass

/-!
# The smooth projective model over `ℂ` and its double cover of the `r`-line (G-NORM)

`GeoEllipticPoints` is the set of complex points of the projective curve `Y² = X³ - X`: the affine
nonsingular points and the point at infinity (`WeierstrassCurve.Affine.Point`). Since
`Δ ≠ 0` every affine solution is nonsingular. We topologize it by the injective map into
`ℙ¹(ℂ) × ℙ¹(ℂ) = OnePoint ℂ × OnePoint ℂ`, `(X, Y) ↦ (X, Y)`, `O ↦ (∞, ∞)`; its image is the
closure of the affine curve, so the space is compact Hausdorff (the topology agrees with the one
from `ℙ²(ℂ)`).

`geoCoverR : (X, Y) ↦ r = -X`, `O ↦ ∞` is continuous, and has fibres of cardinality `2` over
`r ∉ {0, 1, -1, ∞}` and `1` over the four branch points: a double cover of `ℙ¹_r` branched exactly
at `0, 1, -1, ∞`.

Route. Compactness: the image is closed in the compact space `OnePoint ℂ × OnePoint ℂ`, since
`|Y|² = |X³ - X|` forces `X → ∞ ⟺ Y → ∞` along sequences. Fibres: `Y² = -r(1 - r)(1 + r)` has two
roots unless the right side vanishes.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- `Y² = X³ - X` over `ℂ`. -/
abbrev geoWeierstrassℂ : WeierstrassCurve ℂ := geoWeierstrass.baseChange ℂ

/-- The embedding of the projective points into `ℙ¹(ℂ) × ℙ¹(ℂ)`. -/
def geoEllipticEmbed : geoWeierstrassℂ.toAffine.Point → OnePoint ℂ × OnePoint ℂ
  | .zero => (OnePoint.infty, OnePoint.infty)
  | .some x y _ => ((x : OnePoint ℂ), (y : OnePoint ℂ))

/-- The complex points of the smooth projective model `Y² = X³ - X`. -/
def GeoEllipticPoints : Type := geoWeierstrassℂ.toAffine.Point

instance : TopologicalSpace GeoEllipticPoints :=
  TopologicalSpace.induced geoEllipticEmbed inferInstance

/-- Over `ℂ`, every affine solution of the Weierstrass equation is nonsingular (`Δ ≠ 0`). -/
private theorem geo_equation_iff_nonsingular (X Y : ℂ) :
    geoWeierstrassℂ.toAffine.Equation X Y ↔ geoWeierstrassℂ.toAffine.Nonsingular X Y := by
  have : geoWeierstrassℂ.IsElliptic :=
    inferInstanceAs (geoWeierstrass.map (algebraMap ℚ ℂ)).IsElliptic
  exact WeierstrassCurve.Affine.equation_iff_nonsingular

/-- Every affine solution of `Y² = X³ - X` over `ℂ` is a (nonsingular) point of the model. -/
theorem geo_nonsingular_of_equation {X Y : ℂ} (h : Y ^ 2 = X ^ 3 - X) :
    geoWeierstrassℂ.toAffine.Nonsingular X Y :=
  (geo_equation_iff_nonsingular X Y).mp ((geoWeierstrass_equation_iff X Y).mpr h)

/-- The embedding is injective (so it is a topological embedding). -/
theorem geo_ellipticEmbed_injective : Function.Injective geoEllipticEmbed := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hxy <;>
    simp only [geoEllipticEmbed, Prod.mk.injEq, OnePoint.coe_eq_coe] at hxy
  · rfl
  · exact absurd hxy.1 (OnePoint.infty_ne_coe x')
  · exact absurd hxy.1 (OnePoint.coe_ne_infty x)
  · obtain ⟨rfl, rfl⟩ := hxy
    rfl

/-- A finite pair lies on the image of the model iff it solves `Y² = X³ - X`. -/
private theorem geo_coe_mem_range_ellipticEmbed_iff (x y : ℂ) :
    ((x : OnePoint ℂ), (y : OnePoint ℂ)) ∈ Set.range geoEllipticEmbed ↔ y ^ 2 = x ^ 3 - x := by
  constructor
  · rintro ⟨_ | ⟨x', y', h'⟩, hP⟩ <;>
      simp only [geoEllipticEmbed, Prod.mk.injEq, OnePoint.coe_eq_coe] at hP
    · exact absurd hP.1 (OnePoint.infty_ne_coe x)
    · obtain ⟨rfl, rfl⟩ := hP
      exact (geoWeierstrass_equation_iff _ _).mp h'.1
  · intro h
    exact ⟨.some x y (geo_nonsingular_of_equation h), rfl⟩

/-- No point of the model has exactly one infinite coordinate. -/
private theorem geo_infty_coe_notMem_range (y : ℂ) :
    (OnePoint.infty, (y : OnePoint ℂ)) ∉ Set.range geoEllipticEmbed := by
  rintro ⟨_ | ⟨x', y', h'⟩, hP⟩ <;> simp only [geoEllipticEmbed, Prod.mk.injEq] at hP
  · exact OnePoint.infty_ne_coe y hP.2
  · exact OnePoint.coe_ne_infty x' hP.1

/-- No point of the model has exactly one infinite coordinate. -/
private theorem geo_coe_infty_notMem_range (x : ℂ) :
    ((x : OnePoint ℂ), OnePoint.infty) ∉ Set.range geoEllipticEmbed := by
  rintro ⟨_ | ⟨x', y', h'⟩, hP⟩ <;> simp only [geoEllipticEmbed, Prod.mk.injEq] at hP
  · exact OnePoint.infty_ne_coe x hP.1
  · exact OnePoint.coe_ne_infty y' hP.2

/-- Near `∞` in `ℙ¹(ℂ)`, every finite point has large norm. -/
private theorem geo_eventually_large_near_infty (R : ℝ) :
    ∀ᶠ a in 𝓝 (OnePoint.infty : OnePoint ℂ), ∀ x : ℂ, a = (x : OnePoint ℂ) → R < ‖x‖ := by
  rw [OnePoint.nhds_infty_eq, eventually_sup, eventually_map, eventually_pure,
    coclosedCompact_eq_cocompact]
  refine ⟨(tendsto_norm_cocompact_atTop.eventually_gt_atTop R).mono fun z hz x hx ↦ ?_,
    fun x hx ↦ absurd hx (OnePoint.infty_ne_coe x)⟩
  rw [OnePoint.coe_eq_coe] at hx
  rwa [← hx]

/-- Near a finite point `↑y` of `ℙ¹(ℂ)`, every point is finite of norm `< ‖y‖ + 1`. -/
private theorem geo_eventually_bounded_near_coe (y : ℂ) :
    ∀ᶠ b in 𝓝 (y : OnePoint ℂ), ∃ y' : ℂ, b = (y' : OnePoint ℂ) ∧ ‖y'‖ < ‖y‖ + 1 := by
  rw [OnePoint.nhds_coe_eq, eventually_map]
  exact ((continuous_norm.tendsto y).eventually_lt_const (lt_add_one ‖y‖)).mono
    fun y' hy' ↦ ⟨y', rfl, hy'⟩

/-- The image of the model is closed in `ℙ¹(ℂ) × ℙ¹(ℂ)`. -/
private theorem geo_isClosed_range_ellipticEmbed : IsClosed (Set.range geoEllipticEmbed) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  rintro ⟨a, b⟩ hab
  rw [Set.mem_compl_iff] at hab
  induction a using OnePoint.rec with
  | infty =>
    induction b using OnePoint.rec with
    | infty => exact absurd ⟨.zero, rfl⟩ hab
    | coe y =>
      rw [nhds_prod_eq]
      filter_upwards [(geo_eventually_large_near_infty ((‖y‖ + 1) ^ 2 + 2)).prod_mk
        (geo_eventually_bounded_near_coe y)]
      rintro ⟨a', b'⟩ ⟨ha', y', rfl, hy'⟩
      induction a' using OnePoint.rec with
      | infty => exact geo_infty_coe_notMem_range y'
      | coe x =>
        rw [Set.mem_compl_iff, geo_coe_mem_range_ellipticEmbed_iff]
        intro hxy
        have hx := ha' x rfl
        have h1 : ‖y'‖ ^ 2 < ‖x‖ := by nlinarith [norm_nonneg y', norm_nonneg y]
        have h2 : ‖x‖ ≤ ‖x ^ 3 - x‖ := by
          have h3 : ‖x‖ ^ 3 - ‖x‖ ≤ ‖x ^ 3 - x‖ := by
            rw [← norm_pow]; exact norm_sub_norm_le _ _
          have hx2 : 2 < ‖x‖ := by nlinarith [sq_nonneg (‖y‖ + 1)]
          have h4 : 0 ≤ ‖x‖ * (‖x‖ ^ 2 - 2) := mul_nonneg (by linarith) (by nlinarith)
          nlinarith
        rw [← hxy, norm_pow] at h2
        linarith
  | coe x =>
    induction b using OnePoint.rec with
    | infty =>
      rw [nhds_prod_eq]
      filter_upwards [(geo_eventually_bounded_near_coe x).prod_mk
        (geo_eventually_large_near_infty ((‖x‖ + 1) ^ 3 + ‖x‖ + 2))]
      rintro ⟨a', b'⟩ ⟨⟨x', rfl, hx'⟩, hb'⟩
      induction b' using OnePoint.rec with
      | infty => exact geo_coe_infty_notMem_range x'
      | coe y =>
        rw [Set.mem_compl_iff, geo_coe_mem_range_ellipticEmbed_iff]
        intro hxy
        have hy := hb' y rfl
        have h1 : ‖x' ^ 3 - x'‖ ≤ (‖x‖ + 1) ^ 3 + (‖x‖ + 1) := by
          calc ‖x' ^ 3 - x'‖ ≤ ‖x'‖ ^ 3 + ‖x'‖ := by
                rw [← norm_pow]; exact norm_sub_le _ _
            _ ≤ (‖x‖ + 1) ^ 3 + (‖x‖ + 1) := by gcongr
        have h0 : 0 ≤ (‖x‖ + 1) ^ 3 := by positivity
        have hy1 : 1 ≤ ‖y‖ := by linarith [norm_nonneg x]
        have h2 : ‖y‖ ≤ ‖y‖ ^ 2 := by nlinarith
        rw [← norm_pow, hxy] at h2
        linarith
    | coe y =>
      rw [geo_coe_mem_range_ellipticEmbed_iff] at hab
      have hc : Continuous fun q : ℂ × ℂ ↦ q.2 ^ 2 - (q.1 ^ 3 - q.1) := by fun_prop
      have hopen : IsOpen (Prod.map ((↑) : ℂ → OnePoint ℂ) ((↑) : ℂ → OnePoint ℂ) ''
          {q : ℂ × ℂ | q.2 ^ 2 - (q.1 ^ 3 - q.1) ≠ 0}) :=
        (OnePoint.isOpenMap_coe.prodMap OnePoint.isOpenMap_coe) _
          (isOpen_ne_fun hc continuous_const)
      refine Filter.mem_of_superset (hopen.mem_nhds ⟨(x, y), sub_ne_zero.mpr hab, rfl⟩) ?_
      rintro _ ⟨⟨x', y'⟩, hq, rfl⟩
      rw [Set.mem_compl_iff, Prod.map_apply, geo_coe_mem_range_ellipticEmbed_iff]
      exact fun h ↦ hq (sub_eq_zero.mpr h)

/-- The embedding is a topological embedding. -/
private theorem geo_isEmbedding_ellipticEmbed :
    @Topology.IsEmbedding GeoEllipticPoints _ _ _ geoEllipticEmbed :=
  ⟨⟨rfl⟩, geo_ellipticEmbed_injective⟩

/-- The model is compact. -/
instance geo_compactSpace : CompactSpace GeoEllipticPoints := by
  rw [← isCompact_univ_iff, geo_isEmbedding_ellipticEmbed.isInducing.isCompact_iff]
  convert geo_isClosed_range_ellipticEmbed.isCompact using 1
  exact Set.image_univ

/-- The model is Hausdorff. -/
instance geo_t2Space : T2Space GeoEllipticPoints :=
  geo_isEmbedding_ellipticEmbed.t2Space

/-- The double cover `π : (X, Y) ↦ r = -X`, `O ↦ ∞`. -/
def geoCoverR : GeoEllipticPoints → OnePoint ℂ
  | .zero => OnePoint.infty
  | .some x _ _ => ((-x : ℂ) : OnePoint ℂ)

/-- `π` is continuous. -/
theorem geo_continuous_coverR : Continuous geoCoverR := by
  have hneg : Continuous (OnePoint.map fun x : ℂ ↦ -x) := by
    refine OnePoint.continuous_map continuous_neg ?_
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact tendsto_neg_cobounded
  have h : geoCoverR = (OnePoint.map fun x : ℂ ↦ -x) ∘ Prod.fst ∘ geoEllipticEmbed := by
    funext P
    rcases P with _ | ⟨x, y, h⟩ <;> rfl
  rw [h]
  exact hneg.comp (continuous_fst.comp continuous_induced_dom)

/-- The fibre of `π` over `∞` is the point at infinity. -/
private theorem geo_coverR_eq_infty_iff (P : geoWeierstrassℂ.toAffine.Point) :
    geoCoverR P = OnePoint.infty ↔ P = .zero := by
  rcases P with _ | ⟨x, y, h⟩
  · exact iff_of_true rfl rfl
  · exact iff_of_false (OnePoint.coe_ne_infty _) (by simp)

/-- The fibre of `π` over a finite `ρ` consists of the points with `X = -ρ`. -/
private theorem geo_coverR_eq_coe_iff (ρ : ℂ) (P : geoWeierstrassℂ.toAffine.Point) :
    geoCoverR P = (ρ : OnePoint ℂ) ↔
      ∃ (y : ℂ) (h : geoWeierstrassℂ.toAffine.Nonsingular (-ρ) y), P = .some (-ρ) y h := by
  rcases P with _ | ⟨x, y, h⟩
  · exact iff_of_false (OnePoint.infty_ne_coe ρ) (by simp)
  · change ((-x : ℂ) : OnePoint ℂ) = ρ ↔ _
    rw [OnePoint.coe_eq_coe]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · rintro rfl
      exact ⟨y, by simpa using h, by simp, rfl⟩
    · rintro ⟨y', h', hx, -⟩
      rw [hx, neg_neg]

/-- The fibre over a finite point `ρ ∉ {0, ±1}` has two points, else one. -/
private theorem geo_coverR_fiber_ncard_coe (ρ : ℂ) :
    {P : geoWeierstrassℂ.toAffine.Point | geoCoverR P = (ρ : OnePoint ℂ)}.ncard =
      if ρ = 0 ∨ ρ = 1 ∨ ρ = -1 then 1 else 2 := by
  have hy : ∀ y : ℂ, geoWeierstrassℂ.toAffine.Nonsingular (-ρ) y ↔ y ^ 2 = ρ - ρ ^ 3 := by
    intro y
    rw [← geo_equation_iff_nonsingular, geoWeierstrass_equation_iff]
    constructor <;> intro h <;> linear_combination h
  split_ifs with hρ
  · rw [Set.ncard_eq_one]
    have h0 : ρ - ρ ^ 3 = 0 := by
      rcases hρ with rfl | rfl | rfl <;> ring
    refine ⟨.some (-ρ) 0 ((hy 0).mpr (by rw [h0]; ring)), Set.ext fun P ↦ ?_⟩
    rw [Set.mem_ofPred_eq, geo_coverR_eq_coe_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, h, rfl⟩
      have hy0 : y = 0 := by
        have := (hy y).mp h
        rw [h0] at this
        exact pow_eq_zero_iff two_ne_zero |>.mp this
      subst hy0
      rfl
    · rintro rfl
      exact ⟨_, _, rfl⟩
  · rw [Set.ncard_eq_two]
    have h0 : ρ - ρ ^ 3 ≠ 0 := by
      intro h
      apply hρ
      have h' : ρ * (ρ - 1) * (ρ + 1) = 0 := by linear_combination -h
      rcases mul_eq_zero.mp h' with h' | h'
      · rcases mul_eq_zero.mp h' with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl (sub_eq_zero.mp h'))
      · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h'))
    obtain ⟨w, hw⟩ := IsAlgClosed.isSquare (ρ - ρ ^ 3)
    have hw0 : w ≠ 0 := by rintro rfl; exact h0 (by simpa using hw)
    have hw1 : w ^ 2 = ρ - ρ ^ 3 := by rw [hw]; ring
    have hw2 : (-w) ^ 2 = ρ - ρ ^ 3 := by rw [hw]; ring
    refine ⟨.some (-ρ) w ((hy w).mpr hw1), .some (-ρ) (-w) ((hy (-w)).mpr hw2), ?_,
      Set.ext fun P ↦ ?_⟩
    · simp only [ne_eq, WeierstrassCurve.Affine.Point.some.injEq, true_and]
      intro h
      exact hw0 (by linear_combination h / 2)
    · rw [Set.mem_ofPred_eq, geo_coverR_eq_coe_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨y, h, rfl⟩
        have h2 : (y - w) * (y + w) = 0 := by linear_combination (hy y).mp h - hw1
        rcases mul_eq_zero.mp h2 with h2 | h2
        · obtain rfl : y = w := sub_eq_zero.mp h2
          exact Or.inl rfl
        · obtain rfl : y = -w := eq_neg_of_add_eq_zero_left h2
          exact Or.inr rfl
      · rintro (rfl | rfl) <;> exact ⟨_, _, rfl⟩

open Classical in
/-- `π` is a double cover branched exactly over `0, 1, -1, ∞`. -/
theorem geo_coverR_fiber_ncard (r : OnePoint ℂ) :
    (geoCoverR ⁻¹' {r}).ncard =
      if r = ((0 : ℂ) : OnePoint ℂ) ∨ r = ((1 : ℂ) : OnePoint ℂ) ∨
          r = ((-1 : ℂ) : OnePoint ℂ) ∨ r = OnePoint.infty then 1 else 2 := by
  induction r using OnePoint.rec with
  | infty =>
    rw [ite_eq_left_iff.mpr fun h ↦ absurd (Or.inr (Or.inr (Or.inr rfl))) h, Set.ncard_eq_one]
    refine ⟨(.zero : geoWeierstrassℂ.toAffine.Point), Set.ext fun P ↦ ?_⟩
    exact geo_coverR_eq_infty_iff P
  | coe ρ =>
    have h := geo_coverR_fiber_ncard_coe ρ
    simp only [OnePoint.coe_eq_coe, OnePoint.coe_ne_infty, or_false]
    exact h

end AJConjecture
