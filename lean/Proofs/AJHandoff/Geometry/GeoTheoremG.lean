import Mathlib
import AJFamily.Volume.MahlerExtraFactor
import AJHandoff.Geometry.GeoKernelFormula
import AJHandoff.Geometry.GeoActionBranch
import AJHandoff.Geometry.GeoCurveDegreeTwo
import AJHandoff.Geometry.GeoNormIntegralClosure
import AJHandoff.Geometry.GeoRegCompact
import AJHandoff.Geometry.GeoK2Symbol
import AJHandoff.Geometry.GeoShapeMarking
import AJHandoff.Geometry.GeoVolumeSigned
import AJHandoff.Geometry.GeoPhysDiagonal
import AJHandoff.Geometry.GeoVolumeHyperbolic
import AJHandoff.Geometry.GeoSliceShapes
import AJHandoff.Geometry.GeoReducedIntegral
import AJHandoff.Geometry.GeoPhysReduced
import AJHandoff.Geometry.GeoPhysUncond
import AJHandoff.Geometry.GeoKernelChannel
import AJHandoff.Geometry.GeoBlochWignerSymm
import AJHandoff.Geometry.GeoNormModel

/-!
# Theorem G, assembled

Each unit in its own domain and orientation, reported separately:

* G-KERNEL: the coefficient-extraction formula for the coloured Jones function of every library
  knot `whiteheadTorusKnot k`, and the bijection of the homogeneous channel `Q = -1` onto
  `E_x(L) = 0`;
* G-CURVE: `E` is birational to `Y² = X³ - X` (`j = 1728`); the function fields are isomorphic by
  the explicit `X = -r`, `Y = M r (1 - r)`, of degree two over the `r`-line;
* G-NORM: the integral closure of the Laurent coordinate ring of `E` is the coordinate ring of the
  elliptic curve minus four points; the projective model is compact and double covers `ℙ¹_r`
  branched exactly at `0, 1, -1, ∞`;
* G-REG, G-REG-COMPACT: `d(U ∘ r) = η(M, L)` on the smooth torus locus; `Ũ ∘ π` continuous on the
  compact model;
* G-K2: `{M, L} = 0` in `K₂ᴹ(ℚ̄(E)) ⊗ ℚ`;
* G-ACTION: the channel action is a branch on its domain; on admissible lifts
  `dS_crit = log L · dlog x` (envelope); `dV_S = -2η(M, L)`, `V_S + 2U` is constant, and the branch
  normalized at `r = 1/2` equals `-2U`;
* G-MAHLER (library): `m(E) = 4G/π`;
* G-SHAPE, MARK: the pattern eigenvalue pairs over the completed chart are exactly `E ∩ {M ≠ 0}`,
  with `(M, L) = (u, v⁻¹)` forced by the library's peripheral words;
* G-VOL: signed slice volume `-2U(r)`, `4G` at `w = i`, mirror pullback `-4G`, unsigned `4G`, and
  the hyperbolic (metric) volume `G` of the ideal tetrahedron of shape `i`;
* G-PHYS: conditional on `ZhengEstimates a`, the diagonal at `q_N` is asymptotic to the nonzero
  leading term from the window.

No inference from a geometric period to an Ore minimum is made. The assembly is a conjunction of the
unit theorems.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

open Classical in
/-- Theorem G (bounded v1), as the conjunction of its separately proved units. -/
theorem geo_theoremG :
    -- G-KERNEL
    (∀ (k : ℕ) (hk : 1 ≤ k) (N B : ℕ), 1 ≤ N → N ≤ B →
      laurentToField (coloredJones (whiteheadTorusKnot k hk) N) =
        (RatFunc.X : RatFunc ℚ) ^ (4 * (N : ℤ) ^ 2 - 2 * N - 2) *
          PowerSeries.coeff (N - 1)
            (∑ n ∈ Finset.range B,
              PowerSeries.C (torusOddColor (2 * k + 1) n) * geoClaspGen N n)) ∧
    (∀ x : ℂ, x ≠ 0 → x ^ 2 ≠ 1 →
      Set.BijOn (geoChannelL x) {y | geoChannelT x y = 0}
        {L | L ^ 2 - (x ^ 2 - 4 * x + 1) * L + x ^ 2 = 0}) ∧
    (∀ (a : ℕ) {x y : ℂ}, x ≠ 0 → x ^ 2 ≠ 1 → (y ≠ 0 ∧ y ≠ 1 ∧ y ≠ x ∧ y ≠ -x ∧ y ≠ -1) →
      (geoRatioQ a 1 x (-1) (-y) = 1 ∧ geoRatioZ 1 x (-1) (-y) = 1 ↔ geoChannelT x y = 0) ∧
        geoRatioX 1 x (-1) (-y) = geoChannelL x y) ∧
    -- G-CURVE
    Set.BijOn geoToWeierstrass GeoSmoothTorusLocus GeoWeierstrassOpen ∧
    geoWeierstrass.j = 1728 ∧
    (∃ e : GeoFunFieldE ≃+* geoWeierstrass.toAffine.FunctionField,
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
            (algebraMap GeoCoordE GeoFunFieldE geoMer ^ 2 - 1)))) ∧
    Module.finrank (IntermediateField.adjoin ℚ {geoRfun}) GeoFunFieldE = 2 ∧
    -- G-NORM
    (∃ e : GeoLaurentE ≃+* geoLaurentImage,
      (e (algebraMap GeoCoordE GeoLaurentE geoMer) : GeoKW) = geoNuM ∧
        (e (algebraMap GeoCoordE GeoLaurentE geoLong) : GeoKW) = geoNuL) ∧
    (integralClosure geoLaurentImage GeoKW).restrictScalars ℚ = geoPuncturedImage ∧
    CompactSpace GeoEllipticPoints ∧
    (∀ r : OnePoint ℂ, (geoCoverR ⁻¹' {r}).ncard =
      if r = ((0 : ℂ) : OnePoint ℂ) ∨ r = ((1 : ℂ) : OnePoint ℂ) ∨
          r = ((-1 : ℂ) : OnePoint ℂ) ∨ r = OnePoint.infty then 1 else 2) ∧
    -- G-REG
    (∀ {γ : ℝ → ℂ × ℂ} {γ' : ℂ × ℂ} {t : ℝ}, HasDerivAt γ γ' t →
      (∀ᶠ s in 𝓝 t, γ s ∈ GeoSmoothTorusLocus) →
      HasDerivAt (fun s ↦ geoRegPrimitive (geoCurveR (γ s)))
        (geoEta (γ t).1 (γ t).2 γ'.1 γ'.2) t) ∧
    (geoRegPrimitive 0 = 0 ∧ geoRegPrimitive 1 = 0 ∧ geoRegPrimitive (-1) = 0 ∧
      geoRegPrimitive Complex.I = 2 * catalanConstant ∧
      geoRegPrimitive (-Complex.I) = -(2 * catalanConstant)) ∧
    -- G-REG-COMPACT
    (Continuous (geoRegPrimitiveP1 ∘ geoCoverR) ∧
      (∀ q ∈ GeoPuncturedModel, q.1 ^ 2 ≠ -1 →
        geoNormMap q ∈ GeoSmoothTorusLocus ∧
          geoRegPrimitive (geoCurveR (geoNormMap q)) = geoRegPrimitiveP1 (-q.1 : ℂ)) ∧
      (∀ P : GeoEllipticPoints, (geoCoverR P = ((0 : ℂ) : OnePoint ℂ) ∨
          geoCoverR P = ((1 : ℂ) : OnePoint ℂ) ∨ geoCoverR P = ((-1 : ℂ) : OnePoint ℂ) ∨
          geoCoverR P = OnePoint.infty) → geoRegPrimitiveP1 (geoCoverR P) = 0) ∧
      (∀ P : GeoEllipticPoints, geoCoverR P = (Complex.I : OnePoint ℂ) →
        geoRegPrimitiveP1 (geoCoverR P) = 2 * catalanConstant) ∧
      (∀ P : GeoEllipticPoints, geoCoverR P = ((-Complex.I : ℂ) : OnePoint ℂ) →
        geoRegPrimitiveP1 (geoCoverR P) = -(2 * catalanConstant))) ∧
    (∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ¬ ∃ c : ℝ, Tendsto (fun p ↦ geoRegPrimitive (geoCurveR p))
      (𝓝[GeoSmoothTorusLocus] (ε, -1)) (𝓝 c)) ∧
    -- G-K2
    geoSymbol (Units.mk0 geoMerBar geoMerBar_ne_zero) (Units.mk0 geoLongBar geoLongBar_ne_zero)
      ⊗ₜ[ℤ] (1 : ℚ) = 0 ∧
    -- G-ACTION: the channel action is a branch; envelope dS_crit = log L dlog x on admissible
    -- lifts; dV_S = -2η, V_S + 2U constant, and V_S = -2U after normalizing at r = 1/2
    (∀ a : ℕ, GeoChannelActionBranch (geoChannelAction a) geoChannelActionDomain) ∧
    (∀ a : ℕ, ∃ ε > 0, ∀ r ∈ Metric.ball (2 : ℂ) ε,
      (Complex.log (-geoX r) + Real.pi * Complex.I,
          Complex.log (1 / r) + Real.pi * Complex.I) ∈ geoChannelActionDomain ∧
        fderiv ℂ (geoChannelAction a)
          (Complex.log (-geoX r) + Real.pi * Complex.I,
            Complex.log (1 / r) + Real.pi * Complex.I) (0, 1) = 0) ∧
    (∀ {S : ℂ × ℂ → ℂ} {Ω : Set (ℂ × ℂ)}, GeoChannelActionBranch S Ω →
      ∀ {ℓ : ℂ → ℂ × ℂ} {r : ℂ}, (r ≠ 0 ∧ r ≠ 1 ∧ r ≠ -1 ∧ r ^ 2 ≠ -1) →
      DifferentiableAt ℂ ℓ r → ℓ r ∈ Ω →
      (Complex.exp (ℓ r).1 = geoX r ∧ Complex.exp (ℓ r).2 = -1 / r) →
      fderiv ℂ S (ℓ r) (0, 1) = 0 →
      HasDerivAt (fun ρ ↦ S (ℓ ρ)) (fderiv ℂ S (ℓ r) (1, 0) * deriv (fun ρ ↦ (ℓ ρ).1) r) r ∧
        Complex.exp (fderiv ℂ S (ℓ r) (1, 0)) = geoL r) ∧
    (∀ {Ω : Set ℂ}, IsOpen Ω → IsPreconnected Ω → (∀ r ∈ Ω, r ≠ 0 ∧ r ≠ 1 ∧ r ≠ -1) →
      ∀ {lx lL s : ℂ → ℂ}, DifferentiableOn ℂ lx Ω → DifferentiableOn ℂ lL Ω →
      (∀ r ∈ Ω, Complex.exp (lx r) = geoX r) → (∀ r ∈ Ω, Complex.exp (lL r) = geoL r) →
      (∀ r ∈ Ω, HasDerivAt s (lL r * deriv lx r) r) →
      (∀ {γ : ℝ → ℂ × ℂ} {γ' : ℂ × ℂ} {t : ℝ}, HasDerivAt γ γ' t →
          (∀ᶠ τ in 𝓝 t, γ τ ∈ GeoSmoothTorusLocus ∧ geoCurveR (γ τ) ∈ Ω) →
          HasDerivAt (fun τ ↦ (s (geoCurveR (γ τ))).im -
              (lL (geoCurveR (γ τ))).im * (lx (geoCurveR (γ τ))).re)
            (-2 * geoEta (γ t).1 (γ t).2 γ'.1 γ'.2) t) ∧
        (∃ c : ℝ, ∀ r ∈ Ω, (s r).im - (lL r).im * (lx r).re + 2 * geoRegPrimitive r = c) ∧
        ((1 / 2 : ℂ) ∈ Ω → (s (1 / 2)).im - (lL (1 / 2)).im * (lx (1 / 2)).re = 0 →
          ∀ r ∈ Ω, (s r).im - (lL r).im * (lx r).re = -2 * geoRegPrimitive r)) ∧
    -- G-MAHLER (library)
    logMahlerMeasure₂ extraFactorℂ = 4 * catalanConstant / Real.pi ∧
    -- G-SHAPE and MARK
    (∀ z : Fin 4 → ℂ, WhiteheadGluing z → (whiteheadPeripheral z).1 = 1 →
      (whiteheadPeripheral z).2.1 = -1 → ∃ w : ℂ, w ≠ 0 ∧ w ≠ 1 ∧ w ≠ -1 ∧ z = geoSliceShapes w) ∧
    (∀ (w u : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
        (hu : u ^ 2 = (1 + w) / (w * (1 - w))),
      GeoAxisCompleted (geoPatternShapeRep w u hw0 hw1 hwm1 hu) ∧
        GeoPatternEigenPair (geoPatternShapeRep w u hw0 hw1 hwm1 hu) (u, (w ^ 2)⁻¹) ∧
        GeoPatternEigenPair (geoPatternShapeRep w u hw0 hw1 hwm1 hu) (u⁻¹, w ^ 2)) ∧
    {p : ℂ × ℂ | ∃ (w u : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
        (hu : u ^ 2 = (1 + w) / (w * (1 - w))),
        GeoPatternEigenPair (geoPatternShapeRep w u hw0 hw1 hwm1 hu) p} =
      {p : ℂ × ℂ | evalPoint extraFactorℂ p = 0 ∧ p.1 ≠ 0} ∧
    -- G-VOL
    (∀ r : ℂ, r ≠ -1 → r ≠ 1 →
      ∑ j, blochWigner (geoSliceShapes ((1 - r) / (1 + r)) j) = -2 * geoRegPrimitive r) ∧
    ∑ j, blochWigner (geoSliceShapes Complex.I j) = 4 * catalanConstant ∧
    ∑ j, blochWigner (geoSliceShapes Complex.I j)⁻¹ = -(4 * catalanConstant) ∧
    (∀ z : Fin 4 → ℂ, WhiteheadGluing z → WhiteheadComplete z →
      |∑ j, blochWigner (z j)| = 4 * catalanConstant) ∧
    geoHypMeasure geoIdealTetI = ENNReal.ofReal catalanConstant ∧
    -- G-PHYS: from the actual knot to Zheng's diagonal, then the asymptotics (conditional)
    (∀ (k : ℕ) (hk : 1 ≤ k) (N : ℕ), 1 ≤ N →
      laurentToField (coloredJones (whiteheadTorusKnot k hk) N) =
        quantumInt N * torusReducedFormula (2 * k + 1) N) ∧
    (∀ k N : ℕ, 1 ≤ k → 1 ≤ N →
      ∃ P : LaurentPolynomial ℤ, laurentToField P = torusReducedFormula (2 * k + 1) N) ∧
    (∀ (a N : ℕ) (P : LaurentPolynomial ℤ), 1 ≤ N → laurentToField P = torusReducedFormula a N →
      LaurentPolynomial.eval₂ (Int.castRingHom ℂ)
          (Units.mk0 (Complex.exp (Real.pi * Complex.I / (2 * N))) (Complex.exp_ne_zero _)) P =
        geoZhengDiagonal a N) ∧
    (∀ a N n : ℕ, 1 ≤ N →
      geoPhasePow N n (-(8 * a : ℝ)) = geoRootQ N ^ (-(2 * (a : ℤ) * n * (n + 1)))) ∧
    (∀ δ : ℝ, 1 / 2 < δ → δ < 1 →
      ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N n i : ℕ, N₀ ≤ N → n + i < N → GeoInWindow N ((N : ℝ) ^ δ) n i →
        let q := geoRootQ N
        let zi := (1 - q ^ (i + 1)) / (1 - q ^ (n + i + 1))
        let zj := (1 - q ^ (N - n - i)) / (1 - q ^ (N - i))
        ‖q ^ n + 1‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧ ‖q ^ i - Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧
          ‖q ^ (N - 1 - n - i) - Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧
          ‖zi + Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧ ‖zj + Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧
          ‖q ^ n * zi - Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧
          ‖q ^ n * zj - Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1)) ∧
    (∀ a : ℕ, geoRatioQ a 1 1 (-1) (-Complex.I) = 1 ∧ geoRatioZ 1 1 (-1) (-Complex.I) = 1 ∧
      geoRatioX 1 1 (-1) (-Complex.I) = -1 ∧ geoChannelT 1 Complex.I = 0 ∧
      -2 * geoRegPrimitive (-Complex.I) = 4 * catalanConstant) ∧
    (∀ a : ℕ, 3 ≤ a → Odd a → ZhengEstimates a →
      (∀ N : ℕ, 1 ≤ N → geoZhengLeading a N ≠ 0) ∧
        Tendsto (fun N : ℕ ↦ geoZhengDiagonal a N / geoZhengLeading a N) atTop (𝓝 1)) := by
  refine ⟨fun k hk N B hN hB ↦ geo_coloredJones_eq_extract k hk N B hN hB,
    fun x hx0 hx1 ↦ (geo_channel_bijOn hx0 hx1).1,
    fun a x y hx0 hx1 hy ↦ geo_channel_critical_iff a hx0 hx1 hy,
    geo_weierstrass_birational.1, geoWeierstrass_j, geo_functionField_equiv,
    geo_finrank_functionField_adjoin_rfun,
    geo_laurent_equiv, geo_integralClosure_laurent, inferInstance, geo_coverR_fiber_ncard,
    fun hγ hE ↦ geo_reg_hasDerivAt hγ hE, geo_regPrimitive_values, geo_regCompact,
    geo_regPrimitive_no_limit_at_node, geo_K2_functionField,
    geo_channelAction_branch, geo_channelAction_admissible_near_two_lift,
    fun hS _ _ hr hℓ hℓΩ hexp hadm ↦
      geo_action_envelope hS hr hℓ hℓΩ hexp hadm,
    fun hΩ hconn hsing _ _ _ hlx hlL hexpx hexpL hs ↦
      geo_action_normalized hΩ hconn hsing hlx hlL hexpx hexpL hs,
    mahlerMeasure_extraFactor.2, geo_sliceShapes_of_complete,
    fun w u hw0 hw1 hwm1 hu ↦
      ⟨(geo_shape_marking hw0 hw1 hwm1 hu).1, (geo_shape_marking hw0 hw1 hwm1 hu).2.1,
        (geo_shape_marking hw0 hw1 hwm1 hu).2.2.1⟩,
    geo_shape_marking_image, fun r hr hr1 ↦ geo_slice_signedVolume_eq_action hr hr1,
    geo_slice_complete_volumes.1,
    (geo_mirror_signedVolume (fun _ ↦ 1) fun _ ↦ one_ne_zero).2, geo_unsigned_volume,
    geo_hypVolume_idealTetI, laurentToField_coloredJones_whiteheadTorusKnot_eq,
    exists_laurent_torusReducedFormula,
    fun a N P hN hP ↦ geo_reduced_value_eq_zhengDiagonal a N hN P hP,
    geo_phase_pow_eq_homogeneous, geo_phys_coordinates, fun a ↦ ?_,
    fun a ha hodd hZ ↦ ⟨(geo_phys_diagonal a ha hodd hZ).2.2.1,
      (geo_phys_diagonal a ha hodd hZ).2.2.2.2⟩⟩
  obtain ⟨h1, h2, h3, h4, -, -, -, h8⟩ := geo_phys_endpoint a
  exact ⟨h1, h2, h3, h4, h8⟩

end AJConjecture
