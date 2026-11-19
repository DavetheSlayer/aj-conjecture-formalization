import Mathlib
import AJFamily.Volume.ArctanCatalan

/-!
# The radial profile of the ideal tetrahedron of shape `i` integrates to Catalan's constant

`hypVolProfile a = log((1 + a)² / (2a)) / (2(1 + a²))` is what is left of the hyperbolic volume
of the ideal tetrahedron with vertices `∞, 0, 1, i` after integrating out the height and the
distance along the ray of slope `a` from `0`. We show `∫₀^∞ hypVolProfile = G`:

* the substitution `a ↦ 1/a` maps the profile on `(1, ∞)` to the profile on `(0, 1)`;
* `2 · hypVolProfile a = -log a / (1 + a²) + (2 log(1 + a) - log 2) / (1 + a²)`;
* `∫₀¹ -log a / (1 + a²) da = ∫₀¹ arctan b / b db = G` by Tonelli (`-log a = ∫_a^1 db/b`);
* `∫₀¹ (2 log(1 + a) - log 2) / (1 + a²) da = 0` by the substitution `a ↦ (1 - a)/(1 + a)`.
-/

open MeasureTheory Set

noncomputable section

namespace AJConjecture

/-- The profile `a ↦ log((1 + a)² / (2a)) / (2(1 + a²))` of the hyperbolic volume of the ideal
tetrahedron of shape `i` along the rays from the vertex `0`. -/
def hypVolProfile (a : ℝ) : ℝ :=
  Real.log ((1 + a) ^ 2 / (2 * a)) / (2 * (1 + a ^ 2))

/-- For `f` continuous on `[p, q]` and nonnegative on `(p, q]`, the lower integral of `f` over
`(p, q]` is the interval integral. -/
lemma hypVol_lintegral_Ioc_ofReal {f : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hf : ContinuousOn f (Icc p q)) (h0 : ∀ x ∈ Ioc p q, 0 ≤ f x) :
    ∫⁻ x in Ioc p q, ENNReal.ofReal (f x) = ENNReal.ofReal (∫ x in p..q, f x) := by
  rw [intervalIntegral.integral_of_le hpq, ofReal_integral_eq_lintegral_ofReal]
  · exact hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact ae_restrict_of_forall_mem measurableSet_Ioc h0

/-- Catalan's constant is nonnegative. -/
lemma hypVol_catalanConstant_nonneg : 0 ≤ catalanConstant := by
  rw [← integral_arctan_div_self]
  exact intervalIntegral.integral_nonneg zero_le_one fun b hb ↦
    div_nonneg (Real.arctan_nonneg.2 hb.1) hb.1

/-- `∫₀¹ -log a / (1 + a²) da = G`, as a lower integral. -/
lemma hypVol_lintegral_neg_log_div : ∫⁻ a in Ioc (0 : ℝ) 1,
    ENNReal.ofReal (-Real.log a / (1 + a ^ 2)) = ENNReal.ofReal catalanConstant := by
  set F : ℝ → ℝ → ENNReal := fun a b ↦
    if a < b then ENNReal.ofReal (b⁻¹ * (1 + a ^ 2)⁻¹) else 0 with hF
  have hFm : Measurable (Function.uncurry F) := by
    refine Measurable.ite (measurableSet_lt measurable_fst measurable_snd) ?_ measurable_const
    fun_prop
  have h1 : ∀ a ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (-Real.log a / (1 + a ^ 2)) =
      ∫⁻ b in Ioc 0 1, F a b := by
    intro a ha
    have e : ∀ b, F a b = (Ioi a).indicator (fun b ↦ ENNReal.ofReal (b⁻¹ * (1 + a ^ 2)⁻¹)) b :=
      fun b ↦ by simp only [hF, indicator_apply, mem_Ioi]
    simp_rw [e]
    have hs : Ioi a ∩ Ioc 0 1 = Ioc a 1 := by
      ext b
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, ha.1.trans h1, h2⟩
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hs,
      hypVol_lintegral_Ioc_ofReal ha.2]
    · rw [intervalIntegral.integral_mul_const, integral_inv_of_pos ha.1 one_pos, div_eq_mul_inv,
        div_eq_mul_inv, one_mul, Real.log_inv]
    · exact ContinuousOn.mul (continuousOn_inv₀.mono fun b hb ↦ (ha.1.trans_le hb.1).ne')
        continuousOn_const
    · intro b hb
      have : 0 < b := ha.1.trans hb.1
      positivity
  have h2 : ∀ b ∈ Ioc (0 : ℝ) 1, ∫⁻ a in Ioc 0 1, F a b =
      ENNReal.ofReal (Real.arctan b / b) := by
    intro b hb
    have e : ∀ a, F a b = (Iio b).indicator (fun a ↦ ENNReal.ofReal (b⁻¹ * (1 + a ^ 2)⁻¹)) a :=
      fun a ↦ by simp only [hF, indicator_apply, mem_Iio]
    simp_rw [e]
    have hs : Iio b ∩ Ioc 0 1 = Ioo 0 b := by
      ext a
      simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, h2.le.trans hb.2⟩
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, hs,
      setLIntegral_congr Ioo_ae_eq_Ioc, hypVol_lintegral_Ioc_ofReal hb.1.le]
    · rw [intervalIntegral.integral_const_mul]
      simp only [← one_div, integral_one_div_one_add_sq, Real.arctan_zero, sub_zero]
      rw [one_div_mul_eq_div]
    · fun_prop (disch := intro a _; positivity)
    · intro a _
      have : 0 < b := hb.1
      positivity
  rw [setLIntegral_congr_fun measurableSet_Ioc h1,
    lintegral_lintegral_swap hFm.aemeasurable,
    setLIntegral_congr_fun measurableSet_Ioc h2, ← integral_arctan_div_self,
    intervalIntegral.integral_of_le zero_le_one, ofReal_integral_eq_lintegral_ofReal]
  · refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      (Real.continuous_arctan.measurable.div measurable_id).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun b hb ↦ ?_)
    rw [Real.norm_eq_abs, abs_div, div_le_one (abs_pos.2 hb.1.ne')]
    exact Real.abs_arctan_le_abs
  · exact ae_restrict_of_forall_mem measurableSet_Ioc fun b hb ↦
      div_nonneg (Real.arctan_nonneg.2 hb.1.le) hb.1.le

/-- `∫₀¹ (2 log(1 + a) - log 2) / (1 + a²) da = 0`, by the substitution `a ↦ (1 - a)/(1 + a)`. -/
lemma hypVol_integral_log_one_add_div :
    ∫ a in (0 : ℝ)..1, (2 * Real.log (1 + a) - Real.log 2) / (1 + a ^ 2) = 0 := by
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hfd : ∀ b ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun b : ℝ ↦ (1 - b) / (1 + b)) (-2 / (1 + b) ^ 2) b := by
    intro b hb
    have h1 : (1 + b) ≠ 0 := by linarith [hb.1]
    have := ((hasDerivAt_id' b).const_sub 1).div ((hasDerivAt_id' b).const_add 1) h1
    convert this using 1
    field_simp
    ring
  have himg : (fun b : ℝ ↦ (1 - b) / (1 + b)) '' Icc 0 1 ⊆ Icc 0 1 := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : 0 < 1 + b := by linarith [hb.1]
    exact ⟨div_nonneg (by linarith [hb.2]) h1.le, (div_le_one h1).2 (by linarith [hb.1])⟩
  have hgc : ContinuousOn (fun a : ℝ ↦ (2 * Real.log (1 + a) - Real.log 2) / (1 + a ^ 2))
      (Icc 0 1) := by
    refine ContinuousOn.div ?_ (continuous_const.add (continuous_pow 2)).continuousOn
      fun a _ ↦ (by positivity : (1 : ℝ) + a ^ 2 ≠ 0)
    refine ContinuousOn.sub (ContinuousOn.mul continuousOn_const ?_) continuousOn_const
    exact ContinuousOn.log (continuous_const.add continuous_id).continuousOn
      fun a ha ↦ by linarith [ha.1]
  have hf'c : ContinuousOn (fun b : ℝ ↦ -2 / (1 + b) ^ 2) (Icc 0 1) :=
    ContinuousOn.div continuousOn_const
      ((continuous_const.add continuous_id).pow 2).continuousOn fun b hb ↦ by
      have : 0 < 1 + b := by linarith [hb.1]
      exact (by positivity : (1 + b) ^ 2 ≠ 0)
  have hsub := intervalIntegral.integral_comp_mul_deriv''
    (f := fun b : ℝ ↦ (1 - b) / (1 + b)) (f' := fun b : ℝ ↦ -2 / (1 + b) ^ 2)
    (g := fun a : ℝ ↦ (2 * Real.log (1 + a) - Real.log 2) / (1 + a ^ 2)) (a := 0) (b := 1)
    (by rw [hI]; exact fun b hb ↦ (hfd b hb).continuousAt.continuousWithinAt)
    (fun b hb ↦ by
      rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at hb
      exact (hfd b (Ioo_subset_Icc_self hb)).hasDerivWithinAt)
    (by rw [hI]; exact hf'c) (by rw [hI]; exact hgc.mono himg)
  have hpt : ∀ b ∈ uIcc (0 : ℝ) 1,
      ((fun a : ℝ ↦ (2 * Real.log (1 + a) - Real.log 2) / (1 + a ^ 2)) ∘
        (fun b : ℝ ↦ (1 - b) / (1 + b))) b * (-2 / (1 + b) ^ 2) =
      (2 * Real.log (1 + b) - Real.log 2) / (1 + b ^ 2) := by
    intro b hb
    rw [hI] at hb
    have h1 : 0 < 1 + b := by linarith [hb.1]
    have e1 : 1 + (1 - b) / (1 + b) = 2 / (1 + b) := by field_simp; ring
    simp only [Function.comp, e1]
    rw [Real.log_div two_ne_zero h1.ne']
    field_simp
    ring
  rw [intervalIntegral.integral_congr hpt] at hsub
  norm_num at hsub
  rw [intervalIntegral.integral_symm 1 0] at hsub ⊢
  linarith

/-- The substitution `a ↦ 1/a` maps the profile on `(1, ∞)` to the profile on `(0, 1)`. -/
lemma hypVol_lintegral_profile_Ioi_one : ∫⁻ a in Ioi (1 : ℝ), ENNReal.ofReal (hypVolProfile a) =
    ∫⁻ a in Ioc 0 1, ENNReal.ofReal (hypVolProfile a) := by
  rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
  have himg : (fun x : ℝ ↦ x⁻¹) '' Ioi 1 = Ioo 0 1 := by
    rw [Set.image_inv_eq_inv, Set.inv_Ioi₀ one_pos, inv_one]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (f' := fun x ↦ -(x ^ 2)⁻¹)
    (fun x hx ↦ (hasDerivAt_inv (zero_lt_one.trans hx).ne').hasDerivWithinAt)
    inv_injective.injOn]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_neg, abs_of_pos (by positivity)]
  simp only [hypVolProfile]
  have e : (1 + x⁻¹) ^ 2 / (2 * x⁻¹) = (1 + x) ^ 2 / (2 * x) := by
    field_simp
    ring
  rw [e]
  field_simp
  ring

/-- The profile is nonnegative for `a > 0`, since `(1 + a)² ≥ 2a`. -/
lemma hypVolProfile_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ hypVolProfile a := by
  refine div_nonneg (Real.log_nonneg ((one_le_div (by positivity)).2 ?_)) (by positivity)
  nlinarith [sq_nonneg a]

/-- `∫₀^∞ log((1 + a)² / (2a)) / (2(1 + a²)) da = G`. -/
theorem hypVol_lintegral_profile :
    ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (hypVolProfile a) = ENNReal.ofReal catalanConstant := by
  set A : ℝ → ℝ := fun a ↦ -Real.log a / (1 + a ^ 2) with hAdef
  set B : ℝ → ℝ := fun a ↦ (2 * Real.log (1 + a) - Real.log 2) / (1 + a ^ 2) with hBdef
  have hAm : Measurable A := by fun_prop
  have hAnn : ∀ a ∈ Ioc (0 : ℝ) 1, 0 ≤ A a := fun a ha ↦
    div_nonneg (neg_nonneg.2 (Real.log_nonpos ha.1.le ha.2)) (by positivity)
  have hAlin : ∫⁻ a in Ioc (0 : ℝ) 1, ENNReal.ofReal (A a) = ENNReal.ofReal catalanConstant :=
    hypVol_lintegral_neg_log_div
  have hAint : IntegrableOn A (Ioc 0 1) := by
    have h := integrable_toReal_of_lintegral_ne_top (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (f := fun a ↦ ENNReal.ofReal (A a)) hAm.ennreal_ofReal.aemeasurable
      (by rw [hAlin]; exact ENNReal.ofReal_ne_top)
    refine h.congr (ae_restrict_of_forall_mem measurableSet_Ioc fun a ha ↦ ?_)
    exact ENNReal.toReal_ofReal (hAnn a ha)
  have hA : ∫ a in Ioc (0 : ℝ) 1, A a = catalanConstant := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioc hAnn)
      hAm.aestronglyMeasurable, hAlin, ENNReal.toReal_ofReal hypVol_catalanConstant_nonneg]
  have hBc : ContinuousOn B (Icc 0 1) := by
    refine ContinuousOn.div ?_ (continuous_const.add (continuous_pow 2)).continuousOn
      fun a _ ↦ (by positivity : (1 : ℝ) + a ^ 2 ≠ 0)
    refine ContinuousOn.sub (ContinuousOn.mul continuousOn_const ?_) continuousOn_const
    exact ContinuousOn.log (continuous_const.add continuous_id).continuousOn
      fun a ha ↦ by linarith [ha.1]
  have hBint : IntegrableOn B (Ioc 0 1) := hBc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hB : ∫ a in Ioc (0 : ℝ) 1, B a = 0 := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact hypVol_integral_log_one_add_div
  have hpm : Measurable fun a ↦ ENNReal.ofReal (hypVolProfile a) := by
    unfold hypVolProfile
    fun_prop
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl), hypVol_lintegral_profile_Ioi_one,
    ← lintegral_add_left hpm]
  have hsum : ∀ a ∈ Ioc (0 : ℝ) 1, hypVolProfile a + hypVolProfile a = A a + B a := by
    intro a ha
    have ha0 := ha.1
    simp only [hypVolProfile, hAdef, hBdef]
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow,
      Real.log_mul two_ne_zero ha0.ne']
    field_simp
    ring
  have hpt : ∀ a ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (hypVolProfile a) +
      ENNReal.ofReal (hypVolProfile a) = ENNReal.ofReal (A a + B a) := by
    intro a ha
    rw [← ENNReal.ofReal_add (hypVolProfile_nonneg ha.1) (hypVolProfile_nonneg ha.1), hsum a ha]
  rw [setLIntegral_congr_fun measurableSet_Ioc hpt, ← ofReal_integral_eq_lintegral_ofReal
    (f := fun a ↦ A a + B a) (hAint.add hBint), integral_add hAint hBint, hA, hB, add_zero]
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun a ha ↦ ?_
  show 0 ≤ A a + B a
  rw [← hsum a ha]
  exact add_nonneg (hypVolProfile_nonneg ha.1) (hypVolProfile_nonneg ha.1)

end AJConjecture
