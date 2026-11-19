import Mathlib
import AJHandoff.Geometry.GeoPhysDefs
import AJHandoff.Geometry.GeoKernelChannel
import AJHandoff.Geometry.GeoBlochWignerSymm

/-!
# The unconditional parts of the physical diagonal (G-PHYS)

* Phase identity (source (3)): `a_n^{-8a} = q_N^{-2an(n+1)} = v_n(q_N)`, the homogeneous solution of
  the companion recurrence at the root; the exponents differ by `4πi a n ∈ 2πiℤ`.
* Periodicity (4.3): `A⁺_{a,2}(N + 8a, k) = A⁺_{a,2}(N, k)`; with Proposition 4.1 this gives
  `c_a N^{5/2} ≤ |C_{a,N}| ≤ C_a N^{5/2}`.
* `S₀ > 0`.
* The coefficient-extraction coordinates (source (9)–(10)): with `x = q_N^N = 1`, the dual ratios
  `z_i = (1 - q^{i+1})/(1 - q^{n+i+1})`, `z_j = (1 - q^{j+1})/(1 - q^{n+j+1})`, `j = N - 1 - n - i`,
  satisfy, uniformly on the window `|n - N/2| + |i - N/4| < N^δ` (`1/2 < δ < 1`),
  `q^n → -1`, `q^i, q^j → i`, `z_i, z_j → -i`, `y = q^n z → i`, with errors `O(N^{δ-1})`.
* The limit point `(x, Q, z, y) = (1, -1, -i, i)` solves the formal critical equations of
  `GeoKernelRatios` with `L = -1`; `M = t^{2N} = -1` on `t = -e^{πi/(2N)}`; the normalized
  parameters are `r = 1/y = -i`, `w = (y - 1)/(y + 1) = i`; the normalized action there is
  `-2U(-i) = 2U(i) = 4G`.

Route. `exp` arithmetic; `|e^{iθ} - e^{iφ}| ≤ |θ - φ|`; the denominators `1 - q^{n+i+1}` tend to
`1 + i` and are bounded away from `0` on the window; `geo_regPrimitive_values`.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- `q_N^m = exp(m · 2πi/N)` for integer `m`. -/
private theorem geoRootQ_zpow_eq_exp (N : ℕ) (m : ℤ) :
    geoRootQ N ^ m = Complex.exp (m * (2 * Real.pi * Complex.I / N)) := by
  rw [Complex.exp_int_mul, geoRootQ, geoHalfRoot, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- `a_n^{-8a} = q_N^{-2an(n+1)}`. -/
theorem geo_phase_pow_eq_homogeneous (a N n : ℕ) (hN : 1 ≤ N) :
    geoPhasePow N n (-(8 * a : ℝ)) = geoRootQ N ^ (-(2 * (a : ℤ) * n * (n + 1))) := by
  rw [geoRootQ_zpow_eq_exp, geoPhasePow, geoPhaseArg, Complex.exp_eq_exp_iff_exists_int]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  refine ⟨2 * a * n, ?_⟩
  push_cast
  field_simp
  ring

/-- (4.3): `A⁺_{a,2}` is periodic in `N` with period `4pq = 8a`. -/
theorem geo_zhengA_periodic (a : ℕ) (N : ℤ) (k : ℕ) :
    geoZhengA a (N + 8 * a) k = geoZhengA a N k := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [geoZhengA]
  unfold geoZhengA
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hexp : Complex.exp (-((N + 8 * a : ℤ) : ℂ) * (j : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a)) =
      Complex.exp (-(N : ℂ) * (j : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a)) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-(j : ℤ) ^ 2, ?_⟩
    push_cast
    field_simp
    ring
  rw [hexp]

/-- `A⁺_{a,2}(N, k)` depends only on `N mod 8a`. -/
private theorem geoZhengA_natCast_mod (a k : ℕ) (N : ℕ) :
    geoZhengA a (N : ℤ) k = geoZhengA a ((N % (8 * a) : ℕ) : ℤ) k := by
  have key : ∀ m M : ℕ, geoZhengA a ((M + 8 * a * m : ℕ) : ℤ) k = geoZhengA a (M : ℤ) k := by
    intro m
    induction m with
    | zero => intro M; simp
    | succ m ih =>
      intro M
      rw [show ((M + 8 * a * (m + 1) : ℕ) : ℤ) = ((M + 8 * a * m : ℕ) : ℤ) + 8 * a by
        push_cast; ring, geo_zhengA_periodic, ih]
  conv_lhs => rw [← Nat.mod_add_div N (8 * a)]
  exact key _ _

/-- `|C_{a,N}| = 2 (4a)^{-3/2} |A⁺_{a,2}(N, 1)| N^{5/2}`. -/
private theorem norm_geoZhengC (a N : ℕ) :
    ‖geoZhengC a N‖ =
      2 / (4 * (a : ℝ)) ^ (3 / 2 : ℝ) * ‖geoZhengA a N 1‖ * (N : ℝ) ^ (5 / 2 : ℝ) := by
  have harg : -((a : ℂ) / 2 + 2 / a) * Real.pi * Complex.I / (2 * N) +
      Real.pi * Complex.I / 4 =
      ((-((a : ℝ) / 2 + 2 / a) * Real.pi / (2 * N) + Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hpos : 0 ≤ (N : ℝ) ^ (5 / 2 : ℝ) / (4 * (a : ℝ)) ^ (3 / 2 : ℝ) := by positivity
  rw [geoZhengC, harg, norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_of_nonneg hpos]
  norm_num
  ring

/-- With Proposition 4.1, `|C_{a,N}| ≍ N^{5/2}`. -/
theorem geo_zhengC_bounds (a : ℕ) (ha : 1 ≤ a) (hP : ZhengProp41 a) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      c * (N : ℝ) ^ (5 / 2 : ℝ) ≤ ‖geoZhengC a N‖ ∧
        ‖geoZhengC a N‖ ≤ C * (N : ℝ) ^ (5 / 2 : ℝ) := by
  set f : ℕ → ℝ := fun m ↦ ‖geoZhengA a (m : ℤ) 1‖ with hf
  have hne : (Finset.range (8 * a)).Nonempty := ⟨0, by simp; omega⟩
  obtain ⟨m0, hm0, hmin⟩ := (Finset.range (8 * a)).exists_min_image f hne
  obtain ⟨m1, -, hmax⟩ := (Finset.range (8 * a)).exists_max_image f hne
  have hf0 : 0 < f m0 := norm_pos_iff.mpr (hP m0)
  have hK : 0 < 2 / (4 * (a : ℝ)) ^ (3 / 2 : ℝ) := by
    have : (0 : ℝ) < a := by exact_mod_cast ha
    positivity
  have hmem : ∀ N : ℕ, N % (8 * a) ∈ Finset.range (8 * a) := fun N ↦
    Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  refine ⟨2 / (4 * (a : ℝ)) ^ (3 / 2 : ℝ) * f m0, 2 / (4 * (a : ℝ)) ^ (3 / 2 : ℝ) * f m1,
    by positivity, mul_pos hK (hf0.trans_le (hmax m0 hm0)), fun N _ ↦ ?_⟩
  have hfN : ‖geoZhengA a N 1‖ = f (N % (8 * a)) := by
    rw [hf]
    dsimp only
    rw [geoZhengA_natCast_mod]
  rw [norm_geoZhengC, hfN]
  constructor
  · gcongr
    exact hmin _ (hmem N)
  · gcongr
    exact hmax _ (hmem N)

/-- `S₀ = S_{[N/2],[N/4]} > 0`. -/
theorem geo_normFactor0_pos (N : ℕ) (hN : 1 ≤ N) : 0 < geoNormFactor0 N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsin : ∀ m : ℕ, 1 ≤ m → m < N → 0 < Real.sin ((m : ℝ) * Real.pi / N) := by
    intro m hm1 hmN
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < m := by exact_mod_cast hm1
      positivity
    · rw [div_lt_iff₀ hNr]
      have : (m : ℝ) < N := by exact_mod_cast hmN
      nlinarith [Real.pi_pos]
  unfold geoNormFactor0 geoNormFactor
  refine Finset.prod_pos fun j hj ↦ ?_
  rw [Finset.mem_Icc] at hj
  have h1 := hsin (N / 4 + j) (by omega) (by omega)
  have h2 := hsin j hj.1 (by omega)
  push_cast at h1
  positivity

/-- `q_N^m = exp(2πi m/N)`. -/
private theorem geoRootQ_pow_eq_exp (N m : ℕ) :
    geoRootQ N ^ m = Complex.exp (((2 * Real.pi * m / N : ℝ) : ℂ) * Complex.I) := by
  rw [geoRootQ, geoHalfRoot, ← pow_mul, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `|e^{iθ} - e^{iφ}| ≤ |θ - φ|`. -/
private theorem norm_exp_mul_I_sub_exp_mul_I_le (θ φ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I)‖ ≤ |θ - φ| := by
  have h : Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I) =
      Complex.exp (φ * Complex.I) * (Complex.exp (Complex.I * ((θ - φ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- If `|m - cN| ≤ D` then `|q_N^m - e^{2πic}| ≤ 2πD/N`. -/
private theorem geoRootQ_pow_sub_le (N m : ℕ) (hN : 1 ≤ N) (c D : ℝ) (h : |(m : ℝ) - c * N| ≤ D) :
    ‖geoRootQ N ^ m - Complex.exp (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I)‖ ≤
      2 * Real.pi * D / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [geoRootQ_pow_eq_exp]
  refine (norm_exp_mul_I_sub_exp_mul_I_le _ _).trans ?_
  have : 2 * Real.pi * m / N - 2 * Real.pi * c = 2 * Real.pi / N * (m - c * N) := by
    field_simp
  rw [this, abs_mul, abs_of_pos (by positivity), div_mul_eq_mul_div, mul_div_assoc,
    mul_div_assoc]
  gcongr

/-- Perturbation bound for the dual ratios `(1 - u)/(1 - v)` near `u = i`, `v = -i`, and their
product with `w` near `-1`. -/
private theorem norm_dual_ratio_add_I_le (u v w : ℂ) (η : ℝ) (hu : ‖u - Complex.I‖ ≤ η)
    (hv : ‖v + Complex.I‖ ≤ η) (hw : ‖w + 1‖ ≤ η) (hη : η ≤ 1 / 2) :
    ‖(1 - u) / (1 - v) + Complex.I‖ ≤ 4 * η ∧
      ‖w * ((1 - u) / (1 - v)) - Complex.I‖ ≤ 7 * η := by
  have hre : 1 / 2 ≤ ‖1 - v‖ := by
    have h1 : |(v + Complex.I).re| ≤ ‖v + Complex.I‖ := Complex.abs_re_le_norm _
    have h2 : |(1 - v).re| ≤ ‖1 - v‖ := Complex.abs_re_le_norm _
    simp only [Complex.add_re, Complex.I_re, add_zero, Complex.sub_re, Complex.one_re] at h1 h2
    have h3 := le_abs_self (v.re)
    have h4 := le_abs_self (1 - v.re)
    linarith
  have hv0 : 1 - v ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hre; norm_num at hre
  have hpos : 0 < ‖1 - v‖ := norm_pos_iff.mpr hv0
  have heq : (1 - u) / (1 - v) + Complex.I = (-(u - Complex.I) - Complex.I * (v + Complex.I)) /
      (1 - v) := by
    rw [eq_div_iff hv0, add_mul, div_mul_cancel₀ _ hv0]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hnum : ‖-(u - Complex.I) - Complex.I * (v + Complex.I)‖ ≤ 2 * η := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
    linarith
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hu
  have hz : ‖(1 - u) / (1 - v) + Complex.I‖ ≤ 4 * η := by
    rw [heq, norm_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hη0 (sub_nonneg.mpr hre)]
  refine ⟨hz, ?_⟩
  have hzn : ‖(1 - u) / (1 - v)‖ ≤ 3 := by
    have := norm_sub_le ((1 - u) / (1 - v) + Complex.I) Complex.I
    rw [add_sub_cancel_right, Complex.norm_I] at this
    linarith
  have heq2 : w * ((1 - u) / (1 - v)) - Complex.I =
      (w + 1) * ((1 - u) / (1 - v)) - ((1 - u) / (1 - v) + Complex.I) := by ring
  rw [heq2]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  nlinarith [norm_nonneg (w + 1), norm_nonneg ((1 - u) / (1 - v))]

/-- The coefficient-extraction coordinates converge uniformly on the window. -/
theorem geo_phys_coordinates (δ : ℝ) (hδ0 : 1 / 2 < δ) (hδ : δ < 1) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N n i : ℕ, N₀ ≤ N → n + i < N → GeoInWindow N ((N : ℝ) ^ δ) n i →
      let q := geoRootQ N
      let zi := (1 - q ^ (i + 1)) / (1 - q ^ (n + i + 1))
      let zj := (1 - q ^ (N - n - i)) / (1 - q ^ (N - i))
      ‖q ^ n + 1‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧ ‖q ^ i - Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧
        ‖q ^ (N - 1 - n - i) - Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧
        ‖zi + Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧ ‖zj + Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧
        ‖q ^ n * zi - Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) ∧
        ‖q ^ n * zj - Complex.I‖ ≤ C * (N : ℝ) ^ (δ - 1) := by
  have hδ1 : 0 < 1 - δ := by linarith
  have hlim : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (δ - 1)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hδ1).comp tendsto_natCast_atTop_atTop
    simpa only [neg_sub, Function.comp_def] using this
  have h8 : (0 : ℝ) < 1 / (8 * Real.pi) := by positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds h8))
  refine ⟨28 * Real.pi, max N₀ 1, fun N n i hN hni hwin ↦ ?_⟩
  dsimp only
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hεsmall : (N : ℝ) ^ (δ - 1) < 1 / (8 * Real.pi) := hN₀ N (le_of_max_le_left hN)
  set ε := (N : ℝ) ^ (δ - 1) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hdiv : (N : ℝ) ^ δ / N = ε := by rw [hε, Real.rpow_sub_one hNr.ne']
  have hinv : 1 / (N : ℝ) ≤ ε := by
    rw [← hdiv]
    gcongr
    exact Real.one_le_rpow (by exact_mod_cast hN1) (by linarith)
  have hη : 4 * Real.pi * ε ≤ 1 / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hεsmall
    nlinarith
  have key : ∀ m : ℕ, ∀ c : ℝ, |(m : ℝ) - c * N| ≤ (N : ℝ) ^ δ + 1 →
      ‖geoRootQ N ^ m - Complex.exp (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I)‖ ≤
        4 * Real.pi * ε := by
    intro m c h
    refine (geoRootQ_pow_sub_le N m hN1 c _ h).trans ?_
    rw [show 2 * Real.pi * ((N : ℝ) ^ δ + 1) / N = 2 * Real.pi * ((N : ℝ) ^ δ / N + 1 / N) by
      ring, hdiv]
    nlinarith [Real.pi_pos]
  have em1 : Complex.exp (((2 * Real.pi * (1 / 2) : ℝ) : ℂ) * Complex.I) = -1 := by
    push_cast
    rw [show 2 * (Real.pi : ℂ) * (1 / 2) * Complex.I = Real.pi * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  have eI : Complex.exp (((2 * Real.pi * (1 / 4) : ℝ) : ℂ) * Complex.I) = Complex.I := by
    push_cast
    rw [show 2 * (Real.pi : ℂ) * (1 / 4) * Complex.I = Real.pi / 2 * Complex.I by ring]
    exact Complex.exp_pi_div_two_mul_I
  have emI : Complex.exp (((2 * Real.pi * (3 / 4) : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    push_cast
    rw [show 2 * (Real.pi : ℂ) * (3 / 4) * Complex.I =
      Real.pi * Complex.I + Real.pi / 2 * Complex.I by ring, Complex.exp_add,
      Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
    ring
  unfold GeoInWindow at hwin
  have A1 := le_abs_self ((n : ℝ) - N / 2)
  have A2 := neg_abs_le ((n : ℝ) - N / 2)
  have A3 := le_abs_self ((i : ℝ) - N / 4)
  have A4 := neg_abs_le ((i : ℝ) - N / 4)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, N = n + i + 1 + j := ⟨N - 1 - n - i, by omega⟩
  have hjr : (N : ℝ) = n + i + 1 + j := by exact_mod_cast hj
  rw [show N - 1 - n - i = j by omega, show N - n - i = j + 1 by omega,
    show N - i = n + j + 1 by omega]
  have h1 := key n (1 / 2) (abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [em1, sub_neg_eq_add] at h1
  have h2 := key i (1 / 4) (abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [eI] at h2
  have h3 := key j (1 / 4) (abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [eI] at h3
  have h4 := key (i + 1) (1 / 4) (abs_le.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩)
  rw [eI] at h4
  have h5 := key (n + i + 1) (3 / 4)
    (abs_le.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩)
  rw [emI, sub_neg_eq_add] at h5
  have h6 := key (j + 1) (1 / 4) (abs_le.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩)
  rw [eI] at h6
  have h7 := key (n + j + 1) (3 / 4)
    (abs_le.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩)
  rw [emI, sub_neg_eq_add] at h7
  obtain ⟨r1, r1'⟩ := norm_dual_ratio_add_I_le _ _ _ _ h4 h5 h1 hη
  obtain ⟨r2, r2'⟩ := norm_dual_ratio_add_I_le _ _ _ _ h6 h7 h1 hη
  have hp : 0 ≤ Real.pi * ε := by positivity
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-- The limit point solves the formal critical equations, lies over the node `(-1, -1)` and
carries the normalized action `4G`. -/
theorem geo_phys_endpoint (a : ℕ) :
    geoRatioQ a 1 1 (-1) (-Complex.I) = 1 ∧ geoRatioZ 1 1 (-1) (-Complex.I) = 1 ∧
      geoRatioX 1 1 (-1) (-Complex.I) = -1 ∧ geoChannelT 1 Complex.I = 0 ∧
      (∀ N : ℕ, 1 ≤ N → (-Complex.exp (Real.pi * Complex.I / (2 * N))) ^ (2 * N) = -1) ∧
      1 / Complex.I = -Complex.I ∧ (Complex.I - 1) / (Complex.I + 1) = Complex.I ∧
      -2 * geoRegPrimitive (-Complex.I) = 4 * catalanConstant := by
  have h1 : (1 : ℂ) - Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have h2 : (1 : ℂ) + Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have h3 : Complex.I + 1 ≠ 0 := by rw [add_comm]; exact h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hz : ((1 : ℂ) ^ 2 * (-1)) ^ (-(4 * (a : ℤ))) = 1 := by
      rw [one_pow, one_mul, zpow_neg, zpow_mul]; norm_num
    rw [geoRatioQ, hz]
    field_simp
    ring_nf
    simp [Complex.I_sq]
    ring
  · rw [geoRatioZ]
    field_simp
    ring_nf
    simp [Complex.I_sq]
    ring
  · rw [geoRatioX]
    field_simp
    ring_nf
    have hinv : (1 + Complex.I)⁻¹ = (1 - Complex.I) / 2 := by
      apply inv_eq_of_mul_eq_one_right
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hinv]
    ring_nf
    rw [Complex.I_sq]
    ring
  · simp [geoChannelT]
  · intro N hN
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [neg_pow, pow_mul, neg_one_sq, one_pow, one_mul, ← Complex.exp_nat_mul]
    have : ((2 * N : ℕ) : ℂ) * (Real.pi * Complex.I / (2 * N)) = Real.pi * Complex.I := by
      push_cast; field_simp
    rw [this, Complex.exp_pi_mul_I]
  · simp
  · field_simp
    ring_nf
    simp [Complex.I_sq]
    ring
  · rw [geo_regPrimitive_values.2.2.2.2]
    ring

end AJConjecture
