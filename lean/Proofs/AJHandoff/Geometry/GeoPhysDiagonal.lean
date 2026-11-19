import Mathlib
import AJHandoff.Geometry.GeoPhysUncond
import AJHandoff.Geometry.GeoPhysGaussian

/-!
# The physical diagonal, conditional on Zheng's estimates (G-PHYS, G-physical-v1)

For a fixed odd `a ≥ 3`, assuming the cited estimates `ZhengEstimates a` (Zheng, math/0508138v4,
Lemmas 3.2–3.3, (5.16), (5.19)–(5.20), Proposition 4.1):

1. the leading derivative of the companion input on the window has the homogeneous phase:
   `q∂_q Ĥ_n(q_N) = C_{a,N} v_n(q_N) + O(N²)` with `v_n = q^{-2an(n+1)}`, and
   `c_a N^{5/2} ≤ |C_{a,N}| ≤ C_a N^{5/2}` (a genuine nonzero amplitude; this is about the
   derivative, not the false `u_n = v_n`);
2. the leading term `ℒ_N = q_N^{-1/2} C_{a,N} C_β e^{-βNπi/8} S₀`, `β = -(8a + 1)`, is nonzero, the
   window `D_N` (`1/2 < δ < 2/3`) carries it — `J_N^{D_N}/ℒ_N → 1` — the complement is negligible,
   and `J_N(q_N)/ℒ_N → 1`.

Together with `geo_phys_coordinates` and `geo_phys_endpoint` (unconditional), the noncancelling
leading discrete contribution maps uniformly to `(x, Q, z, y) = (1, -1, -i, i)`, the normalized
branch `r = -i`, `w = i` over the node `M = L = -1`, where the normalized action is `4G`. Only the
fixed `a`, the root `q_N` and `x = 1` are involved: no variable-`x` or all-torus statement.

Route (source (5)–(7)). On `D_N ⊆ {|n - N/2| + |i - N/4| < N/(8a)}` (large `N`), write the bracket
as
`C_{a,N} a_n^{-8a} + O(N²)` by (5.19)–(5.20); the main part is
`C_{a,N} ∑_{D_N} a_n^β S_{n,i} = C_{a,N} C_β N e^{-βNπi/8} S₀ (1 + O(N^{3δ-2}))` (Lemma 3.3), and
the error is `O(N²) ∑_{D_N} S_{n,i} = O(N³ S₀)` (Lemma 3.3 at `β = 0`); relative size `O(N^{-1/2})`
by item 1. Outside `D_N` there are `O(N²)` terms, each `O(N⁴) e^{-εN^{2δ-1}} S₀` by (5.16) and
Lemma 3.2. Nonvanishing: `geo_gaussConst_eq`, `geo_normFactor0_pos`, `geo_zhengC_bounds`.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- Phases multiply: `a_n^{β₁} a_n^{β₂} = a_n^{β₁ + β₂}`. -/
private theorem geoPhasePow_mul (N n : ℕ) (β₁ β₂ : ℝ) :
    geoPhasePow N n β₁ * geoPhasePow N n β₂ = geoPhasePow N n (β₁ + β₂) := by
  rw [geoPhasePow, geoPhasePow, geoPhasePow, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `|a_n^β| = 1`. -/
private theorem norm_geoPhasePow (N n : ℕ) (β : ℝ) : ‖geoPhasePow N n β‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- `S_{n,i} ≥ 0` for `n < N`. -/
private theorem geoNormFactor_nonneg (N n i : ℕ) (hn : n < N) : 0 ≤ geoNormFactor N n i := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine Finset.prod_nonneg fun j hj ↦ ?_
  rw [Finset.mem_Icc] at hj
  have hs : 0 < Real.sin ((j : ℝ) * Real.pi / N) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < j := by exact_mod_cast hj.1
      positivity
    · rw [div_lt_iff₀ hNr]
      have : (j : ℝ) < N := by exact_mod_cast (show j < N by omega)
      nlinarith [Real.pi_pos]
  positivity

/-- `N^{-γ} → 0` along the naturals. -/
private theorem tendsto_natCast_rpow_neg {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-γ)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop

/-- `N^{5/2} e^{-ε N^γ} → 0` along the naturals. -/
private theorem tendsto_natCast_rpow_mul_exp_neg {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-ε * (N : ℝ) ^ γ)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / (2 * γ)) ε hε).comp
    ((tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop)
  refine h.congr fun N ↦ ?_
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 2
  field_simp

/-- For large `N`, the window of radius `N^δ` lies in the window of radius `N/(8a)`. -/
private theorem eventually_rpow_le_div {a : ℕ} (ha : 1 ≤ a) {δ : ℝ} (hδ : δ < 1) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ δ ≤ N / (8 * a) := by
  have h := ((tendsto_rpow_atTop (show 0 < 1 - δ by linarith)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (8 * (a : ℝ))
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
  simp only [Function.comp_apply] at hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have ha' : (0 : ℝ) < 8 * a := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  rw [le_div_iff₀ ha']
  have : (N : ℝ) = N ^ δ * N ^ (1 - δ) := by
    rw [← Real.rpow_add hNr]; simp
  calc (N : ℝ) ^ δ * (8 * a) ≤ N ^ δ * N ^ (1 - δ) := by gcongr
    _ = N := this.symm

open Classical in
/-- The `β = 0` window sum is the real sum `∑_{D_N} S_{n,i}`. -/
private theorem geoWindowSum_zero (N : ℕ) (δ : ℝ) :
    geoWindowSum N δ 0 =
      ((∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        if GeoInWindow N ((N : ℝ) ^ δ) n i then geoNormFactor N n i else 0 : ℝ) : ℂ) := by
  have h1 : ∀ n : ℕ, geoPhasePow N n 0 = 1 := fun n ↦ by simp [geoPhasePow]
  simp only [geoWindowSum, h1, one_mul, Complex.ofReal_sum, apply_ite (Complex.ofReal),
    Complex.ofReal_zero]

open Classical in
/-- The window sum of Lemma 3.3 at `β = 0` is nonnegative. -/
private theorem windowSum_normFactor_nonneg (N : ℕ) (δ : ℝ) :
    0 ≤ ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
      if GeoInWindow N ((N : ℝ) ^ δ) n i then geoNormFactor N n i else 0 := by
  refine Finset.sum_nonneg fun n hn ↦ Finset.sum_nonneg fun i _ ↦ ?_
  split_ifs
  · exact geoNormFactor_nonneg N n i (Finset.mem_range.mp hn)
  · exact le_rfl

open Classical in
/-- On the window, replacing the bracket by `C_{a,N} a_n^{-8a}` costs at most
`K N² ∑_{D_N} S_{n,i}`. -/
private theorem norm_windowDiagonal_sub_le (a N : ℕ) (δ K : ℝ)
    (hB : ∀ n i : ℕ, n + i < N → GeoInWindow N ((N : ℝ) ^ δ) n i →
      ‖geoZhengB N n i * geoHatInput a n (geoHalfRoot N) + geoHatInputDeriv a n N -
        geoZhengC a N * geoPhasePow N n (-(8 * a : ℝ))‖ ≤ K * (N : ℝ) ^ 2) :
    ‖(∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        if GeoInWindow N ((N : ℝ) ^ δ) n i then
          geoPhasePow N n (-1) * geoNormFactor N n i *
            (geoZhengB N n i * geoHatInput a n (geoHalfRoot N) + geoHatInputDeriv a n N)
        else 0) - geoZhengC a N * geoWindowSum N δ (-(8 * a + 1 : ℝ))‖ ≤
      K * (N : ℝ) ^ 2 * ‖geoWindowSum N δ 0‖ := by
  have hph : ∀ n : ℕ, geoPhasePow N n (-(8 * a + 1 : ℝ)) =
      geoPhasePow N n (-1) * geoPhasePow N n (-(8 * a : ℝ)) := fun n ↦ by
    rw [geoPhasePow_mul]; congr 1; ring
  rw [geoWindowSum_zero, Complex.norm_real, Real.norm_of_nonneg (windowSum_normFactor_nonneg N δ)]
  calc _ = ‖∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        if GeoInWindow N ((N : ℝ) ^ δ) n i then
          geoPhasePow N n (-1) * geoNormFactor N n i *
            (geoZhengB N n i * geoHatInput a n (geoHalfRoot N) + geoHatInputDeriv a n N -
              geoZhengC a N * geoPhasePow N n (-(8 * a : ℝ)))
        else 0‖ := by
        congr 1
        rw [geoWindowSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        split_ifs
        · rw [hph]; ring
        · simp
    _ ≤ ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        ‖if GeoInWindow N ((N : ℝ) ^ δ) n i then
          geoPhasePow N n (-1) * geoNormFactor N n i *
            (geoZhengB N n i * geoHatInput a n (geoHalfRoot N) + geoHatInputDeriv a n N -
              geoZhengC a N * geoPhasePow N n (-(8 * a : ℝ)))
        else 0‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ norm_sum_le _ _)
    _ ≤ ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        if GeoInWindow N ((N : ℝ) ^ δ) n i then K * (N : ℝ) ^ 2 * geoNormFactor N n i else 0 := by
        refine Finset.sum_le_sum fun n hn ↦ Finset.sum_le_sum fun i hi ↦ ?_
        have hn' := Finset.mem_range.mp hn
        have hi' := Finset.mem_range.mp hi
        have hS := geoNormFactor_nonneg N n i hn'
        split_ifs with hw
        · rw [norm_mul, norm_mul, norm_geoPhasePow, Complex.norm_real, Real.norm_of_nonneg hS,
            one_mul, mul_comm (K * _)]
          exact mul_le_mul_of_nonneg_left (hB n i (by omega) hw) hS
        · simp
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        split_ifs <;> simp

/-- The leading term `ℒ_N = q_N^{-1/2} C_{a,N} C_β e^{-βNπi/8} S₀`, `β = -(8a + 1)`. -/
def geoZhengLeading (a N : ℕ) : ℂ :=
  (geoHalfRoot N)⁻¹ * geoZhengC a N * geoGaussConst (-(8 * a + 1 : ℝ)) *
    Complex.exp ((8 * a + 1 : ℂ) * N * Real.pi * Complex.I / 8) * geoNormFactor0 N

open Classical in
/-- On the window `D_N`, `J_N^{D_N}/ℒ_N = 1 + O(N^{3δ-2}) + O(N^{-1/2})`. -/
private theorem window_ratio_bound (a : ℕ) (ha : 3 ≤ a) (hZ : ZhengEstimates a) (δ : ℝ)
    (hδ0 : 1 / 2 < δ) (hδ : δ < 2 / 3) :
    ∃ A B : ℝ, ∀ᶠ N : ℕ in atTop,
      ‖geoZhengDiagonalIn a N δ / geoZhengLeading a N - 1‖ ≤
        A * (N : ℝ) ^ (3 * δ - 2) + B * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨-, hL33, -, ⟨K19, h19⟩, ⟨K20, h20⟩, hP⟩ := hZ
  obtain ⟨⟨Kβ, hKβ⟩, ⟨K0, hK0⟩⟩ := hL33 δ hδ0 hδ
  obtain ⟨c, Cc, hc, -, hCb⟩ := geo_zhengC_bounds a (by omega) hP
  set G := geoGaussConst (-(8 * a + 1 : ℝ)) with hGdef
  set G0 := geoGaussConst 0 with hG0def
  have hGpos : 0 < ‖G‖ := norm_pos_iff.mpr (geo_gaussConst_eq _).2
  set K' := (|K19| + |K20|) * (‖G0‖ + |K0|) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  refine ⟨|Kβ| / ‖G‖, K' / (c * ‖G‖), ?_⟩
  filter_upwards [eventually_rpow_le_div (a := a) (by omega) (by linarith : δ < 1),
    eventually_ge_atTop 1] with N hsub hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hS0 : 0 < geoNormFactor0 N := geo_normFactor0_pos N hN1
  set S₀ := geoNormFactor0 N with hS₀
  set C := geoZhengC a N with hCdef
  have hCN : c * (N : ℝ) ^ (5 / 2 : ℝ) ≤ ‖C‖ := (hCb N hN1).1
  have hCpos : 0 < ‖C‖ := lt_of_lt_of_le (by positivity) hCN
  have hC0 : C ≠ 0 := norm_pos_iff.mp hCpos
  have hG0' : G ≠ 0 := norm_pos_iff.mp hGpos
  have hs : geoHalfRoot N ≠ 0 := Complex.exp_ne_zero _
  set E := Complex.exp ((8 * a + 1 : ℂ) * N * Real.pi * Complex.I / 8) with hEdef
  have hE : ‖E‖ = 1 := by
    rw [hEdef, show (8 * a + 1 : ℂ) * N * Real.pi * Complex.I / 8 =
      (((8 * a + 1) * N * Real.pi / 8 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNr.ne'
  have hS00 : (S₀ : ℂ) ≠ 0 := by exact_mod_cast hS0.ne'
  set X := ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
    if GeoInWindow N ((N : ℝ) ^ δ) n i then
      geoPhasePow N n (-1) * geoNormFactor N n i *
        (geoZhengB N n i * geoHatInput a n (geoHalfRoot N) + geoHatInputDeriv a n N)
    else 0 with hXdef
  have key : geoZhengDiagonalIn a N δ / geoZhengLeading a N - 1 =
      (X - N * C * G * E * S₀) / (N * C * G * E * S₀) := by
    rw [show geoZhengDiagonalIn a N δ = (geoHalfRoot N)⁻¹ / N * X from rfl,
      show geoZhengLeading a N = (geoHalfRoot N)⁻¹ * C * G * E * S₀ from rfl]
    field_simp
  have hden : ‖(N : ℂ) * C * G * E * (S₀ : ℂ)‖ = N * ‖C‖ * ‖G‖ * S₀ := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hE, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg hS0.le, mul_one]
  have hβ : ‖geoWindowSum N δ (-(8 * a + 1 : ℝ)) - G * N * E * S₀‖ ≤
      Kβ * (N : ℝ) ^ (3 * δ - 2) * (N * S₀) := by
    have h := hKβ N hN1
    rwa [show Complex.exp (-(((-(8 * a + 1 : ℝ)) : ℝ) : ℂ) * N * Real.pi * Complex.I / 8) = E by
      rw [hEdef]; congr 1; push_cast; ring] at h
  have hle1 : (N : ℝ) ^ (3 * δ - 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith)
  have h0 : ‖geoWindowSum N δ 0‖ ≤ (‖G0‖ + |K0|) * (N * S₀) := by
    have h := hK0 N hN1
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, zero_div, Complex.exp_zero,
      mul_one] at h
    have h' := norm_sub_norm_le (geoWindowSum N δ 0) (G0 * N * S₀)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg hS0.le] at h'
    have hNS : 0 ≤ (N : ℝ) * S₀ := by positivity
    have : K0 * (N : ℝ) ^ (3 * δ - 2) * (N * S₀) ≤ |K0| * (N * S₀) := by
      gcongr
      calc K0 * (N : ℝ) ^ (3 * δ - 2) ≤ |K0| * (N : ℝ) ^ (3 * δ - 2) := by
            gcongr; exact le_abs_self K0
        _ ≤ |K0| * 1 := by gcongr
        _ = |K0| := mul_one _
    nlinarith
  have hwin := norm_windowDiagonal_sub_le a N δ (|K19| + |K20|) fun n i hni hw ↦ by
    have hw' : GeoInWindow N (N / (8 * a)) n i := lt_of_lt_of_le hw hsub
    rw [add_sub_assoc]
    refine (norm_add_le _ _).trans ?_
    have := h19 N n i hN1 hni hw'
    have := h20 N n i hN1 hni hw'
    have : K19 ≤ |K19| := le_abs_self _
    have : K20 ≤ |K20| := le_abs_self _
    nlinarith [sq_nonneg (N : ℝ)]
  have hnum : ‖X - N * C * G * E * S₀‖ ≤
      ‖C‖ * (|Kβ| * (N : ℝ) ^ (3 * δ - 2) * (N * S₀)) + K' * (N : ℝ) ^ 2 * (N * S₀) := by
    rw [show X - N * C * G * E * S₀ = C * (geoWindowSum N δ (-(8 * a + 1 : ℝ)) - G * N * E * S₀) +
      (X - C * geoWindowSum N δ (-(8 * a + 1 : ℝ))) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have hKβ' : Kβ * (N : ℝ) ^ (3 * δ - 2) * (N * S₀) ≤
        |Kβ| * (N : ℝ) ^ (3 * δ - 2) * (N * S₀) := by
      gcongr; exact le_abs_self _
    have h2 : (|K19| + |K20|) * (N : ℝ) ^ 2 * ‖geoWindowSum N δ 0‖ ≤
        K' * (N : ℝ) ^ 2 * (N * S₀) := by
      rw [hK']
      calc (|K19| + |K20|) * (N : ℝ) ^ 2 * ‖geoWindowSum N δ 0‖ ≤
          (|K19| + |K20|) * (N : ℝ) ^ 2 * ((‖G0‖ + |K0|) * (N * S₀)) := by gcongr
        _ = _ := by ring
    have := mul_le_mul_of_nonneg_left (hβ.trans hKβ') (norm_nonneg C)
    linarith
  have hrp : (N : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (5 / 2 : ℝ) = (N : ℝ) ^ 2 := by
    rw [← Real.rpow_add hNr]
    norm_num
  rw [key, norm_div, hden, div_le_iff₀ (by positivity)]
  refine hnum.trans ?_
  have hB0 : 0 ≤ K' / c * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  calc ‖C‖ * (|Kβ| * (N : ℝ) ^ (3 * δ - 2) * (N * S₀)) + K' * (N : ℝ) ^ 2 * (N * S₀)
      = ‖C‖ * (|Kβ| * (N : ℝ) ^ (3 * δ - 2) * (N * S₀)) +
          K' / c * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (c * (N : ℝ) ^ (5 / 2 : ℝ)) * (N * S₀) := by
        rw [show K' / c * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (c * (N : ℝ) ^ (5 / 2 : ℝ)) =
          K' * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (5 / 2 : ℝ)) by field_simp, hrp]
    _ ≤ ‖C‖ * (|Kβ| * (N : ℝ) ^ (3 * δ - 2) * (N * S₀)) +
          K' / c * (N : ℝ) ^ (-(1 / 2 : ℝ)) * ‖C‖ * (N * S₀) := by gcongr
    _ = _ := by field_simp

open Classical in
/-- Off the window, `(J_N - J_N^{D_N})/ℒ_N = O(N^{5/2} e^{-εN^{2δ-1}})`. -/
private theorem complement_ratio_bound (a : ℕ) (ha : 3 ≤ a) (hZ : ZhengEstimates a) (δ : ℝ)
    (hδ0 : 1 / 2 < δ) (hδ : δ < 2 / 3) :
    ∃ A ε : ℝ, 0 < ε ∧ ∀ᶠ N : ℕ in atTop,
      ‖(geoZhengDiagonal a N - geoZhengDiagonalIn a N δ) / geoZhengLeading a N‖ ≤
        A * ((N : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-ε * (N : ℝ) ^ (2 * δ - 1))) := by
  obtain ⟨hL32, -, ⟨K16, h16⟩, -, -, hP⟩ := hZ
  obtain ⟨ε, hε, Cl, hCl, h32⟩ := hL32 δ hδ0 (by linarith)
  obtain ⟨c, Cc, hc, -, hCb⟩ := geo_zhengC_bounds a (by omega) hP
  set G := geoGaussConst (-(8 * a + 1 : ℝ)) with hGdef
  have hGpos : 0 < ‖G‖ := norm_pos_iff.mpr (geo_gaussConst_eq _).2
  refine ⟨|K16| * Cl / (c * ‖G‖), ε, hε, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hS0 : 0 < geoNormFactor0 N := geo_normFactor0_pos N hN1
  set S₀ := geoNormFactor0 N with hS₀
  set C := geoZhengC a N with hCdef
  have hCN : c * (N : ℝ) ^ (5 / 2 : ℝ) ≤ ‖C‖ := (hCb N hN1).1
  have hCpos : 0 < ‖C‖ := lt_of_lt_of_le (by positivity) hCN
  have hC0 : C ≠ 0 := norm_pos_iff.mp hCpos
  have hG0' : G ≠ 0 := norm_pos_iff.mp hGpos
  have hs : geoHalfRoot N ≠ 0 := Complex.exp_ne_zero _
  set E := Complex.exp ((8 * a + 1 : ℂ) * N * Real.pi * Complex.I / 8) with hEdef
  have hE : ‖E‖ = 1 := by
    rw [hEdef, show (8 * a + 1 : ℂ) * N * Real.pi * Complex.I / 8 =
      (((8 * a + 1) * N * Real.pi / 8 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNr.ne'
  have hS00 : (S₀ : ℂ) ≠ 0 := by exact_mod_cast hS0.ne'
  set Y := ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
    if GeoInWindow N ((N : ℝ) ^ δ) n i then 0 else
      geoPhasePow N n (-1) * geoNormFactor N n i *
        (geoZhengB N n i * geoHatInput a n (geoHalfRoot N) + geoHatInputDeriv a n N) with hYdef
  have hdiff : geoZhengDiagonal a N - geoZhengDiagonalIn a N δ = (geoHalfRoot N)⁻¹ / N * Y := by
    rw [geoZhengDiagonal, geoZhengDiagonalIn, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp
  have key : (geoZhengDiagonal a N - geoZhengDiagonalIn a N δ) / geoZhengLeading a N =
      Y / (N * C * G * E * S₀) := by
    rw [hdiff, show geoZhengLeading a N = (geoHalfRoot N)⁻¹ * C * G * E * S₀ from rfl]
    field_simp
  have hden : ‖(N : ℂ) * C * G * E * (S₀ : ℂ)‖ = N * ‖C‖ * ‖G‖ * S₀ := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hE, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg hS0.le, mul_one]
  set e := Real.exp (-ε * (N : ℝ) ^ (2 * δ - 1)) with he
  have he0 : 0 < e := Real.exp_pos _
  set M := |K16| * (N : ℝ) ^ 4 * (Cl * e * S₀) with hM
  have hM0 : 0 ≤ M := by positivity
  have hterm : ∀ n ∈ Finset.range N, ∀ i ∈ Finset.range (N - n),
      ‖if GeoInWindow N ((N : ℝ) ^ δ) n i then 0 else
        geoPhasePow N n (-1) * geoNormFactor N n i *
          (geoZhengB N n i * geoHatInput a n (geoHalfRoot N) + geoHatInputDeriv a n N)‖ ≤ M := by
    intro n hn i hi
    have hn' := Finset.mem_range.mp hn
    have hi' := Finset.mem_range.mp hi
    have hS := geoNormFactor_nonneg N n i hn'
    split_ifs with hw
    · rw [norm_zero]; exact hM0
    · rw [norm_mul, norm_mul, norm_geoPhasePow, Complex.norm_real, Real.norm_of_nonneg hS,
        one_mul]
      have hb := h16 N n i hN1 (by omega)
      have hb' : K16 * (N : ℝ) ^ 4 ≤ |K16| * (N : ℝ) ^ 4 := by gcongr; exact le_abs_self _
      have hs32 := (h32 N n i hN1 (by omega) (not_lt.mp hw)).le
      calc geoNormFactor N n i * ‖geoZhengB N n i * geoHatInput a n (geoHalfRoot N) +
            geoHatInputDeriv a n N‖ ≤ geoNormFactor N n i * (|K16| * (N : ℝ) ^ 4) :=
            mul_le_mul_of_nonneg_left (hb.trans hb') hS
        _ ≤ (Cl * e * S₀) * (|K16| * (N : ℝ) ^ 4) := by gcongr
        _ = M := by ring
  have hY : ‖Y‖ ≤ N * (N * M) := by
    calc ‖Y‖ ≤ ∑ n ∈ Finset.range N, (N * M) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn ↦ ?_)
          refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (hterm n hn)).trans ?_)
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          gcongr
          exact_mod_cast Nat.sub_le N n
      _ = N * (N * M) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hrp : (N : ℝ) ^ (5 / 2 : ℝ) * (N : ℝ) ^ (5 / 2 : ℝ) = (N : ℝ) ^ 5 := by
    rw [← Real.rpow_add hNr]
    norm_num
  rw [key, norm_div, hden, div_le_iff₀ (by positivity)]
  refine hY.trans ?_
  calc (N : ℝ) * (N * M) = |K16| * Cl / c * ((N : ℝ) ^ (5 / 2 : ℝ) * e) *
        (c * (N : ℝ) ^ (5 / 2 : ℝ)) * (N * S₀) := by
        rw [hM]
        field_simp
        rw [sq, hrp]
        ring
    _ ≤ |K16| * Cl / c * ((N : ℝ) ^ (5 / 2 : ℝ) * e) * ‖C‖ * (N * S₀) := by gcongr
    _ = _ := by field_simp

set_option linter.unusedVariables false in
/-- G-physical-v1, conditional on the cited estimates. -/
theorem geo_phys_diagonal (a : ℕ) (ha : 3 ≤ a) (hodd : Odd a) (hZ : ZhengEstimates a) :
    (∃ K : ℝ, ∀ N n i : ℕ, 1 ≤ N → n + i < N → GeoInWindow N (N / (8 * a)) n i →
        ‖geoHatInputDeriv a n N -
            geoZhengC a N * geoRootQ N ^ (-(2 * (a : ℤ) * n * (n + 1)))‖ ≤ K * (N : ℝ) ^ 2) ∧
      (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        c * (N : ℝ) ^ (5 / 2 : ℝ) ≤ ‖geoZhengC a N‖ ∧
          ‖geoZhengC a N‖ ≤ C * (N : ℝ) ^ (5 / 2 : ℝ)) ∧
      (∀ N : ℕ, 1 ≤ N → geoZhengLeading a N ≠ 0) ∧
      (∀ δ : ℝ, 1 / 2 < δ → δ < 2 / 3 →
        Tendsto (fun N : ℕ ↦ geoZhengDiagonalIn a N δ / geoZhengLeading a N) atTop (𝓝 1) ∧
          Tendsto (fun N : ℕ ↦ (geoZhengDiagonal a N - geoZhengDiagonalIn a N δ) /
            geoZhengLeading a N) atTop (𝓝 0)) ∧
      Tendsto (fun N : ℕ ↦ geoZhengDiagonal a N / geoZhengLeading a N) atTop (𝓝 1) := by
  have hCb := geo_zhengC_bounds a (by omega) hZ.2.2.2.2.2
  have hwin : ∀ δ : ℝ, 1 / 2 < δ → δ < 2 / 3 →
      Tendsto (fun N : ℕ ↦ geoZhengDiagonalIn a N δ / geoZhengLeading a N) atTop (𝓝 1) ∧
        Tendsto (fun N : ℕ ↦ (geoZhengDiagonal a N - geoZhengDiagonalIn a N δ) /
          geoZhengLeading a N) atTop (𝓝 0) := by
    intro δ hδ0 hδ
    constructor
    · obtain ⟨A, B, hb⟩ := window_ratio_bound a ha hZ δ hδ0 hδ
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (3 * δ - 2)) atTop (𝓝 0) := by
        simpa only [neg_sub] using tendsto_natCast_rpow_neg (show 0 < 2 - 3 * δ by linarith)
      have h2 := tendsto_natCast_rpow_neg (show (0 : ℝ) < 1 / 2 by norm_num)
      have h3 := (h1.const_mul A).add (h2.const_mul B)
      rw [mul_zero, mul_zero, add_zero] at h3
      exact squeeze_zero' (Eventually.of_forall fun N ↦ norm_nonneg _) hb h3
    · obtain ⟨A, ε, hε, hb⟩ := complement_ratio_bound a ha hZ δ hδ0 hδ
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h3 := (tendsto_natCast_rpow_mul_exp_neg (show 0 < 2 * δ - 1 by linarith) hε).const_mul A
      rw [mul_zero] at h3
      exact squeeze_zero' (Eventually.of_forall fun N ↦ norm_nonneg _) hb h3
  refine ⟨?_, hCb, ?_, hwin, ?_⟩
  · obtain ⟨K, hK⟩ := hZ.2.2.2.2.1
    exact ⟨K, fun N n i hN hni hw ↦ by
      rw [← geo_phase_pow_eq_homogeneous a N n hN]; exact hK N n i hN hni hw⟩
  · intro N hN
    obtain ⟨c, C, hc, -, hb⟩ := hCb
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hC : geoZhengC a N ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hb N hN).1)
    have hS : (geoNormFactor0 N : ℂ) ≠ 0 := by exact_mod_cast (geo_normFactor0_pos N hN).ne'
    unfold geoZhengLeading
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (inv_ne_zero (Complex.exp_ne_zero _)) hC) (geo_gaussConst_eq _).2)
        (Complex.exp_ne_zero _)) hS
  · obtain ⟨h1, h2⟩ := hwin (7 / 12) (by norm_num) (by norm_num)
    have h := h1.add h2
    rw [add_zero] at h
    refine h.congr fun N ↦ ?_
    rw [← add_div, add_sub_cancel]

end AJConjecture
