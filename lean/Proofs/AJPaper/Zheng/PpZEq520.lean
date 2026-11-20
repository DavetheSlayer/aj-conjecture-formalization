import Mathlib
import AJPaper.Zheng.PpZEq520Main

/-!
# Zheng's (5.20) (Unit PpZ, node `PpZ_Eq520`)

Source: H. Zheng, arXiv:math/0508138v4, (5.20):
`t d/dt Ĵ_{T(p,q),2n+1} = -2 a_n^{-4pq} N^{5/2}/(2pq)^{3/2} e^{-(p/q+q/p)πi/(2N) + πi/4}
A⁺_{p,q}(N,1) + O(N²)` uniformly on `|n - N/2| + |i - N/4| < N/(4pq)`; here `(p, q) = (a, 2)`.

Route. Let `K₁` be the constant of `ppZ_hatInputDeriv_main`.
* `N ≥ 16a`: the window `GeoInWindow N (N/(8a)) n i` gives `|n - N/2| < N/(8a)`, hence
  `|2n + 1 - N| ≤ 2|n - N/2| + 1 < N/(4a) + 1`; `n < N` from `n + i < N`.
  (So Zheng's Lemma W step for `q∂_q Ĥ` is not needed: the colour window of
  `ppZ_hatInputDeriv_main` already contains the boundary layer.)
* `1 ≤ N < 16a`: `‖q∂_q Ĥ_n‖ ≤ 24(a+1)N³ ≤ 24(a+1)·16a·N²` (`geoZh_norm_hatInputDeriv_le`) and
  `‖C_{a,N} a_n^{-8a}‖ = ‖C_{a,N}‖ ≤ 2 N^{5/2}/(4a)^{3/2} · ‖A⁺_{a,2}(N,1)‖`,
  `‖A⁺_{a,2}(N,1)‖ ≤ ∑_{j<2a} j² ≤ 8a³`, `N^{5/2} ≤ N² √(16a)`; the phase has modulus `1`.
-/

noncomputable section

namespace AJConjecture

/-- `‖A⁺_{a,2}(N, 1)‖ ≤ 8a³`. -/
private theorem norm_zhengA_one_le_ppZEq520 (a : ℕ) (N : ℤ) :
    ‖geoZhengA a N 1‖ ≤ 8 * (a : ℝ) ^ 3 := by
  have hterm : ∀ j ∈ Finset.Icc 1 (2 * a - 1),
      ‖Complex.exp (-(N : ℂ) * (j : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a)) *
        (j : ℂ) ^ (2 * 1) * Real.sin (j * Real.pi / a) * Real.sin (j * Real.pi / 2)‖ ≤
      (2 * (a : ℝ)) ^ 2 := fun j hj ↦ by
    have hj2 : (j : ℝ) ≤ 2 * a := by
      exact_mod_cast (by have := (Finset.mem_Icc.mp hj).2; omega : j ≤ 2 * a)
    have harg : (-(N : ℂ) * (j : ℂ) ^ 2 * Real.pi * Complex.I / (4 * a) : ℂ) =
        ((-(N : ℝ) * (j : ℝ) ^ 2 * Real.pi / (4 * a) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [norm_mul, norm_mul, norm_mul, harg, Complex.norm_exp_ofReal_mul_I, norm_pow,
      Complex.norm_natCast, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, one_mul, mul_one]
    have h1 := Real.abs_sin_le_one (j * Real.pi / a)
    have h2 := Real.abs_sin_le_one (j * Real.pi / 2)
    have h3 : (j : ℝ) ^ 2 ≤ (2 * (a : ℝ)) ^ 2 := by gcongr
    calc (j : ℝ) ^ 2 * |Real.sin (j * Real.pi / a)| * |Real.sin (j * Real.pi / 2)|
        ≤ (j : ℝ) ^ 2 * 1 * 1 := by gcongr
      _ ≤ (2 * (a : ℝ)) ^ 2 := by linarith
  have hcard : ((Finset.Icc 1 (2 * a - 1)).card : ℝ) ≤ 2 * a := by
    rw [Nat.card_Icc]
    exact_mod_cast (by omega : 2 * a - 1 + 1 - 1 ≤ 2 * a)
  rw [geoZhengA]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_)
  rw [nsmul_eq_mul]
  nlinarith [sq_nonneg (2 * (a : ℝ))]

/-- `‖C_{a,N}‖ ≤ 16 a³ N³`. -/
private theorem norm_zhengC_le_ppZEq520 (a N : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) :
    ‖geoZhengC a N‖ ≤ 2 * (N : ℝ) ^ 3 * (8 * (a : ℝ) ^ 3) := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have harg : -((a : ℂ) / 2 + 2 / a) * Real.pi * Complex.I / (2 * N) +
      Real.pi * Complex.I / 4 =
      ((-((a : ℝ) / 2 + 2 / a) * Real.pi / (2 * N) + Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hden : (1 : ℝ) ≤ (4 * (a : ℝ)) ^ (3 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hnum : (N : ℝ) ^ (5 / 2 : ℝ) ≤ (N : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast (N : ℝ) 3]
    exact Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
  have hpos : 0 ≤ (N : ℝ) ^ (5 / 2 : ℝ) / (4 * (a : ℝ)) ^ (3 / 2 : ℝ) := by positivity
  have hR : (N : ℝ) ^ (5 / 2 : ℝ) / (4 * (a : ℝ)) ^ (3 / 2 : ℝ) ≤ (N : ℝ) ^ 3 :=
    (div_le_self (by positivity) hden).trans hnum
  have hA := norm_zhengA_one_le_ppZEq520 a N
  rw [geoZhengC, harg, norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_of_nonneg hpos, norm_neg, Complex.norm_ofNat, mul_one]
  gcongr

/-- **Zheng (5.20)** for the companion `T(a, 2)`, `a` odd. -/
theorem zhengEq520_holds (a : ℕ) (hodd : Odd a) : ZhengEq520 a := by
  have ha : 1 ≤ a := hodd.pos
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  obtain ⟨K₁, hK₁⟩ := ppZ_hatInputDeriv_main a hodd
  refine ⟨|K₁| + (24 * (a + 1) * (16 * a) + 2 * (16 * a) * (8 * (a : ℝ) ^ 3)),
    fun N n i hN hni hwin ↦ ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : (0 : ℝ) ≤ 24 * (a + 1) * (16 * a) + 2 * (16 * a) * (8 * (a : ℝ) ^ 3) := by
    positivity
  by_cases hbig : 16 * a ≤ N
  · have hw : |(2 * (n : ℝ) + 1) - N| < N / (4 * a) + 1 := by
      rw [GeoInWindow] at hwin
      have h1 : |(n : ℝ) - N / 2| < N / (8 * a) := by
        linarith [abs_nonneg ((i : ℝ) - N / 4)]
      have h2 : (N : ℝ) / (4 * a) = 2 * (N / (8 * a)) := by
        field_simp
        ring
      rw [abs_lt] at h1 ⊢
      constructor <;> linarith [h1.1, h1.2]
    refine (hK₁ N n hbig (by omega) hw).trans ?_
    have := le_abs_self K₁
    have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hc hN2]
  · have hNlt : (N : ℝ) ≤ 16 * a := by exact_mod_cast (by omega : N ≤ 16 * a)
    have hD := geoZh_norm_hatInputDeriv_le a n N (by omega)
    have hC := norm_zhengC_le_ppZEq520 a N ha hN
    have hph : ‖geoPhasePow N n (-(8 * a : ℝ))‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hN3 : (N : ℝ) ^ 3 ≤ 16 * a * (N : ℝ) ^ 2 := by
      have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hNlt hN2]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, hph, mul_one]
    have hK0 := abs_nonneg K₁
    have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
    have e1 : 24 * ((a : ℝ) + 1) * (N : ℝ) ^ 3 ≤ 24 * (a + 1) * (16 * a) * (N : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hN3 (by positivity : (0 : ℝ) ≤ 24 * ((a : ℝ) + 1))
      linarith
    have e2 : 2 * (N : ℝ) ^ 3 * (8 * (a : ℝ) ^ 3) ≤
        2 * (16 * a) * (8 * (a : ℝ) ^ 3) * (N : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hN3 (by positivity : (0 : ℝ) ≤ 2 * (8 * (a : ℝ) ^ 3))
      linarith
    nlinarith [mul_nonneg hK0 hN2]

end AJConjecture
