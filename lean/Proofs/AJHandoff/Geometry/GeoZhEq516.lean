import Mathlib
import AJHandoff.Geometry.GeoPhysDefs
import AJHandoff.Geometry.GeoPhysReducedValue

/-!
# Zheng's (5.16) for the corrected `b` (unconditional)

For every `a`, the bracket `b_{n,i} Ĥ_n + q∂_q Ĥ_n` of Zheng's diagonal (5.3) is `O(N⁴)` uniformly
on `n + i < N` (`ZhengEq516 a`), with the corrected sign of `b_{n,i}` used in `geoZhengB`.

The proof bounds each summand in absolute value, so the sign of the three summed terms of `b`
plays no role:
* `‖1 - q_N^m‖ = 2|sin(πm/N)| ≥ 4/N` for `1 ≤ |m| < N` (Jordan's inequality), hence each summand
  of `b_{n,i}` is at most `N²/4` and `‖b_{n,i}‖ ≤ N² + (3/4) n N²`;
* `‖Ĥ_n(s)‖ ≤ 2(2n + 1)` since `|s| = 1`;
* `q∂_q Ĥ_n = (s/2) Ĥ_n'(s)` is a sum of `O(n)` monomials with exponents `O((a + 1) N²)`.
-/

open Real

noncomputable section

namespace AJConjecture

/-- `q_N^m = exp(2 (πm/N) i)`. -/
theorem geoZh_rootQ_zpow (N : ℕ) (m : ℤ) :
    geoRootQ N ^ m = Complex.exp (2 * ((Real.pi * m / N : ℝ) : ℂ) * Complex.I) := by
  rw [geoRootQ, geoHalfRoot, ← Complex.exp_nat_mul, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- `‖1 - q_N^m‖ = 2 |sin(πm/N)|`. -/
theorem geoZh_norm_one_sub_rootQ_zpow (N : ℕ) (m : ℤ) :
    ‖1 - geoRootQ N ^ m‖ = 2 * |Real.sin (Real.pi * m / N)| := by
  rw [geoZh_rootQ_zpow, geo_one_sub_exp_two_mul_I, norm_mul]
  have h : ((Real.pi * m / N : ℝ) : ℂ) - Real.pi / 2 =
      ((Real.pi * m / N - Real.pi / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_two]

/-- Jordan's inequality at the points `πx/N`, `1 ≤ x ≤ N - 1`: `sin(πx/N) ≥ 2/N`. -/
theorem geoZh_sin_ge {N : ℕ} {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ N - 1) :
    2 / N ≤ Real.sin (Real.pi * x / N) := by
  have hN : (0 : ℝ) < N := by linarith
  have hpi := Real.pi_pos
  rcases le_total (2 * x) N with h | h
  · have h0 : 0 ≤ Real.pi * x / N := by positivity
    have hle : Real.pi * x / N ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hN two_pos]
      nlinarith
    refine le_trans ?_ (Real.mul_le_sin h0 hle)
    rw [show 2 / Real.pi * (Real.pi * x / N) = 2 * x / N by field_simp]
    gcongr
    linarith
  · have hs : Real.sin (Real.pi * x / N) = Real.sin (Real.pi * (N - x) / N) := by
      rw [← Real.sin_pi_sub]
      congr 1
      field_simp
    rw [hs]
    have h0 : 0 ≤ Real.pi * (N - x) / N := by
      apply div_nonneg _ hN.le
      nlinarith
    have hle : Real.pi * (N - x) / N ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hN two_pos]
      nlinarith
    refine le_trans ?_ (Real.mul_le_sin h0 hle)
    rw [show 2 / Real.pi * (Real.pi * (N - x) / N) = 2 * (N - x) / N by field_simp]
    gcongr
    linarith

/-- `‖1 - q_N^m‖ ≥ 4/N` for `1 ≤ |m| < N`. -/
theorem geoZh_norm_one_sub_rootQ_zpow_ge {N : ℕ} {m : ℤ} (h1 : 1 ≤ |m|) (h2 : |m| < N) :
    4 / N ≤ ‖1 - geoRootQ N ^ m‖ := by
  rw [geoZh_norm_one_sub_rootQ_zpow]
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast h1
  have hm2 : |(m : ℝ)| ≤ N - 1 := by
    have : |m| + 1 ≤ N := by omega
    have : (|m| : ℝ) + 1 ≤ N := by exact_mod_cast this
    linarith
  have key := geoZh_sin_ge hm1 hm2
  have h4 : (4 : ℝ) / N = 2 * (2 / N) := by ring
  rcases abs_cases (m : ℝ) with ⟨hm, -⟩ | ⟨hm, -⟩
  · rw [hm] at key
    rw [abs_of_nonneg (le_trans (by positivity) key)]
    linarith
  · rw [hm, mul_neg, neg_div, Real.sin_neg] at key
    rw [abs_of_nonpos (by linarith [show (0 : ℝ) ≤ 2 / N by positivity])]
    linarith

/-- A summand `c/(1 - q_N^m)` of `b_{n,i}` with `‖c‖ ≤ N`, `1 ≤ |m| < N` is at most `N²/4`. -/
theorem geoZh_norm_div_one_sub_le {N : ℕ} {m : ℤ} (h1 : 1 ≤ |m|) (h2 : |m| < N) {c : ℂ}
    (hc : ‖c‖ ≤ N) : ‖c / (1 - geoRootQ N ^ m)‖ ≤ (N : ℝ) ^ 2 / 4 := by
  have hN : (0 : ℝ) < N := by
    have : (0 : ℤ) < N := by omega
    exact_mod_cast this
  have hd := geoZh_norm_one_sub_rootQ_zpow_ge h1 h2
  have hpos : 0 < ‖1 - geoRootQ N ^ m‖ := lt_of_lt_of_le (by positivity) hd
  rw [norm_div, div_le_iff₀ hpos]
  calc ‖c‖ ≤ N := hc
    _ = (N : ℝ) ^ 2 / 4 * (4 / N) := by field_simp
    _ ≤ _ := by gcongr

/-- `‖b_{n,i}‖ ≤ N² + (3/4) n N²` on `n + i < N` (corrected sign). -/
theorem geoZh_norm_zhengB_le {N n i : ℕ} (h : n + i < N) :
    ‖geoZhengB N n i‖ ≤ (N : ℝ) ^ 2 + n * (3 * (N : ℝ) ^ 2 / 4) := by
  unfold geoZhengB
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [neg_mul, norm_neg, norm_mul, Complex.norm_natCast,
      show (i : ℂ) + n = ((i + n : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast, sq]
    gcongr
    exact_mod_cast (by omega : i + n ≤ N)
  · refine (norm_sum_le _ _).trans ?_
    have hcard : (Finset.Icc 1 n).card = n := by simp
    calc ∑ j ∈ Finset.Icc 1 n, ‖((N : ℂ) - i - j) / (1 - geoRootQ N ^ (-(N : ℤ) + i + j)) +
            ((i : ℂ) + j) / (1 - geoRootQ N ^ (-((i : ℤ) + j))) -
            (j : ℂ) / (1 - geoRootQ N ^ (-(j : ℤ)))‖
        ≤ ∑ j ∈ Finset.Icc 1 n, 3 * (N : ℝ) ^ 2 / 4 := by
          refine Finset.sum_le_sum fun j hj ↦ ?_
          obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.mp hj
          refine (norm_sub_le _ _).trans ?_
          refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
          have e1 := geoZh_norm_div_one_sub_le (N := N) (m := -(N : ℤ) + i + j)
              (by rw [abs_of_neg (by omega)]; omega) (by rw [abs_of_neg (by omega)]; omega)
              (c := (N : ℂ) - i - j) (by
                rw [show (N : ℂ) - i - j = ((N - i - j : ℕ) : ℂ) by
                  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)], Complex.norm_natCast]
                exact_mod_cast (by omega : N - i - j ≤ N))
          have e2 := geoZh_norm_div_one_sub_le (N := N) (m := -((i : ℤ) + j))
              (by rw [abs_neg, abs_of_pos (by omega)]; omega)
              (by rw [abs_neg, abs_of_pos (by omega)]; omega)
              (c := (i : ℂ) + j) (by
                rw [show (i : ℂ) + j = ((i + j : ℕ) : ℂ) by push_cast; ring,
                  Complex.norm_natCast]
                exact_mod_cast (by omega : i + j ≤ N))
          have e3 := geoZh_norm_div_one_sub_le (N := N) (m := -(j : ℤ))
              (by rw [abs_neg, abs_of_pos (by omega)]; omega)
              (by rw [abs_neg, abs_of_pos (by omega)]; omega)
              (c := (j : ℂ)) (by
                rw [Complex.norm_natCast]
                exact_mod_cast (by omega : j ≤ N))
          linarith
      _ = n * (3 * (N : ℝ) ^ 2 / 4) := by rw [Finset.sum_const, hcard, nsmul_eq_mul]

/-- `|s_N| = 1`. -/
theorem geoZh_norm_halfRoot (N : ℕ) : ‖geoHalfRoot N‖ = 1 := by
  rw [geoHalfRoot, show (Real.pi : ℂ) * Complex.I / N = ((Real.pi / N : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-- `‖Ĥ_n(s)‖ ≤ 2(2n + 1)` for `|s| = 1`. -/
theorem geoZh_norm_hatInput_le (a n : ℕ) {s : ℂ} (hs : ‖s‖ = 1) :
    ‖geoHatInput a n s‖ ≤ 2 * (2 * n + 1) := by
  have hpow : ∀ m : ℤ, ‖s ^ m‖ = 1 := fun m ↦ by rw [norm_zpow, hs, one_zpow]
  have hcard : ((Finset.Icc (-(n : ℤ)) n).card : ℝ) = 2 * n + 1 := by
    rw [Int.card_Icc, show (n : ℤ) + 1 - -(n : ℤ) = ((2 * n + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast]
    push_cast
    ring
  unfold geoHatInput
  rw [norm_mul, hpow, one_mul]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        ‖s ^ (2 * (a : ℤ) * k * (2 * k + 1)) * (s ^ (4 * k + 1) - s ^ (-(4 * k + 1)))‖
      ≤ ∑ k ∈ Finset.Icc (-(n : ℤ)) n, (2 : ℝ) := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        rw [norm_mul, hpow, one_mul]
        refine (norm_sub_le _ _).trans ?_
        rw [hpow, hpow]
        norm_num
    _ = 2 * (2 * n + 1) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring

/-- The exponents of `Ĥ_n` are at most `4(a + 1)N²` in absolute value. -/
theorem geoZh_exponent_bounds {a n N : ℕ} (hn : n < N) {k : ℤ}
    (hk : k ∈ Finset.Icc (-(n : ℤ)) n) :
    |((2 * (a : ℤ) * k * (2 * k + 1) : ℤ) : ℝ)| ≤ 4 * (a + 1) * (N : ℝ) ^ 2 ∧
      |((4 * k + 1 : ℤ) : ℝ)| ≤ 4 * (a + 1) * (N : ℝ) ^ 2 ∧
      |((-(4 * k + 1) : ℤ) : ℝ)| ≤ 4 * (a + 1) * (N : ℝ) ^ 2 := by
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have hk1' : -(n : ℝ) ≤ k := by exact_mod_cast hk1
  have hk2' : (k : ℝ) ≤ n := by exact_mod_cast hk2
  have hnN : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hf : |(4 * (k : ℝ) + 1)| ≤ 4 * (a + 1) * (N : ℝ) ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg ha (sq_nonneg (N : ℝ))]
  push_cast
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, hf, by rw [abs_neg]; exact hf⟩
  · nlinarith [mul_nonneg ha (sq_nonneg (k : ℝ)), mul_nonneg ha (by linarith : (0 : ℝ) ≤ k + n),
      mul_nonneg ha (by linarith : (0 : ℝ) ≤ N - n),
      mul_nonneg (by linarith : (0 : ℝ) ≤ a + 1) (by nlinarith : (0 : ℝ) ≤ N * (N - 1))]
  · nlinarith [mul_nonneg ha (mul_nonneg (by linarith : (0 : ℝ) ≤ n - k)
        (by linarith : (0 : ℝ) ≤ n + k)), mul_nonneg ha (by linarith : (0 : ℝ) ≤ n - k),
      mul_nonneg ha (mul_nonneg (by linarith : (0 : ℝ) ≤ N - n - 1)
        (by linarith : (0 : ℝ) ≤ N + n + 1)), sq_nonneg (N : ℝ)]

/-- `‖q∂_q Ĥ_n‖ ≤ 24(a + 1)N³` for `n < N`. -/
theorem geoZh_norm_hatInputDeriv_le (a n N : ℕ) (hn : n < N) :
    ‖geoHatInputDeriv a n N‖ ≤ 24 * (a + 1) * (N : ℝ) ^ 3 := by
  set s := geoHalfRoot N with hs_def
  have hs1 : ‖s‖ = 1 := geoZh_norm_halfRoot N
  have hs : s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs1
    exact zero_ne_one hs1
  have hpow : ∀ m : ℤ, ‖s ^ m‖ = 1 := fun m ↦ by rw [norm_zpow, hs1, one_zpow]
  have hd : HasDerivAt (geoHatInput a n) _ s :=
    (hasDerivAt_zpow (-(4 * (a : ℤ) * n * (n + 1))) s (Or.inl hs)).fun_mul
      (HasDerivAt.fun_sum (u := Finset.Icc (-(n : ℤ)) n) fun k _ ↦
        (hasDerivAt_zpow (2 * (a : ℤ) * k * (2 * k + 1)) s (Or.inl hs)).fun_mul
          ((hasDerivAt_zpow (4 * k + 1) s (Or.inl hs)).fun_sub
            (hasDerivAt_zpow (-(4 * k + 1)) s (Or.inl hs))))
  set B : ℝ := 4 * (a + 1) * (N : ℝ) ^ 2 with hB
  have hNr : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
  have hB0 : 0 ≤ B := by positivity
  have hcard : ((Finset.Icc (-(n : ℤ)) n).card : ℝ) = 2 * n + 1 := by
    rw [Int.card_Icc, show (n : ℤ) + 1 - -(n : ℤ) = ((2 * n + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast]
    push_cast
    ring
  have hE : |((-(4 * (a : ℤ) * n * (n + 1)) : ℤ) : ℝ)| ≤ B := by
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity), hB]
    nlinarith [mul_nonneg ha (mul_nonneg hn0 (by linarith : (0 : ℝ) ≤ N - n - 1)),
      mul_nonneg ha (by linarith : (0 : ℝ) ≤ N - n - 1), sq_nonneg (N : ℝ)]
  have hg : ‖∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      s ^ (2 * (a : ℤ) * k * (2 * k + 1)) * (s ^ (4 * k + 1) - s ^ (-(4 * k + 1)))‖ ≤
      2 * (2 * n + 1) := by
    have h := geoZh_norm_hatInput_le a n hs1
    unfold geoHatInput at h
    rwa [norm_mul, hpow, one_mul] at h
  unfold geoHatInputDeriv
  rw [← hs_def, hd.deriv, norm_mul, norm_div, hs1, Complex.norm_ofNat]
  refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)).trans ?_
  rw [norm_mul, norm_mul, norm_mul, hpow, hpow, one_mul, mul_one, Complex.norm_intCast]
  have hsum : ‖∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      ((((2 * (a : ℤ) * k * (2 * k + 1)) : ℤ) : ℂ) * s ^ (2 * (a : ℤ) * k * (2 * k + 1) - 1) *
          (s ^ (4 * k + 1) - s ^ (-(4 * k + 1))) +
        s ^ (2 * (a : ℤ) * k * (2 * k + 1)) *
          ((((4 * k + 1) : ℤ) : ℂ) * s ^ (4 * k + 1 - 1) -
            (((-(4 * k + 1)) : ℤ) : ℂ) * s ^ (-(4 * k + 1) - 1)))‖ ≤ 4 * B * (2 * n + 1) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ k ∈ Finset.Icc (-(n : ℤ)) n, 4 * B := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          obtain ⟨h1, h2, h3⟩ := geoZh_exponent_bounds (a := a) hn hk
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_mul, hpow, hpow, mul_one, one_mul,
            Complex.norm_intCast]
          have hdiff : ‖s ^ (4 * k + 1) - s ^ (-(4 * k + 1))‖ ≤ 2 := by
            refine (norm_sub_le _ _).trans ?_
            rw [hpow, hpow]
            norm_num
          have hdiff' : ‖(((4 * k + 1 : ℤ)) : ℂ) * s ^ (4 * k + 1 - 1) -
              (((-(4 * k + 1)) : ℤ) : ℂ) * s ^ (-(4 * k + 1) - 1)‖ ≤ 2 * B := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul, hpow, hpow, mul_one, mul_one, Complex.norm_intCast,
              Complex.norm_intCast]
            linarith
          nlinarith [abs_nonneg ((2 * (a : ℤ) * k * (2 * k + 1) : ℤ) : ℝ)]
      _ = 4 * B * (2 * n + 1) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
  calc 1 / 2 * (|((-(4 * (a : ℤ) * n * (n + 1)) : ℤ) : ℝ)| *
        ‖∑ k ∈ Finset.Icc (-(n : ℤ)) n,
          s ^ (2 * (a : ℤ) * k * (2 * k + 1)) * (s ^ (4 * k + 1) - s ^ (-(4 * k + 1)))‖ + _)
      ≤ 1 / 2 * (B * (2 * (2 * n + 1)) + 4 * B * (2 * n + 1)) := by
        gcongr
    _ = 3 * B * (2 * n + 1) := by ring
    _ ≤ 3 * B * (2 * N) := by gcongr; linarith
    _ = 24 * (a + 1) * (N : ℝ) ^ 3 := by rw [hB]; ring

/-- Zheng's (5.16) for the corrected `b`: the bracket is `O(N⁴)` on `n + i < N`. -/
theorem zhengEq516_holds (a : ℕ) : ZhengEq516 a := by
  refine ⟨7 + 24 * (a + 1), fun N n i hN h ↦ ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (n : ℝ) + 1 ≤ N := by exact_mod_cast (by omega : n + 1 ≤ N)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb := geoZh_norm_zhengB_le h
  have hH := geoZh_norm_hatInput_le a n (geoZh_norm_halfRoot N)
  have hD := geoZh_norm_hatInputDeriv_le a n N (by omega)
  have h1 : (N : ℝ) ^ 2 + n * (3 * (N : ℝ) ^ 2 / 4) ≤ 7 / 4 * (N : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : (n : ℝ) ≤ N - 1) (sq_nonneg (N : ℝ)),
      mul_le_mul_of_nonneg_right hN1 (sq_nonneg (N : ℝ))]
  have h2 : 2 * (2 * (n : ℝ) + 1) ≤ 4 * N := by linarith
  have h3 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hN1 (pow_nonneg (by linarith : (0 : ℝ) ≤ N) 3)]
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  calc ‖geoZhengB N n i * geoHatInput a n (geoHalfRoot N) + geoHatInputDeriv a n N‖
      ≤ ‖geoZhengB N n i‖ * ‖geoHatInput a n (geoHalfRoot N)‖ + ‖geoHatInputDeriv a n N‖ := by
        rw [← norm_mul]
        exact norm_add_le _ _
    _ ≤ (7 / 4 * (N : ℝ) ^ 3) * (4 * N) + 24 * (a + 1) * (N : ℝ) ^ 3 := by
        gcongr
        · exact hb.trans h1
        · exact hH.trans h2
    _ ≤ (7 + 24 * (a + 1)) * (N : ℝ) ^ 4 := by
        nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 24 * (a + 1))]

end AJConjecture
