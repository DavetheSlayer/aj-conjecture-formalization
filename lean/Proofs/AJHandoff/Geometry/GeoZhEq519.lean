import Mathlib
import AJHandoff.Geometry.GeoZhEq516

/-!
# Zheng's (5.19) for the corrected `b`, from the `b`-free bound `Ĥ_n = O(1)`

On the window `|n - N/2| + |i - N/4| < N/(8a)` every summand of the corrected `b_{n,i}` is `O(N)`
in absolute value: the arguments `i + j` stay in `(N/8, 7N/8)`, so `|1 - q_N^{±(i+j)}| ≥ 1/2`, and
`j/|1 - q_N^{-j}| ≤ N/2` by Jordan's inequality. Hence `‖b_{n,i}‖ ≤ 4N²` there
(`geoZh_norm_zhengB_window_le`; Zheng's (5.18) restricted to the window, for either sign of the
summed terms). Together with Zheng's Lemma 5.2 bound `Ĥ_n = O(1)` on the window, (5.12), which
does not involve `b`, this gives `ZhengEq519 a` (`zhengEq519_of_hatInput_bound`).
-/

open Real

noncomputable section

namespace AJConjecture

/-- Jordan's inequality on `[0, N]`: `sin(πx/N) ≥ 2 min(x, N - x)/N`. -/
theorem geoZh_sin_ge_min {N : ℕ} {x : ℝ} (hN : 0 < (N : ℝ)) (hx0 : 0 ≤ x) (hxN : x ≤ N) :
    2 * min x (N - x) / N ≤ Real.sin (Real.pi * x / N) := by
  have hpi := Real.pi_pos
  rcases le_total (2 * x) N with h | h
  · have h0 : 0 ≤ Real.pi * x / N := by positivity
    have hle : Real.pi * x / N ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hN two_pos]
      nlinarith
    refine le_trans ?_ (Real.mul_le_sin h0 hle)
    rw [show 2 / Real.pi * (Real.pi * x / N) = 2 * x / N by field_simp]
    gcongr
    exact min_le_left _ _
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
    exact min_le_right _ _

/-- `‖c/(1 - q_N^{-r})‖ ≤ ‖c‖/(2σ)` whenever `0 < σ ≤ 2 min(r, N - r)/N`, `0 ≤ r ≤ N`. -/
theorem geoZh_norm_div_one_sub_neg_le {N r : ℕ} (hrN : r ≤ N) {c : ℂ} {σ : ℝ} (hσ : 0 < σ)
    (hσle : σ ≤ 2 * min (r : ℝ) (N - r) / N) :
    ‖c / (1 - geoRootQ N ^ (-(r : ℤ)))‖ ≤ ‖c‖ / (2 * σ) := by
  have hN : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      simp at hσle
      linarith
    · exact_mod_cast h0
  have hsin := geoZh_sin_ge_min hN (Nat.cast_nonneg r) (by exact_mod_cast hrN)
  have hd : 2 * σ ≤ ‖1 - geoRootQ N ^ (-(r : ℤ))‖ := by
    rw [geoZh_norm_one_sub_rootQ_zpow, Int.cast_neg, mul_neg, neg_div, Real.sin_neg, abs_neg,
      Int.cast_natCast, abs_of_nonneg (by linarith)]
    linarith
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hd

/-- Corrected (5.18) on the window: `‖b_{n,i}‖ ≤ 4N²` for `|n - N/2| + |i - N/4| < N/(8a)`. -/
theorem geoZh_norm_zhengB_window_le {a N n i : ℕ} (ha : 1 ≤ a) (h : n + i < N)
    (hw : GeoInWindow N (N / (8 * a)) n i) : ‖geoZhengB N n i‖ ≤ 4 * (N : ℝ) ^ 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hrad : (N : ℝ) / (8 * a) ≤ N / 8 := by
    apply div_le_div_of_nonneg_left hN.le (by norm_num) (by linarith)
  unfold GeoInWindow at hw
  have hw' := lt_of_lt_of_le hw hrad
  have hn1 := le_abs_self ((n : ℝ) - N / 2)
  have hn2 := neg_abs_le ((n : ℝ) - N / 2)
  have hi1 := le_abs_self ((i : ℝ) - N / 4)
  have hi2 := neg_abs_le ((i : ℝ) - N / 4)
  have han0 := abs_nonneg ((n : ℝ) - N / 2)
  have hai0 := abs_nonneg ((i : ℝ) - N / 4)
  have hn5 : (n : ℝ) < 5 * N / 8 := by linarith
  have hi8 : (N : ℝ) / 8 < i := by linarith
  have hni : (n : ℝ) + i < 7 * N / 8 := by linarith
  unfold geoZhengB
  refine (norm_add_le _ _).trans ?_
  rw [neg_mul, norm_neg, norm_mul, Complex.norm_natCast,
    show (i : ℂ) + n = ((i + n : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  have hsum : ‖∑ j ∈ Finset.Icc 1 n,
      (((N : ℂ) - i - j) / (1 - geoRootQ N ^ (-(N : ℤ) + i + j)) +
        ((i : ℂ) + j) / (1 - geoRootQ N ^ (-((i : ℤ) + j))) -
        (j : ℂ) / (1 - geoRootQ N ^ (-(j : ℤ))))‖ ≤ n * (9 * N / 2) := by
    refine (norm_sum_le _ _).trans ?_
    have hcard : (Finset.Icc 1 n).card = n := by simp
    calc _ ≤ ∑ j ∈ Finset.Icc 1 n, (9 * N / 2 : ℝ) := by
          refine Finset.sum_le_sum fun j hj ↦ ?_
          obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.mp hj
          have hjr : (j : ℝ) ≤ n := by exact_mod_cast hjn
          have hj1r : (1 : ℝ) ≤ j := by exact_mod_cast hj1
          refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
          -- the two terms with argument `i + j ∈ (N/8, 7N/8)`
          have hm : (1 / 4 : ℝ) ≤ 2 * min ((i + j : ℕ) : ℝ) (N - (i + j : ℕ)) / N := by
            rw [le_div_iff₀ hN]
            push_cast
            rcases min_cases ((i : ℝ) + j) (N - (i + j)) with ⟨hmin, -⟩ | ⟨hmin, -⟩ <;>
              rw [hmin] <;> linarith
          have hm' : (1 / 4 : ℝ) ≤ 2 * min ((N - i - j : ℕ) : ℝ) (N - (N - i - j : ℕ)) / N := by
            rw [le_div_iff₀ hN, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
            rcases min_cases ((N : ℝ) - i - j) (N - (N - i - j)) with ⟨hmin, -⟩ | ⟨hmin, -⟩ <;>
              rw [hmin] <;> linarith
          have e1 := geoZh_norm_div_one_sub_neg_le (N := N) (r := N - i - j) (by omega)
            (c := (N : ℂ) - i - j) (by norm_num) hm'
          rw [show (-((N - i - j : ℕ) : ℤ)) = -(N : ℤ) + i + j by omega] at e1
          have e2 := geoZh_norm_div_one_sub_neg_le (N := N) (r := i + j) (by omega)
            (c := (i : ℂ) + j) (by norm_num) hm
          rw [show (-((i + j : ℕ) : ℤ)) = -((i : ℤ) + j) by push_cast; ring] at e2
          have hc1 : ‖(N : ℂ) - i - j‖ ≤ N := by
            rw [show (N : ℂ) - i - j = ((N - i - j : ℕ) : ℂ) by
              rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)], Complex.norm_natCast]
            exact_mod_cast (by omega : N - i - j ≤ N)
          have hc2 : ‖(i : ℂ) + j‖ ≤ N := by
            rw [show (i : ℂ) + j = ((i + j : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
            exact_mod_cast (by omega : i + j ≤ N)
          -- the term `j/(1 - q^{-j})`, `1 ≤ j < 5N/8`
          have e3 : ‖(j : ℂ) / (1 - geoRootQ N ^ (-(j : ℤ)))‖ ≤ N / 2 := by
            rcases le_total (2 * (j : ℝ)) N with hj2 | hj2
            · have hσ : 2 * (j : ℝ) / N ≤ 2 * min (j : ℝ) (N - j) / N := by
                rw [min_eq_left (by linarith)]
              have := geoZh_norm_div_one_sub_neg_le (N := N) (r := j) (by omega)
                (c := (j : ℂ)) (by positivity) hσ
              rw [Complex.norm_natCast] at this
              have hj0 : (0 : ℝ) < j := by linarith
              have hq : (j : ℝ) / (2 * (2 * j / N)) = N / 4 := by field_simp; ring
              rw [hq] at this
              linarith
            · have hσ : (3 / 4 : ℝ) ≤ 2 * min (j : ℝ) (N - j) / N := by
                rw [min_eq_right (by linarith), le_div_iff₀ hN]
                linarith
              have := geoZh_norm_div_one_sub_neg_le (N := N) (r := j) (by omega)
                (c := (j : ℂ)) (by norm_num) hσ
              rw [Complex.norm_natCast, show (j : ℝ) / (2 * (3 / 4)) = 2 * j / 3 by ring] at this
              linarith
          have e1' : ‖((N : ℂ) - i - j) / (1 - geoRootQ N ^ (-(N : ℤ) + i + j))‖ ≤ 2 * N := by
            rw [show ‖(N : ℂ) - i - j‖ / (2 * (1 / 4)) = 2 * ‖(N : ℂ) - i - j‖ by ring] at e1
            linarith
          have e2' : ‖((i : ℂ) + j) / (1 - geoRootQ N ^ (-((i : ℤ) + j)))‖ ≤ 2 * N := by
            rw [show ‖(i : ℂ) + j‖ / (2 * (1 / 4)) = 2 * ‖(i : ℂ) + j‖ by ring] at e2
            linarith
          linarith
      _ = n * (9 * N / 2) := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hin : ((i + n : ℕ) : ℝ) ≤ 7 * N / 8 := by push_cast; linarith
  calc (N : ℝ) * ((i + n : ℕ) : ℝ) + _ ≤ N * (7 * N / 8) + n * (9 * N / 2) := by
        gcongr
    _ ≤ 4 * (N : ℝ) ^ 2 := by nlinarith

/-- **Zheng (5.19) for the corrected `b`**, from the `b`-free bound `Ĥ_n = O(1)` on the window
(Zheng's (5.12), Lemma 5.2). -/
theorem zhengEq519_of_hatInput_bound (a : ℕ) (ha : 1 ≤ a)
    (hH : ∃ K : ℝ, ∀ N n i : ℕ, 1 ≤ N → n + i < N → GeoInWindow N (N / (8 * a)) n i →
      ‖geoHatInput a n (geoHalfRoot N)‖ ≤ K) :
    ZhengEq519 a := by
  obtain ⟨K, hK⟩ := hH
  refine ⟨4 * max K 0, fun N n i hN h hw ↦ ?_⟩
  rw [norm_mul]
  calc ‖geoZhengB N n i‖ * ‖geoHatInput a n (geoHalfRoot N)‖
      ≤ (4 * (N : ℝ) ^ 2) * max K 0 :=
        mul_le_mul (geoZh_norm_zhengB_window_le ha h hw) ((hK N n i hN h hw).trans
          (le_max_left _ _)) (norm_nonneg _) (by positivity)
    _ = 4 * max K 0 * (N : ℝ) ^ 2 := by ring

/-! ### From Zheng's colour window to the window in `(n, i)` -/

/-- Zheng, Lemma 5.2, (5.12), for the odd colours `c = 2n + 1` of `T(a, 2)` at `q = e^{2πi/N}`:
`Ĵ_{T(a,2),c} = O(1)` uniformly on `|c - N| < N/(2pq) = N/(4a)`. (Verbatim; `b`-free.) -/
def ZhengEq512 (a : ℕ) : Prop :=
  ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N n : ℕ, N₀ ≤ N → n < N → |(2 * n + 1 : ℝ) - N| < N / (4 * a) →
    ‖geoHatInput a n (geoHalfRoot N)‖ ≤ K

/-- One step in the colour: `Ĥ_{n+1} = s^{-8a(n+1)} Ĥ_n + O(1)` on `|s| = 1` (two new terms). -/
theorem geoZh_hatInput_succ (a n : ℕ) {s : ℂ} (hs : ‖s‖ = 1) :
    ‖geoHatInput a (n + 1) s - s ^ (-(8 * (a : ℤ) * (n + 1))) * geoHatInput a n s‖ ≤ 4 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs
    exact zero_ne_one hs
  have hpow : ∀ m : ℤ, ‖s ^ m‖ = 1 := fun m ↦ by rw [norm_zpow, hs, one_zpow]
  set f : ℤ → ℂ := fun k ↦
    s ^ (2 * (a : ℤ) * k * (2 * k + 1)) * (s ^ (4 * k + 1) - s ^ (-(4 * k + 1))) with hf
  have hfb : ∀ k, ‖f k‖ ≤ 2 := fun k ↦ by
    rw [hf, norm_mul, hpow, one_mul]
    refine (norm_sub_le _ _).trans ?_
    rw [hpow, hpow]
    norm_num
  have hsplit : Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1) =
      {-((n : ℤ) + 1), (n : ℤ) + 1} ∪ Finset.Icc (-(n : ℤ)) n := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hdisj : Disjoint ({-((n : ℤ) + 1), (n : ℤ) + 1} : Finset ℤ) (Finset.Icc (-(n : ℤ)) n) := by
    rw [Finset.disjoint_left]
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [Finset.mem_Icc]
    omega
  have hpre : s ^ (-(4 * (a : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 1 + 1))) =
      s ^ (-(8 * (a : ℤ) * (n + 1))) * s ^ (-(4 * (a : ℤ) * n * (n + 1))) := by
    rw [← zpow_add₀ hs0]
    congr 1
    ring
  have hH : ∀ m : ℕ, geoHatInput a m s =
      s ^ (-(4 * (a : ℤ) * m * (m + 1))) * ∑ k ∈ Finset.Icc (-(m : ℤ)) m, f k := fun m ↦ rfl
  rw [hH, hH]
  push_cast
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_pair (by omega), hpre]
  have : s ^ (-(8 * (a : ℤ) * (n + 1))) * s ^ (-(4 * (a : ℤ) * n * (n + 1))) *
        (f (-((n : ℤ) + 1)) + f ((n : ℤ) + 1) + ∑ k ∈ Finset.Icc (-(n : ℤ)) n, f k) -
      s ^ (-(8 * (a : ℤ) * (n + 1))) *
        (s ^ (-(4 * (a : ℤ) * n * (n + 1))) * ∑ k ∈ Finset.Icc (-(n : ℤ)) n, f k) =
      s ^ (-(8 * (a : ℤ) * (n + 1))) * s ^ (-(4 * (a : ℤ) * n * (n + 1))) *
        (f (-((n : ℤ) + 1)) + f ((n : ℤ) + 1)) := by ring
  rw [this, norm_mul, norm_mul, hpow, hpow, one_mul, one_mul]
  refine (norm_add_le _ _).trans ?_
  linarith [hfb (-((n : ℤ) + 1)), hfb ((n : ℤ) + 1)]

/-- Lemma W for `Ĥ`: Zheng's (5.12) on his colour window implies `Ĥ_n = O(1)` on the window
`|n - N/2| + |i - N/4| < N/(8a)` (whose colours satisfy only `|2n + 1 - N| < N/(4a) + 1`). -/
theorem geoZh_hatInput_window_bound (a : ℕ) (ha : 1 ≤ a) (h : ZhengEq512 a) :
    ∃ K : ℝ, ∀ N n i : ℕ, 1 ≤ N → n + i < N → GeoInWindow N (N / (8 * a)) n i →
      ‖geoHatInput a n (geoHalfRoot N)‖ ≤ K := by
  obtain ⟨K, N₀, hK⟩ := h
  refine ⟨max (K + 4) (4 * (N₀ + 8 * a)), fun N n i hN hni hw ↦ ?_⟩
  have hs := geoZh_norm_halfRoot N
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnN : (n : ℝ) + 1 ≤ N := by exact_mod_cast (by omega : n + 1 ≤ N)
  by_cases hsmall : N < N₀ + 8 * a
  · -- finitely many `N`: the trivial bound `‖Ĥ_n‖ ≤ 2(2n + 1) < 4N`
    refine (geoZh_norm_hatInput_le a n hs).trans (le_trans ?_ (le_max_right _ _))
    have : (N : ℝ) ≤ N₀ + 8 * a := by exact_mod_cast hsmall.le
    linarith
  rw [not_lt] at hsmall
  have hN0 : N₀ ≤ N := by omega
  have hN8 : 8 * (a : ℝ) ≤ N := by exact_mod_cast (by omega : 8 * a ≤ N)
  have hpos : (0 : ℝ) < 4 * a := by positivity
  have hq : (2 : ℝ) ≤ N / (4 * a) := by rw [le_div_iff₀ hpos]; linarith
  -- the colour of `n` is within `N/(4a) + 1` of `N`
  unfold GeoInWindow at hw
  have hn' : |(n : ℝ) - N / 2| < N / (8 * a) := by
    linarith [abs_nonneg ((i : ℝ) - N / 4)]
  have hc : |(2 * n + 1 : ℝ) - N| < N / (4 * a) + 1 := by
    have h8 : (N : ℝ) / (4 * a) = 2 * (N / (8 * a)) := by field_simp; ring
    rw [show (2 * n + 1 : ℝ) - N = 2 * ((n : ℝ) - N / 2) + 1 by ring]
    refine (abs_add_le _ _).trans_lt ?_
    rw [abs_mul, abs_two, abs_one, h8]
    linarith
  by_cases hin : |(2 * n + 1 : ℝ) - N| < N / (4 * a)
  · exact (hK N n hN0 (by omega) hin).trans (by linarith [le_max_left (K + 4) (4 * (N₀ + 8 * a))])
  rw [not_lt] at hin
  refine le_trans ?_ (le_max_left _ _)
  rcases le_or_gt (N : ℝ) (2 * n + 1) with hup | hlo
  · -- step down to `n - 1`
    rw [abs_of_nonneg (by linarith)] at hc hin
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
      have : (1 : ℝ) ≤ n := by linarith
      have : 1 ≤ n := by exact_mod_cast this
      omega⟩
    push_cast at hc hin hnN ⊢
    have hm := hK N m hN0 (by omega) (by rw [abs_lt]; constructor <;> linarith)
    have hstep := geoZh_hatInput_succ a m hs
    have : ‖geoHatInput a (m + 1) (geoHalfRoot N)‖ ≤
        ‖geoHalfRoot N ^ (-(8 * (a : ℤ) * (m + 1))) * geoHatInput a m (geoHalfRoot N)‖ + 4 := by
      have := norm_sub_norm_le (geoHatInput a (m + 1) (geoHalfRoot N))
        (geoHalfRoot N ^ (-(8 * (a : ℤ) * (m + 1))) * geoHatInput a m (geoHalfRoot N))
      linarith
    rw [norm_mul, norm_zpow, hs, one_zpow, one_mul] at this
    linarith
  · -- step up to `n + 1`
    rw [abs_of_neg (by linarith)] at hc hin
    have hm := hK N (n + 1) hN0 (by
      have : (2 * n + 3 : ℝ) ≤ N := by linarith
      have : 2 * n + 3 ≤ N := by exact_mod_cast this
      omega) (by push_cast; rw [abs_lt]; constructor <;> linarith)
    have hstep := geoZh_hatInput_succ a n hs
    have : ‖geoHalfRoot N ^ (-(8 * (a : ℤ) * (n + 1))) * geoHatInput a n (geoHalfRoot N)‖ ≤
        ‖geoHatInput a (n + 1) (geoHalfRoot N)‖ + 4 := by
      have := norm_sub_norm_le
        (geoHalfRoot N ^ (-(8 * (a : ℤ) * (n + 1))) * geoHatInput a n (geoHalfRoot N))
        (geoHatInput a (n + 1) (geoHalfRoot N))
      rw [norm_sub_rev] at this
      linarith
    rw [norm_mul, norm_zpow, hs, one_zpow, one_mul] at this
    linarith

/-- **Zheng (5.19) for the corrected `b`**, conditional only on the verbatim, `b`-free (5.12). -/
theorem zhengEq519_of_zhengEq512 (a : ℕ) (ha : 1 ≤ a) (h : ZhengEq512 a) : ZhengEq519 a :=
  zhengEq519_of_hatInput_bound a ha (geoZh_hatInput_window_bound a ha h)

end AJConjecture
