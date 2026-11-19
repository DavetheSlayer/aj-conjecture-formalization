import Mathlib
import AJTwist.Select.TwSCoefDefs

/-!
# The finite-cutoff estimate, `θ = 1`

Source: Lemma 6.2 (`lem:coefficient-cutoff`) of `selection.tex` (revision 5), case `θ = 1`, in
the cleared form: if `ν(w_n) ≥ -C`, then `twsCoefM true w` is a controlled expansion of
`twsClearedY true w`.

Proof. As for `θ = 0`. On the triangle the order of `τ(n,i,j) q^(N(i+j))` is at least
`i N + j (N - i - n) + n(n+1)/2 + j(j-1)/2 - C`: for `i ≥ H` this is `≥ H N - C`; otherwise
`j ≥ H - i` gives `≥ H N - (H - i)(i + n) + n²/2 - C`. Outside the triangle the order before
evaluation is `(n - j)(n - j + 1)/2 - i j - C` with `n - j ≥ N - H + 1`, at least
`(N - H)²/2 - H² - C`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A finite sum of series of order at least `g` has order at least `g`. -/
private theorem le_orderTop_sum_twsCutoffOne {ι : Type*} (s : Finset ι)
    (f : ι → LaurentSeries ℚ) (g : WithTop ℤ) (h : ∀ i ∈ s, g ≤ (f i).orderTop) :
    g ≤ (∑ i ∈ s, f i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, HahnSeries.orderTop_zero]
    exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))) HahnSeries.min_orderTop_le_orderTop_add

/-- The order of a difference of two initial segments of a sum is bounded by the orders of the
terms between the two ends. -/
private theorem le_orderTop_range_sub_range_twsCutoffOne (f : ℕ → LaurentSeries ℚ) (a b : ℕ)
    (g : WithTop ℤ)
    (h : ∀ i : ℕ, (b ≤ i ∧ i < a) ∨ (a ≤ i ∧ i < b) → g ≤ (f i).orderTop) :
    g ≤ (∑ i ∈ Finset.range a, f i - ∑ i ∈ Finset.range b, f i).orderTop := by
  rcases le_total b a with hab | hab
  · rw [← Finset.sum_Ico_eq_sub _ hab]
    exact le_orderTop_sum_twsCutoffOne _ _ g fun i hi ↦ h i (Or.inl (Finset.mem_Ico.mp hi))
  · rw [← neg_sub, ← Finset.sum_Ico_eq_sub _ hab, HahnSeries.orderTop_neg]
    exact le_orderTop_sum_twsCutoffOne _ _ g fun i hi ↦ h i (Or.inr (Finset.mem_Ico.mp hi))

/-- The order of a product with a monomial. -/
private theorem le_orderTop_mul_twsT_twsCutoffOne {x : LaurentSeries ℚ} {G k : ℤ}
    (h : ((G - k : ℤ) : WithTop ℤ) ≤ x.orderTop) : (G : WithTop ℤ) ≤ (x * twsT k).orderTop := by
  rw [HahnSeries.orderTop_mul, twsT, HahnSeries.orderTop_single one_ne_zero]
  have h2 := add_le_add_left h (k : WithTop ℤ)
  rwa [← WithTop.coe_add, sub_add_cancel] at h2

/-- The expansion of a power of `q`. -/
private theorem twsSeries_qParam_pow_twsCutoffOne (k : ℕ) :
    twsSeries (qParam ^ k) = twsT (4 * (k : ℤ)) := by
  rw [← zpow_natCast, qParam_zpow_eq_ratFuncX_zpow, twsSeries_X_zpow]

/-- The expansion of `1 - q` has order `0`. -/
private theorem orderTop_twsSeries_one_sub_qParam_twsCutoffOne :
    (twsSeries (1 - qParam)).orderTop = 0 := by
  have h := pairQTOrder_one_sub_qParam_zpow_of_pos (k := 1) one_pos
  rw [zpow_one] at h
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero twsSeries).mpr h.1),
    tws_order_twsSeries h.1, h.2]
  rfl

/-- The first estimate of Lemma 6.2, `θ = 1`: the exponents on the finite triangle. -/
private theorem triangle_exponent_twsCutoffOne {N H n i j : ℤ} (hH : 0 ≤ H) (hn : 0 ≤ n)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hjn : j ≤ n) (h1 : i + n < N) (h2 : H ≤ i + j) :
    4 * H * N - 10 * H ^ 2 ≤
      2 * n * (n + 1) + 2 * j * (j - 1) - 4 * j * (i + n) + 4 * N * (i + j) := by
  have hjj : 0 ≤ j * (j - 1) := by
    rcases hj.eq_or_lt with rfl | hpos
    · simp
    · exact mul_nonneg hj (by omega)
  rcases le_or_gt H i with hHi | hiH
  · nlinarith [mul_nonneg (sub_nonneg.mpr hHi) (by omega : (0 : ℤ) ≤ N),
      mul_nonneg hj (by omega : (0 : ℤ) ≤ N - i - n), mul_nonneg hn hn, mul_nonneg hH hH]
  · have e1 : 0 ≤ (j - (H - i)) * (N - i - n) := mul_nonneg (by omega) (by omega)
    have e2 : 0 ≤ i * (i + n) := mul_nonneg hi (by omega)
    have e3 : 0 ≤ (H - i) * (H - i) := mul_nonneg (by omega) (by omega)
    have e4 : 0 ≤ i * (H - i) := mul_nonneg hi (by omega)
    nlinarith [sq_nonneg (n - H), mul_nonneg hH hH, mul_nonneg hi hn]

/-- The second estimate of Lemma 6.2, `θ = 1`: the exponents of the omitted terms. -/
private theorem omitted_exponent_twsCutoffOne {N H n i j : ℤ} (hN : 0 ≤ N)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hjn : j ≤ n) (h1 : i + j < H) (h2 : N ≤ i + n) :
    4 * H * N - 10 * H ^ 2 ≤
      2 * n * (n + 1) + 2 * j * (j - 1) - 4 * j * (i + n) + 4 * N * (i + j) := by
  have e1 : 0 ≤ (H - i) * (H - j) := mul_nonneg (by omega) (by omega)
  have e2 : 0 ≤ N * (i + j) := mul_nonneg hN (by omega)
  have e3 : 0 ≤ H * (n - j + H - N) := mul_nonneg (by omega) (by omega)
  have e4 : 0 ≤ i * H := mul_nonneg hi (by omega)
  have e5 : 0 ≤ j * H := mul_nonneg hj (by omega)
  nlinarith [sq_nonneg (n - j - H), mul_nonneg hi hj]

/-- The order of a term `τ(n, i, j) q^(N (i + j))` on the high part of the triangle and outside
the triangle. -/
private theorem le_orderTop_twsTerm_twsCutoffOne {w : ℕ → RatFunc ℚ} {C : ℤ}
    (hw : ∀ n : ℕ, w n = 0 ∨ -C ≤ pairQTOrder (w n)) (N H : ℕ) {n i j : ℕ} (hjn : j ≤ n)
    (h : (i + n < N ∧ H ≤ i + j) ∨ (i + j < H ∧ N ≤ i + n)) :
    ((4 * (H : ℤ) * N - (C + 10 * (H : ℤ) ^ 2) - 4 * ((N : ℤ) * ((i : ℤ) + j)) : ℤ) :
      WithTop ℤ) ≤ (twsSeries (twsTerm true w n i j)).orderTop := by
  by_cases h0 : w n = 0
  · have hz : twsTerm true w n i j = 0 := by simp [twsTerm, h0]
    rw [hz, map_zero, HahnSeries.orderTop_zero]
    exact le_top
  have hord := (hw n).resolve_left h0
  have ht := tws_tOrder_twsTerm true h0 i hjn
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero twsSeries).mpr ht.1),
    tws_order_twsSeries ht.1, ht.2, WithTop.coe_le_coe]
  simp only [↓reduceIte]
  have key : 4 * (H : ℤ) * N - 10 * (H : ℤ) ^ 2 ≤
      2 * (n : ℤ) * (n + 1) + 2 * (j : ℤ) * (j - 1) - 4 * (j : ℤ) * (i + n) +
        4 * (N : ℤ) * (i + j) := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact triangle_exponent_twsCutoffOne (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
    · exact omitted_exponent_twsCutoffOne (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
  linarith

/-- The terms of total degree less than `H`, summed along the diagonals `i + j = d`, are the
terms with `i < H - j`. -/
private theorem sum_diagonal_twsCutoffOne (F : ℕ → ℕ → RatFunc ℚ) (H n : ℕ) :
    ∑ d ∈ Finset.range H, ∑ j ∈ Finset.range (min n d + 1), F (d - j) j =
      ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (H - j), F i j := by
  rw [Finset.sum_comm' (s' := fun j ↦ Finset.Ico j H) (t' := Finset.range (n + 1))]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Nat.add_sub_cancel_left]
  · intro d j
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

/-- The cleared kernel sum minus the parts `n < N` of the coefficients of degree less than `H`:
for each `(n, j)` the difference of two initial segments in `i`. -/
private theorem clearedY_sub_head_twsCutoffOne (w : ℕ → RatFunc ℚ) (N H : ℕ) :
    (1 - qParam ^ N) * twsY true w N -
        ∑ d ∈ Finset.range H,
          (∑ n ∈ Finset.range N, twsCoefSummand true w d n) * qParam ^ (N * d) =
      (1 - qParam) * ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1),
        (∑ i ∈ Finset.range (N - n), twsTerm true w n i j * qParam ^ (N * (i + j)) -
          ∑ i ∈ Finset.range (H - j), twsTerm true w n i j * qParam ^ (N * (i + j))) := by
  have h2 : ∑ d ∈ Finset.range H,
      (∑ n ∈ Finset.range N, twsCoefSummand true w d n) * qParam ^ (N * d) =
        (1 - qParam) * ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (H - j), twsTerm true w n i j * qParam ^ (N * (i + j)) := by
    simp only [twsCoefSummand, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [← sum_diagonal_twsCutoffOne
      (fun i j ↦ (1 - qParam) * (twsTerm true w n i j * qParam ^ (N * (i + j)))) H n]
    refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun j hj ↦ ?_
    have hjd : j ≤ d := by
      have := Finset.mem_range.mp hj
      omega
    rw [Nat.sub_add_cancel hjd]
    ring
  rw [tws_clearedY_eq_sum, h2, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]

/-- A tail of a summable family is summable. -/
private theorem twsSummable_shift_twsCutoffOne {s : ℕ → LaurentSeries ℚ} (hs : TwsSummable s)
    (N : ℕ) : TwsSummable fun n ↦ s (n + N) := fun g ↦ by
  obtain ⟨n₀, h⟩ := hs g
  exact ⟨n₀, fun n hn ↦ h (n + N) (le_trans hn (Nat.le_add_right n N))⟩

/-- The order of the head of the remainder: the terms with `n < N`. -/
private theorem le_orderTop_head_twsCutoffOne {w : ℕ → RatFunc ℚ} {C : ℤ}
    (hw : ∀ n : ℕ, w n = 0 ∨ -C ≤ pairQTOrder (w n)) (N H : ℕ) :
    ((4 * (H : ℤ) * N - (C + 10 * (H : ℤ) ^ 2) : ℤ) : WithTop ℤ) ≤
      (twsSeries ((1 - qParam ^ N) * twsY true w N -
        ∑ d ∈ Finset.range H,
          (∑ n ∈ Finset.range N, twsCoefSummand true w d n) * qParam ^ (N * d))).orderTop := by
  rw [clearedY_sub_head_twsCutoffOne, map_mul, HahnSeries.orderTop_mul,
    orderTop_twsSeries_one_sub_qParam_twsCutoffOne, zero_add, map_sum]
  refine le_orderTop_sum_twsCutoffOne _ _ _ fun n hn ↦ ?_
  rw [map_sum]
  refine le_orderTop_sum_twsCutoffOne _ _ _ fun j hj ↦ ?_
  rw [Finset.mem_range] at hn hj
  rw [map_sub, map_sum, map_sum]
  refine le_orderTop_range_sub_range_twsCutoffOne _ _ _ _ fun i hi ↦ ?_
  rw [map_mul, twsSeries_qParam_pow_twsCutoffOne]
  refine le_orderTop_mul_twsT_twsCutoffOne ?_
  have hb := le_orderTop_twsTerm_twsCutoffOne hw N H (n := n) (i := i) (j := j) (by omega)
    (by omega)
  push_cast
  exact hb

/-- The order of the tail `n ≥ N` of the coefficient of degree `d < H`. -/
private theorem le_orderTop_tail_twsCutoffOne {w : ℕ → RatFunc ℚ} {C : ℤ}
    (hw : ∀ n : ℕ, w n = 0 ∨ -C ≤ pairQTOrder (w n)) (N H : ℕ) {d : ℕ} (hd : d < H) :
    ((4 * (H : ℤ) * N - (C + 10 * (H : ℤ) ^ 2) : ℤ) : WithTop ℤ) ≤
      ((twsSum fun n ↦ twsSeries (twsCoefSummand true w d (n + N))) *
        twsT (4 * ((N * d : ℕ) : ℤ))).orderTop := by
  refine le_orderTop_mul_twsT_twsCutoffOne (le_orderTop_twsSum
    (twsSummable_shift_twsCutoffOne (tws_summable_coef_one hw d) N) fun n ↦ ?_)
  rw [twsCoefSummand, map_mul, HahnSeries.orderTop_mul,
    orderTop_twsSeries_one_sub_qParam_twsCutoffOne, zero_add, map_sum]
  refine le_orderTop_sum_twsCutoffOne _ _ _ fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  have hb := le_orderTop_twsTerm_twsCutoffOne hw N H (n := n + N) (i := d - j) (j := j)
    (by omega) (Or.inr (by omega))
  have he : ((d - j : ℕ) : ℤ) + j = d := by omega
  rw [he] at hb
  push_cast
  exact hb

/-- The remainder estimate of Lemma 6.2, `θ = 1`, for a cutoff `H` in the degree of `X`. -/
private theorem le_orderTop_remainder_twsCutoffOne {w : ℕ → RatFunc ℚ} {C : ℤ}
    (hw : ∀ n : ℕ, w n = 0 ∨ -C ≤ pairQTOrder (w n)) (N H : ℕ) :
    ((4 * (H : ℤ) * N - (C + 10 * (H : ℤ) ^ 2) : ℤ) : WithTop ℤ) ≤
      (twsSeries ((1 - qParam ^ N) * twsY true w N) -
        ∑ d ∈ Finset.range H, twsCoef true w d * twsT (4 * ((N * d : ℕ) : ℤ))).orderTop := by
  have hsplit : twsSeries ((1 - qParam ^ N) * twsY true w N) -
      ∑ d ∈ Finset.range H, twsCoef true w d * twsT (4 * ((N * d : ℕ) : ℤ)) =
        twsSeries ((1 - qParam ^ N) * twsY true w N -
          ∑ d ∈ Finset.range H,
            (∑ n ∈ Finset.range N, twsCoefSummand true w d n) * qParam ^ (N * d)) -
        ∑ d ∈ Finset.range H, (twsSum fun n ↦ twsSeries (twsCoefSummand true w d (n + N))) *
          twsT (4 * ((N * d : ℕ) : ℤ)) := by
    rw [map_sub, map_sum, sub_sub, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [twsCoef, twsSum_eq_sum_add (tws_summable_coef_one hw d) N, map_mul, map_sum,
      twsSeries_qParam_pow_twsCutoffOne, add_mul]
  rw [hsplit]
  exact le_trans (le_min (le_orderTop_head_twsCutoffOne hw N H)
    (le_orderTop_sum_twsCutoffOne _ _ _ fun d hd ↦
      le_orderTop_tail_twsCutoffOne hw N H (Finset.mem_range.mp hd)))
    HahnSeries.min_orderTop_le_orderTop_sub

/-- The truncated sum over the `M`-degrees `j < J` is the sum over the `X`-degrees
`d < ⌈J / 2⌉`. -/
private theorem sum_twsCoefM_twsCutoffOne (w : ℕ → RatFunc ℚ) (J : ℤ)
    (x : ℤ → LaurentSeries ℚ) :
    ∑ j ∈ Finset.Ico 0 J, twsCoefM true w j * x j =
      ∑ d ∈ Finset.range ((J + 1) / 2).toNat, twsCoef true w d * x (2 * (d : ℤ)) := by
  symm
  refine Finset.sum_of_injOn (fun d : ℕ ↦ 2 * (d : ℤ)) (fun a _ b _ h ↦ by simpa using h)
    (fun d hd ↦ ?_) (fun j hj hj' ↦ ?_) (fun d _ ↦ ?_)
  · have h := Finset.mem_range.mp hd
    simp only [Finset.coe_Ico, Set.mem_Ico]
    omega
  · rw [Finset.mem_Ico] at hj
    have hne : ¬ (0 ≤ j ∧ 2 ∣ j) := by
      rintro ⟨h0, k, rfl⟩
      refine hj' ⟨k.toNat, ?_, ?_⟩
      · rw [Finset.coe_range, Set.mem_Iio]
        omega
      · simp only
        omega
    rw [twsCoefM, ite_eq_right hne, zero_mul]
  · have hd : (0 : ℤ) ≤ 2 * (d : ℤ) ∧ (2 : ℤ) ∣ 2 * (d : ℤ) := ⟨by omega, dvd_mul_right 2 _⟩
    have he : (2 * (d : ℤ) / 2).toNat = d := by omega
    rw [twsCoefM, ite_eq_left hd, he]

/-- **Lemma 6.2, `θ = 1`.** For an input of order bounded below at `t = 0`, the cleared kernel
sum has the controlled expansion `∑_d A'_d M^(2d)`. -/
theorem tws_ctrl_clearedY_one {w : ℕ → RatFunc ℚ} {C : ℤ}
    (hw : ∀ n : ℕ, w n = 0 ∨ -C ≤ pairQTOrder (w n)) :
    TwsCtrl (twsCoefM true w) fun n ↦ twsSeries (twsClearedY true w n) := by
  refine ⟨0, fun j hj ↦ ?_, fun J ↦ ?_⟩
  · rw [twsCoefM, ite_eq_right (by omega)]
  · refine ⟨C + 10 * (((J + 1) / 2).toNat : ℤ) ^ 2, 0, fun n hn ↦ ?_⟩
    obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have key := le_orderTop_remainder_twsCutoffOne hw N ((J + 1) / 2).toNat
    have hsum : ∑ j ∈ Finset.Ico 0 J, twsCoefM true w j * twsT (2 * (N : ℤ) * j) =
        ∑ d ∈ Finset.range ((J + 1) / 2).toNat,
          twsCoef true w d * twsT (4 * ((N * d : ℕ) : ℤ)) := by
      rw [sum_twsCoefM_twsCutoffOne w J fun j ↦ twsT (2 * (N : ℤ) * j)]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      congr 2
      push_cast
      ring
    rw [hsum]
    simp only [twsClearedY, Int.toNat_natCast]
    refine le_trans (WithTop.coe_le_coe.mpr ?_) key
    have h1 : J ≤ 2 * (((J + 1) / 2).toNat : ℤ) := by omega
    have h2 : (0 : ℤ) ≤ N := Int.natCast_nonneg N
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]

end AJConjecture
