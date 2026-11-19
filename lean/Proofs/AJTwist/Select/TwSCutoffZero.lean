import Mathlib
import AJTwist.Select.TwSCoefDefs

/-!
# The finite-cutoff estimate, `θ = 0`

Source: Lemma 6.2 (`lem:coefficient-cutoff`) of `selection.tex` (revision 5), case `θ = 0`, in
the cleared form: if `ν(w_n) ≥ n² - B n - C`, then for every `H`
`ν((1 - q^N) Y_{0,N}(w) - ∑_{d < H} A'_d q^(d N)) ≥ H N - O_H(1)`; that is, `twsCoefM false w` is
a controlled expansion of `twsClearedY false w`.

Proof (as in the manuscript, without the geometric degree `e`). By `tws_clearedY_eq_sum` the
remainder is `(1 - q)` times the terms `τ(n,i,j) q^(N(i+j))` with `i + n < N`, `i + j ≥ H`
(high degrees on the finite triangle), minus the terms with `i + j < H`, `i + n ≥ N` (omitted
outside the triangle; an infinite convergent sum). The order of `τ(n,i,j) q^(N(i+j))` is at least
`i (N - j) + j (N - n) + j (j-1)/2 + n² - B n - C` (in units of `q`): for `j ≥ H` this is
`≥ H (N - n) + n² - B n - C`; for `j < H`, `i ≥ H - j` gives `≥ H N - H² - H n + n² - B n - C`.
Outside the triangle, `n ≥ N - H + 1` and the order before evaluation is
`≥ n² - (B + H) n - C - H²`. All are `≥ H N - O_H(1)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A finite sum of series of order at least `g` has order at least `g`. -/
private theorem le_orderTop_sum_cutoffZero {ι : Type*} (s : Finset ι)
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

/-- A lower bound for the order at `t = 0` is one for the order of the expansion. -/
private theorem le_orderTop_twsSeries_cutoffZero {x : RatFunc ℚ} {b : ℤ}
    (h : x = 0 ∨ b ≤ pairQTOrder x) : (b : WithTop ℤ) ≤ (twsSeries x).orderTop := by
  by_cases h0 : x = 0
  · rw [h0, map_zero, HahnSeries.orderTop_zero]
    exact le_top
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero twsSeries).mpr h0),
    tws_order_twsSeries h0]
  exact WithTop.coe_le_coe.mpr (h.resolve_left h0)

/-- Multiplication by `1 - q` does not lower the order of the expansion. -/
private theorem le_orderTop_one_sub_mul_cutoffZero {x : RatFunc ℚ} {b : WithTop ℤ}
    (h : b ≤ (twsSeries x).orderTop) : b ≤ (twsSeries ((1 - qParam) * x)).orderTop := by
  have h1q : (1 - qParam : RatFunc ℚ) ≠ 0 ∧ pairQTOrder (1 - qParam) = 0 := by
    have h := pairQTOrder_one_sub_qParam_zpow_of_pos (k := 1) one_pos
    rwa [zpow_one] at h
  rw [map_mul, HahnSeries.orderTop_mul,
    ← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero twsSeries).mpr h1q.1),
    tws_order_twsSeries h1q.1, h1q.2, WithTop.coe_zero, zero_add]
  exact h

/-- The expansion of `q^k` is `t^(4k)`. -/
private theorem twsSeries_qParam_pow_cutoffZero (k : ℕ) :
    twsSeries (qParam ^ k) = twsT (4 * (k : ℤ)) := by
  rw [qParam, ← pow_mul, ← zpow_natCast, twsSeries_X_zpow]
  push_cast
  rfl

/-- A tail of a summable family is summable. -/
private theorem twsSummable_shift_cutoffZero {s : ℕ → LaurentSeries ℚ} (hs : TwsSummable s)
    (N : ℕ) : TwsSummable fun n ↦ s (n + N) := fun g ↦ by
  obtain ⟨n₀, h⟩ := hs g
  exact ⟨n₀, fun n hn ↦ h (n + N) (le_trans hn (Nat.le_add_right n N))⟩

/-- A lower bound for the order of the term `τ(n, i, j)`, `θ = 0`. -/
private theorem tOrder_twsTerm_cutoffZero {w : ℕ → RatFunc ℚ} {B C : ℤ}
    (hw : ∀ n : ℕ, w n = 0 ∨ 4 * ((n : ℤ) ^ 2 - B * n - C) ≤ pairQTOrder (w n)) (n i : ℕ)
    {j : ℕ} (hj : j ≤ n) (m : ℕ) :
    twsTerm false w n i j * qParam ^ m = 0 ∨
      4 * ((n : ℤ) ^ 2 - B * n - C) + 2 * (j : ℤ) * ((j : ℤ) - 1) -
        4 * (j : ℤ) * ((i : ℤ) + n) + 4 * (m : ℤ) ≤
          pairQTOrder (twsTerm false w n i j * qParam ^ m) := by
  by_cases h0 : w n = 0
  · exact Or.inl (by simp [twsTerm, h0])
  refine Or.inr ?_
  have h := pairQTOrder_mul_eq (tws_tOrder_twsTerm false h0 i hj) (pairQTOrder_qParam_pow_eq m)
  rw [h.2]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  linarith [(hw n).resolve_left h0]

/-- The order estimate on the finite triangle: for `i + n < N`, `j ≤ n`, and either `i + j ≥ H`
(high degree) or `n ≥ N - H` (large companion index), the term `τ(n,i,j) q^(N (i+j))` has order
at least `4 (H N - K)`. -/
private theorem triangle_ineq_cutoffZero {n i j N H : ℕ} (B C : ℤ) (hj : j ≤ n) (hi : n + i < N)
    (h : N ≤ n + H ∨ H ≤ i + j) :
    4 * ((H : ℤ) * N - ((B + H) ^ 2 + (B + 2 * H) ^ 2 + 2 * (H : ℤ) ^ 2 + C)) ≤
      4 * ((n : ℤ) ^ 2 - B * n - C) + 2 * (j : ℤ) * ((j : ℤ) - 1) -
        4 * (j : ℤ) * ((i : ℤ) + n) + 4 * ((N * (i + j) : ℕ) : ℤ) := by
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hi0 : (0 : ℤ) ≤ i := Int.natCast_nonneg i
  have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
  have hH0 : (0 : ℤ) ≤ H := Int.natCast_nonneg H
  have hjn : (j : ℤ) ≤ n := by exact_mod_cast hj
  have hiN : (n : ℤ) + i + 1 ≤ N := by exact_mod_cast hi
  have h1 : (0 : ℤ) ≤ (j : ℤ) * ((j : ℤ) - 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp
    · exact mul_nonneg hj0 (by omega)
  have h2 : (0 : ℤ) ≤ (i : ℤ) * ((N : ℤ) - j) := mul_nonneg hi0 (by linarith)
  have h3 : (0 : ℤ) ≤ (j : ℤ) * ((N : ℤ) - n) := mul_nonneg hj0 (by linarith)
  have h4 : (0 : ℤ) ≤ (2 * (n : ℤ) - (B + H)) ^ 2 + 3 * (B + H) ^ 2 := by positivity
  have h5 := sq_nonneg (B + 2 * (H : ℤ))
  have h6 := sq_nonneg (H : ℤ)
  push_cast
  rcases h with h | h
  · have h7 : (N : ℤ) ≤ n + H := by exact_mod_cast h
    have h8 : (0 : ℤ) ≤ (H : ℤ) * ((n : ℤ) + H - N) := mul_nonneg hH0 (by linarith)
    nlinarith
  · have h7 : (H : ℤ) ≤ i + j := by exact_mod_cast h
    rcases le_or_gt (H : ℤ) j with hHj | hHj
    · have h8 : (0 : ℤ) ≤ ((j : ℤ) - H) * ((N : ℤ) - n) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    · have h8 : (0 : ℤ) ≤ ((i : ℤ) - (H - j)) * ((N : ℤ) - j) :=
        mul_nonneg (by linarith) (by linarith)
      have h9 : (0 : ℤ) ≤ (H : ℤ) * ((H : ℤ) - j) := mul_nonneg hH0 (by linarith)
      have h10 : (0 : ℤ) ≤ (n : ℤ) * ((H : ℤ) - j) := mul_nonneg hn0 (by linarith)
      have h11 := sq_nonneg (j : ℤ)
      nlinarith

/-- The order estimate outside the triangle: for `d < H`, `j ≤ min(n, d)` and `n ≥ N - H`, the
term `τ(n, d - j, j) q^(N d)` has order at least `4 (H N - K)`. -/
private theorem tail_ineq_cutoffZero {n j d N H : ℕ} (B C : ℤ) (hjn : j ≤ n) (hjd : j ≤ d)
    (hd : d < H) (h : N ≤ n + H) :
    4 * ((H : ℤ) * N - ((B + H) ^ 2 + (B + 2 * H) ^ 2 + 2 * (H : ℤ) ^ 2 + C)) -
        4 * ((N : ℤ) * d) ≤
      4 * ((n : ℤ) ^ 2 - B * n - C) + 2 * (j : ℤ) * ((j : ℤ) - 1) -
        4 * (j : ℤ) * (((d - j : ℕ) : ℤ) + n) + 4 * ((0 : ℕ) : ℤ) := by
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg d
  have hN0 : (0 : ℤ) ≤ N := Int.natCast_nonneg N
  have hH0 : (0 : ℤ) ≤ H := Int.natCast_nonneg H
  have hjd' : (j : ℤ) ≤ d := by exact_mod_cast hjd
  have hd' : (d : ℤ) + 1 ≤ H := by exact_mod_cast hd
  have hN : (N : ℤ) ≤ n + H := by exact_mod_cast h
  have h1 : (0 : ℤ) ≤ (j : ℤ) * ((j : ℤ) - 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp
    · exact mul_nonneg hj0 (by omega)
  have h2 : (0 : ℤ) ≤ (N : ℤ) * d := mul_nonneg hN0 hd0
  have h3 : (0 : ℤ) ≤ (H : ℤ) * ((n : ℤ) + H - N) := mul_nonneg hH0 (by linarith)
  have h4 : (0 : ℤ) ≤ (n : ℤ) * ((H : ℤ) - j) := mul_nonneg hn0 (by linarith)
  have h5 : (0 : ℤ) ≤ ((H : ℤ) - j) * H := mul_nonneg (by linarith) hH0
  have h6 : (0 : ℤ) ≤ (j : ℤ) * ((H : ℤ) - d) := mul_nonneg hj0 (by linarith)
  have h7 : (0 : ℤ) ≤ (2 * (n : ℤ) - (B + 2 * H)) ^ 2 + 3 * (B + 2 * H) ^ 2 := by positivity
  have h8 := sq_nonneg (B + (H : ℤ))
  have h9 := sq_nonneg (j : ℤ)
  rw [Nat.cast_sub hjd]
  push_cast
  nlinarith

/-- Shifting a truncated sum: the terms `d ≥ j` of `∑_{d < H} f (d - j)`. -/
private theorem sum_range_ite_le_cutoffZero {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (H j : ℕ) :
    ∑ d ∈ Finset.range H, (if j ≤ d then f (d - j) else 0) =
      ∑ i ∈ Finset.range (H - j), f i := by
  rcases le_or_gt j H with h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Finset.sum_range_add, Nat.add_sub_cancel_left, Finset.sum_eq_zero, zero_add]
    · exact Finset.sum_congr rfl fun x _ ↦ by
        rw [ite_eq_left (Nat.le_add_right j x), Nat.add_sub_cancel_left]
    · intro x hx
      rw [ite_eq_right (not_le.mpr (Finset.mem_range.mp hx))]
  · rw [Nat.sub_eq_zero_of_le h.le, Finset.range_zero, Finset.sum_empty]
    refine Finset.sum_eq_zero fun d hd ↦ ite_eq_right ?_
    have := Finset.mem_range.mp hd
    omega

/-- The terms `i + j < H` of a sum over a range containing them. -/
private theorem sum_range_ite_lt_cutoffZero {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {H j K : ℕ} (h : H - j ≤ K) :
    ∑ i ∈ Finset.range K, (if i + j < H then f i else 0) =
      ∑ i ∈ Finset.range (H - j), f i := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The terms of degree `d = i + j < H`, summed by degree or by `(i, j)`. -/
private theorem sum_degree_lt_cutoffZero {M : Type*} [AddCommMonoid M] (g : ℕ → ℕ → M)
    {H K : ℕ} (n : ℕ) (h : H ≤ K) :
    ∑ d ∈ Finset.range H, ∑ j ∈ Finset.range (min n d + 1), g (d - j) j =
      ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range (n + 1), if i + j < H then g i j else 0 := by
  have h1 : ∀ d : ℕ, ∑ j ∈ Finset.range (min n d + 1), g (d - j) j =
      ∑ j ∈ Finset.range (n + 1), if j ≤ d then g (d - j) j else 0 := by
    intro d
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp only [h1]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range K)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [sum_range_ite_le_cutoffZero (fun i ↦ g i j),
    sum_range_ite_lt_cutoffZero (fun i ↦ g i j) (by omega)]

/-- The parts with companion index `n < N - H` of the coefficients of degree `d < H`, evaluated
at `X = q^N`, are the terms `i + j < H`, `n < N - H` of the finite triangle. -/
private theorem sum_coefSummand_eq_cutoffZero (w : ℕ → RatFunc ℚ) {N H : ℕ} (hH : H ≤ N) :
    ∑ d ∈ Finset.range H, qParam ^ (N * d) *
        ∑ n ∈ Finset.range (N - H), twsCoefSummand false w d n =
      (1 - qParam) * ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        ∑ j ∈ Finset.range (n + 1),
          if n + H < N ∧ i + j < H then twsTerm false w n i j * qParam ^ (N * (i + j))
          else 0 := by
  have hterm : ∀ d : ℕ, qParam ^ (N * d) *
      ∑ n ∈ Finset.range (N - H), twsCoefSummand false w d n =
        (1 - qParam) * ∑ n ∈ Finset.range (N - H), ∑ j ∈ Finset.range (min n d + 1),
          twsTerm false w n (d - j) j * qParam ^ (N * (d - j + j)) := by
    intro d
    simp only [twsCoefSummand]
    rw [← Finset.mul_sum, mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjd : d - j + j = d := by
      have := Finset.mem_range.mp hj
      omega
    rw [hjd, mul_comm]
  simp only [hterm]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine (Finset.sum_congr rfl fun n hn ↦ ?_).trans
    (Finset.sum_subset (Finset.range_subset_range.mpr (Nat.sub_le N H)) fun n _ hn ↦ ?_)
  · have hn' : n + H < N := by
      have := Finset.mem_range.mp hn
      omega
    rw [sum_degree_lt_cutoffZero
      (fun i j ↦ twsTerm false w n i j * qParam ^ (N * (i + j))) n (K := N - n) (by omega)]
    simp only [hn', true_and]
  · have hn' : ¬ n + H < N := by
      rw [Finset.mem_range] at hn
      omega
    simp only [hn', false_and, ↓reduceIte, Finset.sum_const_zero]

/-- The remainder of the cleared kernel sum after subtracting the terms of degree `< H`, as the
high part of the finite triangle minus the tails of the coefficients. -/
private theorem remainder_eq_cutoffZero {w : ℕ → RatFunc ℚ} {B C : ℤ}
    (hw : ∀ n : ℕ, w n = 0 ∨ 4 * ((n : ℤ) ^ 2 - B * n - C) ≤ pairQTOrder (w n)) {N H : ℕ}
    (hH : H ≤ N) :
    twsSeries ((1 - qParam ^ N) * twsY false w N) -
        ∑ d ∈ Finset.range H, twsCoef false w d * twsT (4 * (N : ℤ) * d) =
      twsSeries ((1 - qParam) * ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        ∑ j ∈ Finset.range (n + 1),
          if n + H < N ∧ i + j < H then 0
          else twsTerm false w n i j * qParam ^ (N * (i + j))) -
      ∑ d ∈ Finset.range H, twsT (4 * (N : ℤ) * d) *
        twsSum fun n ↦ twsSeries (twsCoefSummand false w d (n + (N - H))) := by
  have hsplit : ∀ d : ℕ, twsCoef false w d =
      ∑ n ∈ Finset.range (N - H), twsSeries (twsCoefSummand false w d n) +
        twsSum fun n ↦ twsSeries (twsCoefSummand false w d (n + (N - H))) :=
    fun d ↦ twsSum_eq_sum_add (tws_summable_coef_zero hw d) (N - H)
  have hA : ∑ d ∈ Finset.range H,
      (∑ n ∈ Finset.range (N - H), twsSeries (twsCoefSummand false w d n)) *
        twsT (4 * (N : ℤ) * d) =
      twsSeries ((1 - qParam) * ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        ∑ j ∈ Finset.range (n + 1),
          if n + H < N ∧ i + j < H then twsTerm false w n i j * qParam ^ (N * (i + j))
          else 0) := by
    rw [← sum_coefSummand_eq_cutoffZero w hH, map_sum]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [map_mul, map_sum, twsSeries_qParam_pow_cutoffZero, mul_comm, Nat.cast_mul, mul_assoc]
  have hsum : (1 - qParam) * ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
      ∑ j ∈ Finset.range (n + 1), twsTerm false w n i j * qParam ^ (N * (i + j)) =
      (1 - qParam) * (∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        ∑ j ∈ Finset.range (n + 1),
          if n + H < N ∧ i + j < H then twsTerm false w n i j * qParam ^ (N * (i + j))
          else 0) +
      (1 - qParam) * ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        ∑ j ∈ Finset.range (n + 1),
          if n + H < N ∧ i + j < H then 0
          else twsTerm false w n i j * qParam ^ (N * (i + j)) := by
    rw [← mul_add]
    simp only [← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ ↦ Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs
    · rw [add_zero]
    · rw [zero_add]
  rw [tws_clearedY_eq_sum, hsum, map_add, ← hA]
  simp only [hsplit, add_mul, Finset.sum_add_distrib]
  rw [add_sub_add_left_eq_sub]
  congr 1
  exact Finset.sum_congr rfl fun d _ ↦ mul_comm _ _

/-- The remainder estimate of Lemma 6.2 (`θ = 0`) on natural colours `N ≥ H`. -/
private theorem le_orderTop_remainder_cutoffZero {w : ℕ → RatFunc ℚ} {B C : ℤ}
    (hw : ∀ n : ℕ, w n = 0 ∨ 4 * ((n : ℤ) ^ 2 - B * n - C) ≤ pairQTOrder (w n)) {N H : ℕ}
    (hH : H ≤ N) :
    ((4 * ((H : ℤ) * N - ((B + H) ^ 2 + (B + 2 * H) ^ 2 + 2 * (H : ℤ) ^ 2 + C)) : ℤ) :
        WithTop ℤ) ≤
      (twsSeries ((1 - qParam ^ N) * twsY false w N) -
        ∑ d ∈ Finset.range H, twsCoef false w d * twsT (4 * (N : ℤ) * d)).orderTop := by
  rw [remainder_eq_cutoffZero hw hH]
  refine le_trans (le_min ?_ ?_) HahnSeries.min_orderTop_le_orderTop_sub
  · refine le_orderTop_one_sub_mul_cutoffZero ?_
    simp only [map_sum]
    refine le_orderTop_sum_cutoffZero _ _ _ fun n hn ↦ le_orderTop_sum_cutoffZero _ _ _
      fun i hi ↦ le_orderTop_sum_cutoffZero _ _ _ fun j hj ↦ ?_
    rw [Finset.mem_range] at hn hi hj
    split_ifs with hc
    · rw [map_zero, HahnSeries.orderTop_zero]
      exact le_top
    · refine le_orderTop_twsSeries_cutoffZero
        ((tOrder_twsTerm_cutoffZero hw n i (by omega) (N * (i + j))).imp_right fun h ↦
          le_trans (triangle_ineq_cutoffZero B C (by omega) (by omega) ?_) h)
      rw [not_and_or, not_lt, not_lt] at hc
      exact hc
  · refine le_orderTop_sum_cutoffZero _ _ _ fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    have hb : (4 * ((H : ℤ) * N - ((B + H) ^ 2 + (B + 2 * H) ^ 2 + 2 * (H : ℤ) ^ 2 + C)) : ℤ) =
        4 * (N : ℤ) * d + (4 * ((H : ℤ) * N -
          ((B + H) ^ 2 + (B + 2 * H) ^ 2 + 2 * (H : ℤ) ^ 2 + C)) - 4 * ((N : ℤ) * d)) := by
      ring
    rw [hb, WithTop.coe_add, HahnSeries.orderTop_mul, twsT,
      HahnSeries.orderTop_single one_ne_zero]
    refine add_le_add le_rfl (le_orderTop_twsSum
      (twsSummable_shift_cutoffZero (tws_summable_coef_zero hw d) (N - H)) fun n ↦ ?_)
    rw [twsCoefSummand]
    refine le_orderTop_one_sub_mul_cutoffZero ?_
    rw [map_sum]
    refine le_orderTop_sum_cutoffZero _ _ _ fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    have h := tOrder_twsTerm_cutoffZero hw (n + (N - H)) (d - j) (j := j) (by omega) 0
    rw [pow_zero, mul_one] at h
    exact le_orderTop_twsSeries_cutoffZero (h.imp_right fun h ↦
      le_trans (tail_ineq_cutoffZero B C (by omega) (by omega) hd (by omega)) h)

/-- The truncated sums of the expansion indexed by the `M`-degree are those indexed by the
degree in `X = q^N`. -/
private theorem sum_twsCoefM_cutoffZero (w : ℕ → RatFunc ℚ) (J : ℤ) (N : ℕ) :
    ∑ j ∈ Finset.Ico 0 J, twsCoefM false w j * twsT (2 * (N : ℤ) * j) =
      ∑ d ∈ Finset.range ((J + 1) / 2).toNat, twsCoef false w d * twsT (4 * (N : ℤ) * d) := by
  have himg : ∑ d ∈ Finset.range ((J + 1) / 2).toNat, twsCoef false w d * twsT (4 * (N : ℤ) * d) =
      ∑ j ∈ (Finset.range ((J + 1) / 2).toNat).image (fun d : ℕ ↦ 2 * (d : ℤ)),
        twsCoefM false w j * twsT (2 * (N : ℤ) * j) := by
    rw [Finset.sum_image fun a _ b _ h ↦ by lia]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    have h1 : (2 * (d : ℤ) / 2).toNat = d := by lia
    have h2 : 2 * (N : ℤ) * (2 * (d : ℤ)) = 4 * (N : ℤ) * d := by ring
    rw [twsCoefM, ite_eq_left ⟨by lia, dvd_mul_right 2 _⟩, h1, h2]
  rw [himg]
  symm
  refine Finset.sum_subset (fun j hj ↦ ?_) fun j hj hj' ↦ ?_
  · rw [Finset.mem_image] at hj
    obtain ⟨d, hd, rfl⟩ := hj
    rw [Finset.mem_range] at hd
    rw [Finset.mem_Ico]
    lia
  · rw [Finset.mem_Ico] at hj
    rw [twsCoefM]
    by_cases hc : 0 ≤ j ∧ 2 ∣ j
    · refine absurd (Finset.mem_image.mpr ⟨(j / 2).toNat, ?_, ?_⟩) hj'
      · rw [Finset.mem_range]
        lia
      · lia
    · rw [ite_eq_right hc, zero_mul]

/-- **Lemma 6.2, `θ = 0`.** For an input of order at least `4 (n² - B n - C)` at `t = 0`, the
cleared kernel sum has the controlled expansion `∑_d A'_d M^(2d)`. -/
theorem tws_ctrl_clearedY_zero {w : ℕ → RatFunc ℚ} {B C : ℤ}
    (hw : ∀ n : ℕ, w n = 0 ∨ 4 * ((n : ℤ) ^ 2 - B * n - C) ≤ pairQTOrder (w n)) :
    TwsCtrl (twsCoefM false w) fun n ↦ twsSeries (twsClearedY false w n) := by
  refine ⟨0, fun j hj ↦ ?_, fun J ↦ ?_⟩
  · rw [twsCoefM, ite_eq_right (by lia)]
  obtain ⟨H, hH⟩ : ∃ H : ℕ, H = ((J + 1) / 2).toNat := ⟨_, rfl⟩
  refine ⟨4 * ((B + H) ^ 2 + (B + 2 * H) ^ 2 + 2 * (H : ℤ) ^ 2 + C), H, fun n hn ↦ ?_⟩
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (Int.natCast_nonneg H) hn)
  beta_reduce
  rw [sum_twsCoefM_cutoffZero, twsClearedY, Int.toNat_natCast, ← hH]
  refine le_trans (WithTop.coe_le_coe.mpr ?_)
    (le_orderTop_remainder_cutoffZero hw (by exact_mod_cast hn))
  have h1 : J ≤ 2 * (H : ℤ) := by lia
  have h2 : (0 : ℤ) ≤ (2 * (H : ℤ) - J) * N := mul_nonneg (by linarith) (Int.natCast_nonneg N)
  linarith

end AJConjecture
