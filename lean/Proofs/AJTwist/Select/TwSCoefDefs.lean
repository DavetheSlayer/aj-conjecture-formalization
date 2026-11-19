import Mathlib
import AJConjecture.QAlgQBinomial
import AJTwist.Select.TwSClaspFinite
import AJTwist.Select.TwSSeriesSum

/-!
# The coefficients of the clasp form

Source: eq. (coefficient-kernel) and Lemma 6.2 (`lem:coefficient-cutoff`) of `selection.tex`
(revision 5). Expanding `(X q^(-i-n); q)_n` by the `q`-binomial theorem,
`(-1)^(θ n) q^(θ n(n+1)/2) w_n (q^(i+1); q)_n (X q^(-i-n); q)_n / (q; q)_n` is
`∑_{j ≤ n} τ(n,i,j) X^j`.

The manuscript expands `(1 - q) / (1 - X)` as a geometric series and calls `A_{θ,d}(w)` the
coefficient of `X^d`. Here the denominator `1 - X` is cleared instead: the sequence is
`(1 - q^N) Y_{θ,N}(w)` and its coefficients are `A'_d = A_d - A_(d-1)`,
`A'_d = (1 - q) ∑_{n} ∑_{j ≤ min(n,d)} τ(n, d-j, j)`. The orders at the special degrees are the
same (the minimal term has geometric degree `e = 0`), and no infinite geometric series occurs;
membership in the saturated classes is not affected by the factor `1 - M⁴`.

* `twsTerm θ w n i j` is `τ(n, i, j)`; its order at `t = 0` is
  `2θ n(n+1) + ord w_n + 2 j (j-1) - 4 j (i + n)` (eq. (coefficient-valuation) in units of `t`).
* `twsClearedY θ w` is the sequence `n ↦ (1 - q^n) Y_{θ,n}(w)` on `ℤ`.
* `twsCoef θ w d` is `A'_d ∈ ℚ((t))`, and `twsCoefM θ w` the coefficient family indexed by the
  `M`-degree (`q^(d N) = M^(2d)`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The coefficient `τ(n, i, j)` of `X^j` in
`(-1)^(θ n) q^(θ n(n+1)/2) w_n (q^(i+1); q)_n (X q^(-i-n); q)_n / (q; q)_n` (`j ≤ n`). -/
def twsTerm (θ : Bool) (w : ℕ → RatFunc ℚ) (n i j : ℕ) : RatFunc ℚ :=
  twsTheta θ n * w n * (qPochhammer (qParam ^ (i + 1)) n / qPochhammer qParam n) *
    ((-1) ^ j * qParam ^ (((j * (j - 1) / 2 : ℕ) : ℤ) - (j : ℤ) * ((i : ℤ) + n)) *
      (qPochhammer qParam n / (qPochhammer qParam j * qPochhammer qParam (n - j))))

/-- The cleared kernel sum `(1 - q^n) Y_{θ,n}(w)` as a sequence on `ℤ`. -/
def twsClearedY (θ : Bool) (w : ℕ → RatFunc ℚ) (n : ℤ) : RatFunc ℚ :=
  (1 - qParam ^ n.toNat) * twsY θ w n.toNat

/-- The part with companion index `n` of the coefficient of `X^d` in the cleared kernel sum. -/
def twsCoefSummand (θ : Bool) (w : ℕ → RatFunc ℚ) (d n : ℕ) : RatFunc ℚ :=
  (1 - qParam) * ∑ j ∈ Finset.range (min n d + 1), twsTerm θ w n (d - j) j

/-- The coefficient `A'_d = (1 - q) ∑_n ∑_{j ≤ min(n,d)} τ(n, d-j, j)` of `X^d` in the cleared
kernel sum, an element of `ℚ((t))`. -/
def twsCoef (θ : Bool) (w : ℕ → RatFunc ℚ) (d : ℕ) : LaurentSeries ℚ :=
  twsSum fun n ↦ twsSeries (twsCoefSummand θ w d n)

/-- The coefficients of the cleared kernel sum indexed by the `M`-degree: `A'_d` at `M^(2d)`. -/
def twsCoefM (θ : Bool) (w : ℕ → RatFunc ℚ) (j : ℤ) : LaurentSeries ℚ :=
  if 0 ≤ j ∧ 2 ∣ j then twsCoef θ w (j / 2).toNat else 0

/-- Twice the triangular number `k(k-1)/2`, as an integer. -/
private theorem two_mul_tri_twsCoefDefs (k : ℕ) :
    2 * ((k * (k - 1) / 2 : ℕ) : ℤ) = (k : ℤ) * ((k : ℤ) - 1) := by
  have h := Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd
  have h' : (2 : ℤ) * ((k * (k - 1) / 2 : ℕ) : ℤ) = ((k * (k - 1) : ℕ) : ℤ) := by
    exact_mod_cast h
  rw [h']
  cases k with
  | zero => simp
  | succ k =>
    push_cast
    simp

/-- The terms `τ(n, i, j) q^(N (i + j))`, `j ≤ n`, add up to the summand of the kernel sum. -/
private theorem sum_twsTerm_mul_twsCoefDefs (θ : Bool) (w : ℕ → RatFunc ℚ) {N n i : ℕ}
    (hi : n + i < N) :
    ∑ j ∈ Finset.range (n + 1), twsTerm θ w n i j * qParam ^ (N * (i + j)) =
      qParam ^ (N * i) * (twsTheta θ n * w n) *
        (qPochhammer (qParam ^ (i + 1)) n * qPochhammer (qParam ^ (N - i - n)) n /
          qPochhammer qParam n) := by
  have hq0 : qParam ≠ 0 := qParam_ne_zero
  have hP : qPochhammer qParam n ≠ 0 := qPochhammer_qParam_ne_zero n
  rw [← sum_qBinomial_eq_qPochhammer n (qParam ^ (N - i - n))]
  have hterm : ∀ j ∈ Finset.range (n + 1), twsTerm θ w n i j * qParam ^ (N * (i + j)) =
      qParam ^ (N * i) * (twsTheta θ n * w n) *
        (qPochhammer (qParam ^ (i + 1)) n / qPochhammer qParam n) *
        ((-1) ^ j * qParam ^ (j * (j - 1) / 2) * (qParam ^ (N - i - n)) ^ j *
          (qPochhammer qParam n / (qPochhammer qParam j * qPochhammer qParam (n - j)))) := by
    intro j _
    have key : qParam ^ (((j * (j - 1) / 2 : ℕ) : ℤ) - (j : ℤ) * ((i : ℤ) + n)) *
        qParam ^ (N * (i + j)) =
          qParam ^ (N * i) * (qParam ^ (j * (j - 1) / 2) * (qParam ^ (N - i - n)) ^ j) := by
      rw [← pow_mul, ← zpow_natCast qParam (N * (i + j)), ← zpow_natCast qParam (N * i),
        ← zpow_natCast qParam (j * (j - 1) / 2), ← zpow_natCast qParam ((N - i - n) * j),
        ← zpow_add₀ hq0, ← zpow_add₀ hq0, ← zpow_add₀ hq0]
      congr 1
      rw [Nat.cast_mul (N - i - n), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [twsTerm]
    linear_combination (twsTheta θ n * w n * (qPochhammer (qParam ^ (i + 1)) n /
      qPochhammer qParam n) * (-1) ^ j * (qPochhammer qParam n /
        (qPochhammer qParam j * qPochhammer qParam (n - j)))) * key
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

/-- The cleared kernel sum as a finite sum of the terms `τ(n, i, j) q^(N (i + j))`. -/
theorem tws_clearedY_eq_sum (θ : Bool) (w : ℕ → RatFunc ℚ) (N : ℕ) :
    (1 - qParam ^ N) * twsY θ w N =
      (1 - qParam) * ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (N - n),
        ∑ j ∈ Finset.range (n + 1), twsTerm θ w n i j * qParam ^ (N * (i + j)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hne : (1 : RatFunc ℚ) - qParam ^ N ≠ 0 := by
    have h := one_sub_qParam_zpow_ne_zero (n := (N : ℤ)) (by omega)
    rwa [zpow_natCast] at h
  rw [twsY, ← mul_assoc, mul_div_cancel₀ _ hne]
  congr 1
  refine Finset.sum_congr rfl fun n hn ↦ Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hn hi
  exact (sum_twsTerm_mul_twsCoefDefs θ w (by omega)).symm

/-- The powers of `-1` are nonzero of order `0`. -/
private theorem pairQTOrder_neg_one_pow_twsCoefDefs (j : ℕ) :
    (-1 : RatFunc ℚ) ^ j ≠ 0 ∧ pairQTOrder ((-1 : RatFunc ℚ) ^ j) = 0 := by
  have h1 : pairQTOrder (1 : RatFunc ℚ) = 0 := by
    have h := pairQTOrder_X_zpow 0
    rwa [zpow_zero] at h
  refine ⟨pow_ne_zero j (neg_ne_zero.mpr one_ne_zero), ?_⟩
  rcases neg_one_pow_eq_or (RatFunc ℚ) j with h | h
  · rw [h, h1]
  · rw [h, pairQTOrder_neg, h1]

/-- The `q`-Pochhammer symbol `(q^(a+1); q)_k` is nonzero of order `0`. -/
private theorem pairQTOrder_qPochhammer_pow_twsCoefDefs (a k : ℕ) :
    qPochhammer (qParam ^ (a + 1)) k ≠ 0 ∧
      pairQTOrder (qPochhammer (qParam ^ (a + 1)) k) = 0 := by
  have h := pairQTOrder_prod_eq (Finset.range k) (fun i ↦ 1 - qParam ^ (a + 1) * qParam ^ i)
    (fun _ ↦ 0) fun i _ ↦ by
      have h1 := pairQTOrder_one_sub_qParam_zpow_of_pos (k := ((a + 1 + i : ℕ) : ℤ)) (by omega)
      rwa [zpow_natCast, pow_add] at h1
  rw [Finset.sum_const_zero] at h
  exact h

/-- The factor `(-1)^(θ n) q^(θ n(n+1)/2)` is nonzero of order `2 θ n(n+1)`. -/
private theorem pairQTOrder_twsTheta_twsCoefDefs (θ : Bool) (n : ℕ) :
    twsTheta θ n ≠ 0 ∧
      pairQTOrder (twsTheta θ n) = if θ then 2 * (n : ℤ) * ((n : ℤ) + 1) else 0 := by
  cases θ
  · simp only [twsTheta, Bool.false_eq_true, ↓reduceIte]
    have h := pairQTOrder_X_zpow 0
    rw [zpow_zero] at h
    exact ⟨one_ne_zero, h⟩
  · simp only [twsTheta, ↓reduceIte]
    have h := pairQTOrder_mul_eq (pairQTOrder_neg_one_pow_twsCoefDefs n)
      (pairQTOrder_qParam_pow_eq (n * (n + 1) / 2))
    refine ⟨h.1, h.2.trans ?_⟩
    have h2 := two_mul_tri_twsCoefDefs (n + 1)
    rw [Nat.add_sub_cancel, mul_comm (n + 1) n, Nat.cast_add, Nat.cast_one] at h2
    linarith

set_option linter.unusedVariables false in
/-- The order at `t = 0` of the term `τ(n, i, j)`. -/
theorem tws_tOrder_twsTerm (θ : Bool) {w : ℕ → RatFunc ℚ} {n : ℕ} (hw : w n ≠ 0) (i : ℕ) {j : ℕ}
    (hj : j ≤ n) :
    twsTerm θ w n i j ≠ 0 ∧ pairQTOrder (twsTerm θ w n i j) =
      (if θ then 2 * (n : ℤ) * ((n : ℤ) + 1) else 0) + pairQTOrder (w n) +
        2 * (j : ℤ) * ((j : ℤ) - 1) - 4 * (j : ℤ) * ((i : ℤ) + n) := by
  have h2 := two_mul_tri_twsCoefDefs j
  have hA := pairQTOrder_mul_eq (pairQTOrder_twsTheta_twsCoefDefs θ n) ⟨hw, rfl⟩
  have hB := pairQTOrder_div_eq (pairQTOrder_qPochhammer_pow_twsCoefDefs i n)
    (pairQTOrder_qPochhammer_qParam n)
  have hC := pairQTOrder_mul_eq (pairQTOrder_neg_one_pow_twsCoefDefs j)
    (pairQTOrder_qParam_zpow_eq (((j * (j - 1) / 2 : ℕ) : ℤ) - (j : ℤ) * ((i : ℤ) + n)))
  have hD := pairQTOrder_div_eq (pairQTOrder_qPochhammer_qParam n)
    (pairQTOrder_mul_eq (pairQTOrder_qPochhammer_qParam j) (pairQTOrder_qPochhammer_qParam (n - j)))
  have h := pairQTOrder_mul_eq (pairQTOrder_mul_eq hA hB) (pairQTOrder_mul_eq hC hD)
  refine ⟨h.1, h.2.trans ?_⟩
  linarith

/-- A finite sum of series of order greater than `g` has order greater than `g`. -/
private theorem lt_orderTop_sum_twsCoefDefs {ι : Type*} (s : Finset ι)
    (f : ι → LaurentSeries ℚ) (g : ℤ) (h : ∀ i ∈ s, (g : WithTop ℤ) < (f i).orderTop) :
    (g : WithTop ℤ) < (∑ i ∈ s, f i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, HahnSeries.orderTop_zero]
    exact WithTop.coe_lt_top g
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_lt_of_le (lt_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))) HahnSeries.min_orderTop_le_orderTop_add

/-- The sum defining `A'_d` converges when the orders of the terms `τ(n, d - j, j)`, `j ≤ d`,
tend to infinity with `n`. -/
private theorem twsSummable_coefSummand_twsCoefDefs (θ : Bool) (w : ℕ → RatFunc ℚ) (d : ℕ)
    (h : ∀ g : ℤ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ j : ℕ, j ≤ n → j ≤ d →
      twsTerm θ w n (d - j) j = 0 ∨ g < pairQTOrder (twsTerm θ w n (d - j) j)) :
    TwsSummable fun n ↦ twsSeries (twsCoefSummand θ w d n) := by
  intro g
  obtain ⟨n₀, hn₀⟩ := h g
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have h1q : (1 - qParam : RatFunc ℚ) ≠ 0 ∧ pairQTOrder (1 - qParam) = 0 := by
    have h := pairQTOrder_one_sub_qParam_zpow_of_pos (k := 1) one_pos
    rwa [zpow_one] at h
  have hlt : (g : WithTop ℤ) < (twsSeries (twsCoefSummand θ w d n)).orderTop := by
    rw [twsCoefSummand, Finset.mul_sum, map_sum]
    refine lt_orderTop_sum_twsCoefDefs _ _ g fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    by_cases h0 : twsTerm θ w n (d - j) j = 0
    · rw [h0, mul_zero, map_zero, HahnSeries.orderTop_zero]
      exact WithTop.coe_lt_top g
    · have hg := (hn₀ n hn j (by omega) (by omega)).resolve_left h0
      have hm := pairQTOrder_mul_eq h1q ⟨h0, rfl⟩
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero ((_root_.map_ne_zero twsSeries).mpr hm.1),
        tws_order_twsSeries hm.1, hm.2, zero_add]
      exact WithTop.coe_lt_coe.mpr hg
  by_cases hz : twsSeries (twsCoefSummand θ w d n) = 0
  · exact Or.inl hz
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hz] at hlt
    exact Or.inr (WithTop.coe_lt_coe.mp hlt)

/-- The order of a term `τ(n, d - j, j)` loses at most `4 d (d + n)` by the `q`-binomial
factor. -/
private theorem twsTerm_exponent_bound_twsCoefDefs {n d j : ℕ} (hjd : j ≤ d) :
    -(4 * (d : ℤ) * ((d : ℤ) + n)) ≤
      2 * (j : ℤ) * ((j : ℤ) - 1) - 4 * (j : ℤ) * (((d - j : ℕ) : ℤ) + n) := by
  have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hjd' : (j : ℤ) ≤ d := by exact_mod_cast hjd
  have h1 : (0 : ℤ) ≤ (j : ℤ) * ((j : ℤ) - 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp
    · exact mul_nonneg hj0 (by omega)
  have h2 : (j : ℤ) * (((d : ℤ) - j) + n) ≤ (d : ℤ) * ((d : ℤ) + n) :=
    mul_le_mul hjd' (by linarith) (by linarith) (by linarith)
  rw [Nat.cast_sub hjd]
  linarith

/-- For `θ = 0` and an input of order at least `4 (n² - B n - C)`, the sum defining `A'_d`
converges. -/
theorem tws_summable_coef_zero {w : ℕ → RatFunc ℚ} {B C : ℤ}
    (hw : ∀ n : ℕ, w n = 0 ∨ 4 * ((n : ℤ) ^ 2 - B * n - C) ≤ pairQTOrder (w n)) (d : ℕ) :
    TwsSummable fun n ↦ twsSeries (twsCoefSummand false w d n) := by
  refine twsSummable_coefSummand_twsCoefDefs false w d fun g ↦ ?_
  refine ⟨(|B| + d + |C| + (d : ℤ) ^ 2 + |g| + 1).toNat, fun n hn j hjn hjd ↦ ?_⟩
  by_cases h0 : w n = 0
  · exact Or.inl (by simp [twsTerm, h0])
  refine Or.inr ?_
  have hord := (hw n).resolve_left h0
  have hn' : |B| + d + |C| + (d : ℤ) ^ 2 + |g| + 1 ≤ n := Int.toNat_le.mp hn
  have hb := twsTerm_exponent_bound_twsCoefDefs (n := n) hjd
  have hB := le_abs_self B
  have hC := le_abs_self C
  have hg := le_abs_self g
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg d
  have hK : (1 : ℤ) ≤ (n : ℤ) - B - d := by
    linarith [abs_nonneg C, abs_nonneg g, sq_nonneg (d : ℤ)]
  have hn1 : (1 : ℤ) ≤ n := by
    linarith [abs_nonneg B, abs_nonneg C, abs_nonneg g, sq_nonneg (d : ℤ)]
  have h3 : (n : ℤ) - B - d ≤ n * ((n : ℤ) - B - d) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hK)]
  rw [(tws_tOrder_twsTerm false h0 (d - j) hjn).2]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  linarith [abs_nonneg g]

/-- For `θ = 1` and an input of order bounded below, the sum defining `A'_d` converges. -/
theorem tws_summable_coef_one {w : ℕ → RatFunc ℚ} {C : ℤ}
    (hw : ∀ n : ℕ, w n = 0 ∨ -C ≤ pairQTOrder (w n)) (d : ℕ) :
    TwsSummable fun n ↦ twsSeries (twsCoefSummand true w d n) := by
  refine twsSummable_coefSummand_twsCoefDefs true w d fun g ↦ ?_
  refine ⟨(2 * (d : ℤ) + |C| + 4 * (d : ℤ) ^ 2 + |g| + 1).toNat, fun n hn j hjn hjd ↦ ?_⟩
  by_cases h0 : w n = 0
  · exact Or.inl (by simp [twsTerm, h0])
  refine Or.inr ?_
  have hord := (hw n).resolve_left h0
  have hn' : 2 * (d : ℤ) + |C| + 4 * (d : ℤ) ^ 2 + |g| + 1 ≤ n := Int.toNat_le.mp hn
  have hb := twsTerm_exponent_bound_twsCoefDefs (n := n) hjd
  have hC := le_abs_self C
  have hg := le_abs_self g
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg d
  have hK : (1 : ℤ) ≤ (n : ℤ) - 2 * d := by
    linarith [abs_nonneg C, abs_nonneg g, sq_nonneg (d : ℤ)]
  have hn1 : (1 : ℤ) ≤ n := by linarith
  have h3 : (n : ℤ) - 2 * d ≤ n * ((n : ℤ) - 2 * d) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hK)]
  rw [(tws_tOrder_twsTerm true h0 (d - j) hjn).2]
  simp only [↓reduceIte]
  linarith [abs_nonneg g]

end AJConjecture
