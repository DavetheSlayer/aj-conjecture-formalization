import Mathlib
import AJTwist.Select.TwSClaspFinite
import AJTwist.Select.TwSInput
import AJTwist.Select.TwSCtrlDefs

/-!
# The leading term of the reduced sequence at `a = 0`, right-handed companion

Source: Section 6.5 of `selection.tex` (revision 5): at `a = 0` (`ℓ = r s`) the input is
`v_n = V_n(q)`, of order `0` with leading coefficient `1`. In the clasp form
`F_N = q^(N-1) Y_{0,N}(V)` every summand with `i = 0` has order `0` and leading coefficient `1`
(at `X = q^N` all Pochhammer exponents in the finite support are positive), and the summands
with `i > 0` have larger order. Hence `ν(F_N) = N - 1` and the leading coefficient of `F_N` is
`N`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `f = c + O(t)` at `t = 0`: the expansion of `f` minus the constant `c` has positive
order. -/
private def TwsRegAtLeadZero (f : RatFunc ℚ) (c : ℚ) : Prop :=
  (0 : WithTop ℤ) < (twsSeries f - HahnSeries.C c).orderTop

/-- A constant has nonnegative order. -/
private theorem zero_le_orderTop_C_leadZero (c : ℚ) :
    (0 : WithTop ℤ) ≤ (HahnSeries.C c : LaurentSeries ℚ).orderTop := by
  rw [HahnSeries.C_apply]
  exact HahnSeries.orderTop_single_le

/-- A function regular at `t = 0` has an expansion of nonnegative order. -/
private theorem zero_le_orderTop_of_regAt_leadZero {f : RatFunc ℚ} {c : ℚ}
    (h : TwsRegAtLeadZero f c) : (0 : WithTop ℤ) ≤ (twsSeries f).orderTop := by
  have h1 := HahnSeries.min_orderTop_le_orderTop_add (x := twsSeries f - HahnSeries.C c)
    (y := HahnSeries.C c)
  rw [sub_add_cancel] at h1
  exact le_trans (le_min h.le (zero_le_orderTop_C_leadZero c)) h1

/-- The zero function has the value `0` at `t = 0`. -/
private theorem regAt_zero_leadZero : TwsRegAtLeadZero 0 0 := by
  rw [TwsRegAtLeadZero, map_zero, map_zero, sub_zero, HahnSeries.orderTop_zero]
  exact WithTop.top_pos

/-- The constant `1` has the value `1` at `t = 0`. -/
private theorem regAt_one_leadZero : TwsRegAtLeadZero 1 1 := by
  rw [TwsRegAtLeadZero, map_one, map_one, sub_self, HahnSeries.orderTop_zero]
  exact WithTop.top_pos

/-- A nonzero function of positive order has the value `0` at `t = 0`. -/
private theorem regAt_of_pos_leadZero {f : RatFunc ℚ} (hf : f ≠ 0 ∧ 0 < pairQTOrder f) :
    TwsRegAtLeadZero f 0 := by
  rw [TwsRegAtLeadZero, map_zero, sub_zero,
    ← HahnSeries.order_eq_orderTop_of_ne_zero ((_root_.map_ne_zero twsSeries).mpr hf.1),
    tws_order_twsSeries hf.1]
  exact WithTop.coe_pos.mpr hf.2

/-- Values at `t = 0` add. -/
private theorem regAt_add_leadZero {f g : RatFunc ℚ} {a b : ℚ} (hf : TwsRegAtLeadZero f a)
    (hg : TwsRegAtLeadZero g b) : TwsRegAtLeadZero (f + g) (a + b) := by
  rw [TwsRegAtLeadZero, map_add, map_add, add_sub_add_comm]
  exact lt_of_lt_of_le (lt_min hf hg) HahnSeries.min_orderTop_le_orderTop_add

/-- Values at `t = 0` subtract. -/
private theorem regAt_sub_leadZero {f g : RatFunc ℚ} {a b : ℚ} (hf : TwsRegAtLeadZero f a)
    (hg : TwsRegAtLeadZero g b) : TwsRegAtLeadZero (f - g) (a - b) := by
  rw [TwsRegAtLeadZero, map_sub, map_sub, sub_sub_sub_comm]
  exact lt_of_lt_of_le (lt_min hf hg) HahnSeries.min_orderTop_le_orderTop_sub

/-- Values at `t = 0` multiply. -/
private theorem regAt_mul_leadZero {f g : RatFunc ℚ} {a b : ℚ} (hf : TwsRegAtLeadZero f a)
    (hg : TwsRegAtLeadZero g b) : TwsRegAtLeadZero (f * g) (a * b) := by
  have heq : twsSeries (f * g) - HahnSeries.C (a * b) =
      (twsSeries f - HahnSeries.C a) * twsSeries g +
        HahnSeries.C a * (twsSeries g - HahnSeries.C b) := by
    rw [map_mul, map_mul]
    ring
  rw [TwsRegAtLeadZero, heq]
  refine lt_of_lt_of_le (lt_min ?_ ?_) HahnSeries.min_orderTop_le_orderTop_add
  · rw [HahnSeries.orderTop_mul]
    exact lt_of_lt_of_le hf (le_add_of_nonneg_right (zero_le_orderTop_of_regAt_leadZero hg))
  · rw [HahnSeries.orderTop_mul]
    exact lt_of_lt_of_le hg (le_add_of_nonneg_left (zero_le_orderTop_C_leadZero a))

/-- A function with nonzero value at `t = 0` is nonzero of order `0`, and its leading
coefficient is the value. -/
private theorem lead_of_regAt_leadZero {f : RatFunc ℚ} {c : ℚ} (h : TwsRegAtLeadZero f c)
    (hc : c ≠ 0) :
    f ≠ 0 ∧ (twsSeries f).orderTop = 0 ∧ pairQTOrder f = 0 ∧
      (twsSeries f).leadingCoeff = c := by
  have hCc : (HahnSeries.C c : LaurentSeries ℚ).orderTop = 0 := by
    rw [HahnSeries.C_apply, HahnSeries.orderTop_single hc]
    rfl
  have hlt : (HahnSeries.C c : LaurentSeries ℚ).orderTop <
      (twsSeries f - HahnSeries.C c).orderTop := by
    rw [hCc]
    exact h
  have ho := HahnSeries.orderTop_add_eq_left hlt
  have hl := HahnSeries.leadingCoeff_add_eq_left hlt
  rw [add_sub_cancel] at ho hl
  rw [hCc] at ho
  rw [HahnSeries.C_apply, HahnSeries.leadingCoeff_of_single] at hl
  have hx0 : twsSeries f ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp (by rw [ho]; exact WithTop.zero_ne_top)
  have hf0 : f ≠ 0 := fun h0 ↦ hx0 (by rw [h0, map_zero])
  refine ⟨hf0, ho, ?_, hl⟩
  rw [← tws_order_twsSeries hf0, ← WithTop.coe_eq_zero,
    HahnSeries.order_eq_orderTop_of_ne_zero hx0, ho]

/-- Values at `t = 0` are inverted. -/
private theorem regAt_inv_leadZero {g : RatFunc ℚ} {b : ℚ} (hg : TwsRegAtLeadZero g b)
    (hb : b ≠ 0) : TwsRegAtLeadZero g⁻¹ b⁻¹ := by
  obtain ⟨hg0, hx, -, -⟩ := lead_of_regAt_leadZero hg hb
  have hx0 : twsSeries g ≠ 0 := (_root_.map_ne_zero twsSeries).mpr hg0
  have heq : (twsSeries g⁻¹ - HahnSeries.C b⁻¹) * twsSeries g =
      -(HahnSeries.C b⁻¹ * (twsSeries g - HahnSeries.C b)) := by
    have h1 : (HahnSeries.C b⁻¹ : LaurentSeries ℚ) * HahnSeries.C b = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hb, map_one]
    rw [map_inv₀, sub_mul, inv_mul_cancel₀ hx0]
    linear_combination -h1
  have h2 := congrArg HahnSeries.orderTop heq
  rw [HahnSeries.orderTop_mul, hx, add_zero, HahnSeries.orderTop_neg,
    HahnSeries.orderTop_mul] at h2
  rw [TwsRegAtLeadZero, h2]
  exact lt_of_lt_of_le hg (le_add_of_nonneg_left (zero_le_orderTop_C_leadZero b⁻¹))

/-- Values at `t = 0` divide. -/
private theorem regAt_div_leadZero {f g : RatFunc ℚ} {a b : ℚ} (hf : TwsRegAtLeadZero f a)
    (hg : TwsRegAtLeadZero g b) (hb : b ≠ 0) : TwsRegAtLeadZero (f / g) (a / b) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact regAt_mul_leadZero hf (regAt_inv_leadZero hg hb)

/-- Values at `t = 0` of finite sums. -/
private theorem regAt_sum_leadZero {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℚ) (c : ι → ℚ)
    (h : ∀ i ∈ s, TwsRegAtLeadZero (f i) (c i)) :
    TwsRegAtLeadZero (∑ i ∈ s, f i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact regAt_zero_leadZero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact regAt_add_leadZero (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- A finite product of functions with value `1` at `t = 0` has value `1`. -/
private theorem regAt_prod_one_leadZero {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℚ)
    (h : ∀ i ∈ s, TwsRegAtLeadZero (f i) 1) : TwsRegAtLeadZero (∏ i ∈ s, f i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact regAt_one_leadZero
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← one_mul (1 : ℚ)]
    exact regAt_mul_leadZero (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- The value at `t = 0` of a power of `q`. -/
private theorem regAt_qParam_pow_leadZero (k : ℕ) :
    TwsRegAtLeadZero (qParam ^ k) (if k = 0 then 1 else 0) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, ite_eq_left rfl]
    exact regAt_one_leadZero
  · rw [ite_eq_right hk.ne']
    have h := pairQTOrder_qParam_pow_eq k
    exact regAt_of_pos_leadZero ⟨h.1, by rw [h.2]; omega⟩

/-- `1 - q^(k+1)` has the value `1` at `t = 0`. -/
private theorem regAt_one_sub_qParam_pow_leadZero (k : ℕ) :
    TwsRegAtLeadZero (1 - qParam ^ (k + 1)) 1 := by
  have h := regAt_sub_leadZero regAt_one_leadZero (regAt_qParam_pow_leadZero (k + 1))
  rwa [ite_eq_right (Nat.succ_ne_zero k), sub_zero] at h

/-- `(q^(a+1); q)_n` has the value `1` at `t = 0`. -/
private theorem regAt_qPochhammer_leadZero (a n : ℕ) :
    TwsRegAtLeadZero (qPochhammer (qParam ^ (a + 1)) n) 1 := by
  refine regAt_prod_one_leadZero _ _ fun i _ ↦ ?_
  have h := regAt_one_sub_qParam_pow_leadZero (a + i)
  rwa [add_right_comm, pow_add] at h

/-- The term of index `k ≠ 0` of `V_n(q)` is nonzero of positive order. -/
private theorem torusSum_term_pos_leadZero (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) {k : ℤ}
    (hk0 : k ≠ 0) :
    qParam ^ ((r : ℤ) * k * ((s : ℤ) * k + 1)) * quantumInt (2 * (s : ℤ) * k + 1) ≠ 0 ∧
      0 < pairQTOrder (qParam ^ ((r : ℤ) * k * ((s : ℤ) * k + 1)) *
        quantumInt (2 * (s : ℤ) * k + 1)) := by
  have hr0 : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have hs0 : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have hne : 2 * (s : ℤ) * k + 1 ≠ 0 := by
    rw [mul_assoc]
    omega
  have h := pairQTOrder_mul_eq (pairQTOrder_qParam_zpow_eq ((r : ℤ) * k * ((s : ℤ) * k + 1)))
    (pairQTOrder_quantumInt hne)
  refine ⟨h.1, ?_⟩
  rw [h.2, mul_assoc 2 (s : ℤ) k]
  rcases lt_or_gt_of_ne hk0 with h0 | h0
  · have h1 : (s : ℤ) * k < 0 := by nlinarith
    have h2 : (1 : ℤ) ≤ -((r : ℤ) * k) - 1 := by nlinarith
    have h3 : (1 : ℤ) ≤ -((s : ℤ) * k) - 1 := by nlinarith
    have h4 := one_le_mul_of_one_le_of_one_le h2 h3
    rw [min_eq_left (by omega)]
    nlinarith
  · have h1 : 0 < (s : ℤ) * k := by nlinarith
    have h2 : (2 : ℤ) * k ≤ r * k := by nlinarith
    rw [min_eq_right (by omega)]
    nlinarith

/-- `V_n(q)` has the value `1` at `t = 0`. -/
private theorem regAt_torusSum_leadZero (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (n : ℕ) :
    TwsRegAtLeadZero (twsTorusSum true r s n) 1 := by
  have hsum := regAt_sum_leadZero (Finset.Icc (-(n : ℤ)) (n : ℤ))
    (fun k ↦ qParam ^ ((r : ℤ) * k * ((s : ℤ) * k + 1)) * quantumInt (2 * (s : ℤ) * k + 1))
    (fun k ↦ if k = 0 then 1 else 0) fun k _ ↦ by
      by_cases hk : k = 0
      · have hq1 : quantumInt 1 = 1 := by
          rw [quantumInt, mul_one]
          exact div_self (pairQTOrder_X_zpow_sub_zpow (a := 2) (b := -2) (by omega)).1
        rw [hk, ite_eq_left rfl, mul_zero, zero_mul, zpow_zero, mul_zero, zero_add, hq1, mul_one]
        exact regAt_one_leadZero
      · rw [ite_eq_right hk]
        exact regAt_of_pos_leadZero (torusSum_term_pos_leadZero r s hr hs hk)
  rw [Finset.sum_ite_eq' (Finset.Icc (-(n : ℤ)) (n : ℤ)) 0 fun _ ↦ (1 : ℚ),
    ite_eq_left (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)] at hsum
  simpa only [twsTorusSum, ↓reduceIte, one_mul] using hsum

/-- At `a = 0` the clasp form `Y_{0,N}` of the right-handed companion has the value `N` at
`t = 0`. -/
private theorem regAt_twsY_leadZero (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (ℓ : ℤ)
    (ha : twIndex true r s ℓ = 0) {N : ℕ} (hN : 1 ≤ N) :
    TwsRegAtLeadZero (twsY false (twsInput true r s ℓ) N) (N : ℚ) := by
  have hV : ∀ n : ℕ, TwsRegAtLeadZero (twsTheta false n * twsInput true r s ℓ n) 1 := by
    intro n
    have h := regAt_torusSum_leadZero r s hr hs n
    simpa only [twsTheta, twsInput, ha, zero_mul, neg_zero, zpow_zero, one_mul,
      Bool.false_eq_true, ↓reduceIte] using h
  have hterm : ∀ n ∈ Finset.range N, ∀ i ∈ Finset.range (N - n),
      TwsRegAtLeadZero (qParam ^ (N * i) * (twsTheta false n * twsInput true r s ℓ n) *
        (qPochhammer (qParam ^ (i + 1)) n * qPochhammer (qParam ^ (N - i - n)) n /
          qPochhammer qParam n)) (if i = 0 then 1 else 0) := by
    intro n hn i hi
    rw [Finset.mem_range] at hn hi
    have hP1 := regAt_qPochhammer_leadZero i n
    have hP2 := regAt_qPochhammer_leadZero (N - i - n - 1) n
    have hP3 := regAt_qPochhammer_leadZero 0 n
    rw [show N - i - n - 1 + 1 = N - i - n by omega] at hP2
    rw [zero_add, pow_one] at hP3
    have h := regAt_mul_leadZero (regAt_mul_leadZero (regAt_qParam_pow_leadZero (N * i)) (hV n))
      (regAt_div_leadZero (regAt_mul_leadZero hP1 hP2) hP3 one_ne_zero)
    have hc : (if N * i = 0 then (1 : ℚ) else 0) * 1 * (1 * 1 / 1) = if i = 0 then 1 else 0 := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp
      · rw [ite_eq_right (Nat.mul_ne_zero (by omega) hi0.ne'), ite_eq_right hi0.ne']
        simp
    rwa [hc] at h
  have hinner : ∀ n ∈ Finset.range N, TwsRegAtLeadZero (∑ i ∈ Finset.range (N - n),
      qParam ^ (N * i) * (twsTheta false n * twsInput true r s ℓ n) *
        (qPochhammer (qParam ^ (i + 1)) n * qPochhammer (qParam ^ (N - i - n)) n /
          qPochhammer qParam n)) 1 := by
    intro n hn
    have h := regAt_sum_leadZero _ _ _ (hterm n hn)
    rwa [Finset.sum_ite_eq' (Finset.range (N - n)) 0 fun _ ↦ (1 : ℚ),
      ite_eq_left (Finset.mem_range.mpr (by rw [Finset.mem_range] at hn; omega))] at h
  have hsum := regAt_sum_leadZero _ _ _ hinner
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hpre := regAt_div_leadZero (regAt_one_sub_qParam_pow_leadZero 0)
    (regAt_one_sub_qParam_pow_leadZero M) one_ne_zero
  rw [zero_add, pow_one] at hpre
  have h := regAt_mul_leadZero hpre hsum
  rwa [div_one, one_mul] at h

/-- At `a = 0` the reduced sequence of the right-handed companion is nonzero of order `4 (N - 1)`
at `t = 0`, with leading coefficient `N`. -/
theorem tws_lead_reducedFormula_zero (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (ℓ : ℤ)
    (ha : twIndex true r s ℓ = 0) {N : ℕ} (hN : 1 ≤ N) :
    pairQReducedFormula (twsInput true r s ℓ) N ≠ 0 ∧
      pairQTOrder (pairQReducedFormula (twsInput true r s ℓ) N) = 4 * ((N : ℤ) - 1) ∧
      (twsSeries (pairQReducedFormula (twsInput true r s ℓ) N)).leadingCoeff = (N : ℚ) := by
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨hY0, -, hYo, hYl⟩ :=
    lead_of_regAt_leadZero (regAt_twsY_leadZero r s hr hs ℓ ha hN) hN0
  have hm := pairQTOrder_mul_eq (pairQTOrder_qParam_pow_eq (N - 1)) ⟨hY0, hYo⟩
  rw [tws_reducedFormula_eq_twsY _ hN]
  refine ⟨hm.1, ?_, ?_⟩
  · rw [hm.2, Nat.cast_sub hN]
    push_cast
    ring
  · rw [map_mul, HahnSeries.leadingCoeff_mul, hYl, ← zpow_natCast,
      qParam_zpow_eq_ratFuncX_zpow, twsSeries_X_zpow, twsT, HahnSeries.leadingCoeff_of_single,
      one_mul]

end AJConjecture
