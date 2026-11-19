import Mathlib
import AJHandoff.TorusQuantum.PairQFormula
import AJHandoff.TorusQuantum.PairQTOrderFormula
import AJHandoff.TorusQuantum.PairQReducedDegree
import AJTwist.Select.TwSValClass
import AJTwist.Select.TwSPeriodOrder

/-!
# Degree bounds for the finite transform, and the Gaussian periods

Source: Section 6.2 of `selection.tex` (revision 5), the bounds at infinity on the weighted
forcing module, here for the unweighted transform of an arbitrary input.

For `0 ≤ n ≤ j < N` the summand `C_j(N) K_{j,n} u_n` of `F_N = pairQReducedFormula u N` has degree
`4 j N - 2 n (n+1) + deg u_n`. Hence, if `deg u_n ≤ 4 k n(n+1) + B (n+1)` with `k ≥ 0`, then
`deg F_N ≤ max(4, 4k+2) N² + O(N)`. The period inputs `twsPeriodInput ℓ c` satisfy the hypothesis
with `k = max(0, ℓ)`, for every `c` (`tws_intDegree_periodInput_le`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A power of `-1` is nonzero of degree `0`. -/
private theorem intDegree_neg_one_pow_twsValInf (n : ℕ) :
    (-1 : RatFunc ℚ) ^ n ≠ 0 ∧ ((-1 : RatFunc ℚ) ^ n).intDegree = 0 := by
  refine ⟨pow_ne_zero n (neg_ne_zero.mpr one_ne_zero), ?_⟩
  rcases neg_one_pow_eq_or (RatFunc ℚ) n with h | h
  · rw [h, RatFunc.intDegree_one]
  · rw [h, RatFunc.intDegree_neg, RatFunc.intDegree_one]

/-- Twice the exponent `n(n+1)/2` is `n(n+1)`. -/
private theorem two_mul_triangle_twsValInf (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ℤ) * 2 = (n : ℤ) * ((n : ℤ) + 1) := by
  exact_mod_cast Nat.div_two_mul_two_of_even (Nat.even_mul_succ_self n)

/-- A natural power of `q` is nonzero of degree `4k` in `t`. -/
private theorem intDegree_qParam_pow_twsValInf (k : ℕ) :
    qParam ^ k ≠ 0 ∧ (qParam ^ k).intDegree = 4 * (k : ℤ) :=
  ⟨pow_ne_zero k qParam_ne_zero, by rw [← zpow_natCast, intDegree_qParam_zpow]⟩

/-- `1 - q^k`, `k > 0`, is nonzero of degree `4k` in `t`. -/
private theorem intDegree_one_sub_qParam_zpow_of_pos_twsValInf {k : ℤ} (hk : 0 < k) :
    1 - qParam ^ k ≠ 0 ∧ (1 - qParam ^ k).intDegree = 4 * k := by
  rw [sub_eq_neg_add]
  refine intDegree_add_eq_of_lt
    ⟨neg_ne_zero.mpr (zpow_ne_zero k qParam_ne_zero), ?_⟩ (Or.inr ?_)
  · rw [RatFunc.intDegree_neg, intDegree_qParam_zpow]
  · rw [RatFunc.intDegree_one]
    omega

/-- `1 - q^k`, `k < 0`, is nonzero of degree `0` in `t`. -/
private theorem intDegree_one_sub_qParam_zpow_of_neg_twsValInf {k : ℤ} (hk : k < 0) :
    1 - qParam ^ k ≠ 0 ∧ (1 - qParam ^ k).intDegree = 0 := by
  rw [sub_eq_add_neg]
  refine intDegree_add_eq_of_lt ⟨one_ne_zero, RatFunc.intDegree_one⟩ (Or.inr ?_)
  rw [RatFunc.intDegree_neg, intDegree_qParam_zpow]
  omega

/-- The `q`-Pochhammer symbol `(q; q)_k` is nonzero of degree `2k(k+1)` in `t`. -/
private theorem intDegree_qPochhammer_qParam_twsValInf (k : ℕ) :
    qPochhammer qParam k ≠ 0 ∧
      (qPochhammer qParam k).intDegree = 2 * (k : ℤ) * ((k : ℤ) + 1) := by
  induction k with
  | zero =>
    rw [qPochhammer, Finset.prod_range_zero]
    exact ⟨one_ne_zero, by rw [RatFunc.intDegree_one]; simp⟩
  | succ k ih =>
    have h1 := intDegree_one_sub_qParam_zpow_of_pos_twsValInf (k := (k : ℤ) + 1) (by omega)
    rw [zpow_add₀ qParam_ne_zero, zpow_one, zpow_natCast, mul_comm] at h1
    have h2 := intDegree_mul_eq ih h1
    rw [qPochhammer, Finset.prod_range_succ]
    refine ⟨h2.1, h2.2.trans ?_⟩
    push_cast
    ring

/-- The cyclotomic kernel `C_j(N)`, `j < N`, is nonzero of degree `4jN + 2j(j+1)` in `t`. -/
private theorem intDegree_cyclotomicKernel_of_lt_twsValInf {N : ℕ} (j : ℕ) (hj : j < N) :
    cyclotomicKernel j N ≠ 0 ∧ (cyclotomicKernel j N).intDegree =
      4 * (j : ℤ) * N + 2 * (j : ℤ) * ((j : ℤ) + 1) := by
  induction j with
  | zero =>
    rw [cyclotomicKernel, Finset.Icc_eq_empty (by omega), Finset.prod_empty]
    exact ⟨one_ne_zero, by rw [RatFunc.intDegree_one]; simp⟩
  | succ j ih =>
    have h1 := intDegree_one_sub_qParam_zpow_of_pos_twsValInf
      (k := ((j + 1 : ℕ) : ℤ) + N) (by omega)
    have h2 := intDegree_one_sub_qParam_zpow_of_neg_twsValInf
      (k := ((j + 1 : ℕ) : ℤ) - N) (by omega)
    have h3 := intDegree_mul_eq (ih (by omega)) (intDegree_mul_eq h1 h2)
    rw [cyclotomicKernel, Finset.prod_Icc_succ_top (by omega)]
    refine ⟨h3.1, h3.2.trans ?_⟩
    push_cast
    ring

/-- A finite sum of elements that are zero or of degree at most `d` is zero or of degree at
most `d`. -/
private theorem intDegree_sum_le_twsValInf {ι : Type*} {d : ℤ} (s : Finset ι)
    (f : ι → RatFunc ℚ) (h : ∀ i ∈ s, f i = 0 ∨ (f i).intDegree ≤ d) :
    ∑ i ∈ s, f i = 0 ∨ (∑ i ∈ s, f i).intDegree ≤ d := by
  rcases intDegree_sum_lt_of_lt (d := d + 1) s f fun i hi ↦
    (h i hi).imp_right Int.lt_add_one_iff.mpr with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (Int.lt_add_one_iff.mp h1)

/-- The product of a nonzero element of degree `d` and an element that is zero or of degree at
most `e` is zero or of degree at most `d + e`. -/
private theorem intDegree_mul_le_twsValInf {d e : ℤ} {x y : RatFunc ℚ}
    (hx : x ≠ 0 ∧ x.intDegree = d) (hy : y = 0 ∨ y.intDegree ≤ e) :
    x * y = 0 ∨ (x * y).intDegree ≤ d + e := by
  by_cases hy0 : y = 0
  · exact Or.inl (by rw [hy0, mul_zero])
  · refine Or.inr ?_
    rw [RatFunc.intDegree_mul hx.1 hy0, hx.2]
    exact add_le_add_right (hy.resolve_left hy0) d

/-- The term `n ≤ j` of the sum defining `D_j` is zero or of degree at most
`e - 2n(n+1) - 4(j+1)²`, if `u_n` is zero or of degree at most `e`. -/
private theorem intDegree_cycloCoeff_term_le_twsValInf {u : ℕ → RatFunc ℚ} {e : ℤ} {j n : ℕ}
    (hn : n ≤ j) (hu : u n = 0 ∨ (u n).intDegree ≤ e) :
    (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) = 0 ∨
      ((-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))).intDegree ≤
        e - 2 * (n : ℤ) * ((n : ℤ) + 1) - 4 * ((j : ℤ) + 1) ^ 2 := by
  have hw := intDegree_div_eq
    (intDegree_mul_eq (intDegree_neg_one_pow_twsValInf n)
      (intDegree_qParam_pow_twsValInf (n * (n + 1) / 2)))
    (intDegree_mul_eq (intDegree_qPochhammer_qParam_twsValInf (j - n))
      (intDegree_qPochhammer_qParam_twsValInf (j + n + 1)))
  have h := intDegree_mul_le_twsValInf hw hu
  rw [div_mul_eq_mul_div, Nat.cast_sub hn, Nat.cast_add, Nat.cast_add, Nat.cast_one] at h
  have h2 := two_mul_triangle_twsValInf n
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- `D_j` is zero or of degree at most `d - 2j(j+1)`, if every `u_n`, `n ≤ j`, is zero or of
degree at most `d + 2n(n+1)`. -/
private theorem intDegree_cycloCoeff_le_twsValInf {u : ℕ → RatFunc ℚ} {d : ℤ} (j : ℕ)
    (hu : ∀ n : ℕ, n ≤ j → u n = 0 ∨ (u n).intDegree ≤ d + 2 * (n : ℤ) * ((n : ℤ) + 1)) :
    pairQCycloCoeff u j = 0 ∨
      (pairQCycloCoeff u j).intDegree ≤ d - 2 * (j : ℤ) * ((j : ℤ) + 1) := by
  have h1 := intDegree_one_sub_qParam_zpow_of_pos_twsValInf (k := 1) one_pos
  rw [zpow_one] at h1
  have hp := intDegree_mul_eq (intDegree_mul_eq (intDegree_qParam_pow_twsValInf j) h1)
    (intDegree_qPochhammer_qParam_twsValInf j)
  have h := intDegree_mul_le_twsValInf hp (intDegree_sum_le_twsValInf
    (d := d - 4 * ((j : ℤ) + 1) ^ 2)
    (Finset.range (j + 1)) (fun n ↦ (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
      (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))) fun n hn ↦ by
        have hnj : n ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        rcases intDegree_cycloCoeff_term_le_twsValInf hnj (hu n hnj) with h | h
        · exact Or.inl h
        · exact Or.inr (by linarith))
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [pairQCycloCoeff]; linarith)

/-- The largest degree of the summands of `F_N` over the triangle `n ≤ j < N` is at most
`max(4, 4k+2) N² + |B| N + |B|`. -/
private theorem summand_degree_le_twsValInf {k B j n N : ℤ} (hk : 0 ≤ k) (hn : 0 ≤ n)
    (hnj : n ≤ j) (hjN : j + 1 ≤ N) :
    4 * j * N - 2 * n * (n + 1) + (4 * k * n * (n + 1) + B * (n + 1)) ≤
      max 4 (4 * k + 2) * N ^ 2 + |B| * N + |B| := by
  have hB0 := abs_nonneg B
  have hB1 : B * (n + 1) ≤ |B| * (n + 1) := mul_le_mul_of_nonneg_right (le_abs_self B) (by omega)
  have hB2 : |B| * (n + 1) ≤ |B| * N := mul_le_mul_of_nonneg_left (by omega) hB0
  have hnn : 0 ≤ n * (n + 1) := mul_nonneg hn (by omega)
  have hjN' : j * N ≤ (N - 1) * N := mul_le_mul_of_nonneg_right (by omega) (by omega)
  have hN : 0 ≤ N := by omega
  rcases hk.eq_or_lt with h0 | h1
  · rw [← h0, mul_zero, zero_add, max_eq_left (by norm_num)]
    nlinarith
  · rw [max_eq_right (by omega)]
    have h3 : n * (n + 1) ≤ (N - 1) * N := by nlinarith
    have h4 : (4 * k - 2) * (n * (n + 1)) ≤ (4 * k - 2) * ((N - 1) * N) :=
      mul_le_mul_of_nonneg_left h3 (by omega)
    have h5 : 0 ≤ (4 * k + 2) * N := mul_nonneg (by omega) hN
    nlinarith

/-- Upper bound for the degree of the finite transform of an input of degree at most
`4 k n(n+1) + B (n+1)`. -/
theorem tws_valClass_inf_reducedFormula (u : ℕ → RatFunc ℚ) (k B : ℤ) (hk : 0 ≤ k)
    (hu : ∀ n : ℕ, u n = 0 ∨ (u n).intDegree ≤ 4 * k * n * ((n : ℤ) + 1) + B * ((n : ℤ) + 1)) :
    TwsValClass (fun f : RatFunc ℚ ↦ -f.intDegree) (max 4 (4 * k + 2))
      (pairQReducedFormulaEven u) := by
  refine ⟨|B|, 0, fun m hm ↦ ?_⟩
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rw [pairQReducedFormulaEven, Int.natAbs_natCast, pairQReducedFormula]
  have hsum := intDegree_sum_le_twsValInf
    (d := max 4 (4 * k + 2) * (N : ℤ) ^ 2 + |B| * N + |B|) (Finset.range N)
    (fun j ↦ cyclotomicKernel j N * pairQCycloCoeff u j) fun j hj ↦ by
      have hjN : j < N := Finset.mem_range.mp hj
      have h := intDegree_mul_le_twsValInf (intDegree_cyclotomicKernel_of_lt_twsValInf j hjN)
        (intDegree_cycloCoeff_le_twsValInf (u := u)
          (d := max 4 (4 * k + 2) * (N : ℤ) ^ 2 + |B| * N + |B| - 4 * (j : ℤ) * N) j
          fun n hn ↦ by
            rcases hu n with h0 | h1
            · exact Or.inl h0
            · have h2 := summand_degree_le_twsValInf (k := k) (B := B) (j := j) (n := n)
                (N := N) hk (Int.natCast_nonneg n) (by omega) (by omega)
              exact Or.inr (by linarith))
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
  rcases hsum with h | h
  · exact Or.inl h
  · exact Or.inr (neg_le_neg h)

/-- The Gaussian periods have degree at most `max(4, 4ℓ+2) N² + O(N)`
(`ν_∞ ≥ -max(1, ℓ + 1/2) N² - O(N)`). -/
theorem tws_valClass_inf_period (ℓ c : ℤ) :
    TwsValClass (fun f : RatFunc ℚ ↦ -f.intDegree) (max 4 (4 * ℓ + 2))
      (pairQReducedFormulaEven (twsPeriodInput ℓ c)) := by
  have hmax : max 4 (4 * ℓ + 2) = max 4 (4 * max 0 ℓ + 2) := by
    rcases le_total ℓ 0 with h | h
    · rw [max_eq_left h, mul_zero, zero_add, max_eq_left (show 4 * ℓ + 2 ≤ 4 by omega),
        max_eq_left (by norm_num)]
    · rw [max_eq_right h]
  rw [hmax]
  refine tws_valClass_inf_reducedFormula _ (max 0 ℓ) (4 * |c|) (le_max_left _ _) fun n ↦ ?_
  rcases tws_intDegree_periodInput_le ℓ c n with h0 | h1
  · exact Or.inl h0
  · refine Or.inr (h1.trans ?_)
    have hnn : (0 : ℤ) ≤ (n : ℤ) * ((n : ℤ) + 1) := mul_nonneg (by omega) (by omega)
    have h2 : 0 ≤ (max 0 ℓ - ℓ) * ((n : ℤ) * ((n : ℤ) + 1)) :=
      mul_nonneg (by have := le_max_right 0 ℓ; omega) hnn
    linarith

end AJConjecture
