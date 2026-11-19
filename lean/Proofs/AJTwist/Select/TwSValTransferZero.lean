import Mathlib
import AJHandoff.TorusQuantum.PairQFormula
import AJHandoff.TorusQuantum.PairQTOrderFormula
import AJHandoff.TorusQuantum.PairQReducedDegree
import AJTwist.Select.TwSValClass
import AJTwist.Select.TwSPeriodOrder

/-!
# Valuation bounds at `t = 0` for the finite transform, and the Gaussian periods

Source: Section 6.1 of `selection.tex` (revision 5), the bounds on the weighted forcing module,
here for the unweighted transform of an arbitrary input (the weights are absorbed by the closure
of growth classes under recurrence operators).

For `0 ≤ n ≤ j < N` the summand `C_j(N) K_{j,n} u_n` of `F_N = pairQReducedFormula u N` has order
`2 j (j+1) - 4 j N + 4 j + 2 n (n+1) + ord u_n` at `t = 0`. Hence, if
`ord u_n ≥ -(4 k n(n+1) + B (n+1))` with `k ≥ 0`, then `ord F_N ≥ -max(2, 4k) N² - O(N)` (minimum
at `n = 0`, `j ≈ N` for `k = 0`, at `n = j = N - 1` for `k ≥ 1`). The period inputs
`twsPeriodInput ℓ c` satisfy the hypothesis with `k = max(0, -ℓ)`, for every `c`
(`tws_tOrder_periodInput_ge`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A power of `-1` is nonzero of order `0`. -/
private theorem pairQTOrder_neg_one_pow_twsValZero (n : ℕ) :
    (-1 : RatFunc ℚ) ^ n ≠ 0 ∧ pairQTOrder ((-1 : RatFunc ℚ) ^ n) = 0 := by
  have h1 : pairQTOrder (1 : RatFunc ℚ) = 0 := by simpa using pairQTOrder_X_zpow 0
  refine ⟨pow_ne_zero n (neg_ne_zero.mpr one_ne_zero), ?_⟩
  rcases neg_one_pow_eq_or (RatFunc ℚ) n with h | h
  · rw [h, h1]
  · rw [h, pairQTOrder_neg, h1]

/-- Twice the exponent `n(n+1)/2` is `n(n+1)`. -/
private theorem two_mul_triangle_twsValZero (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ℤ) * 2 = (n : ℤ) * ((n : ℤ) + 1) := by
  exact_mod_cast Nat.div_two_mul_two_of_even (Nat.even_mul_succ_self n)

/-- The cyclotomic kernel `C_j(N)`, `j < N`, is nonzero of order `2j(j+1) - 4jN`. -/
private theorem pairQTOrder_cyclotomicKernel_of_lt_twsValZero {N : ℕ} (j : ℕ) (hj : j < N) :
    cyclotomicKernel j N ≠ 0 ∧ pairQTOrder (cyclotomicKernel j N) =
      2 * (j : ℤ) * ((j : ℤ) + 1) - 4 * (j : ℤ) * N := by
  induction j with
  | zero =>
    rw [cyclotomicKernel, Finset.Icc_eq_empty (by omega), Finset.prod_empty]
    exact ⟨one_ne_zero, by simpa using pairQTOrder_X_zpow 0⟩
  | succ j ih =>
    have h1 := pairQTOrder_one_sub_qParam_zpow_of_pos (k := ((j + 1 : ℕ) : ℤ) + N) (by omega)
    have h2 := pairQTOrder_one_sub_qParam_zpow_of_neg (k := ((j + 1 : ℕ) : ℤ) - N) (by omega)
    have h3 := pairQTOrder_mul_eq (ih (by omega)) (pairQTOrder_mul_eq h1 h2)
    rw [cyclotomicKernel, Finset.prod_Icc_succ_top (by omega)]
    refine ⟨h3.1, h3.2.trans ?_⟩
    push_cast
    ring

/-- The ultrametric inequality at `t = 0`: a sum of two elements that are zero or of order at
least `d` is zero or of order at least `d`. -/
private theorem pairQTOrder_add_ge_twsValZero {d : ℤ} {x y : RatFunc ℚ}
    (hx : x = 0 ∨ d ≤ pairQTOrder x) (hy : y = 0 ∨ d ≤ pairQTOrder y) :
    x + y = 0 ∨ d ≤ pairQTOrder (x + y) := by
  by_cases hx0 : x = 0
  · rwa [hx0, zero_add]
  by_cases hy0 : y = 0
  · rwa [hy0, add_zero]
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  refine Or.inr ?_
  have h := twsOrd_tOrder.map_sub hx0 (neg_ne_zero.mpr hy0) (by rwa [sub_neg_eq_add])
  rw [sub_neg_eq_add, pairQTOrder_neg] at h
  exact (le_min (hx.resolve_left hx0) (hy.resolve_left hy0)).trans h

/-- A finite sum of elements that are zero or of order at least `d` is zero or of order at
least `d`. -/
private theorem pairQTOrder_sum_ge_twsValZero {ι : Type*} {d : ℤ} (s : Finset ι)
    (f : ι → RatFunc ℚ) (h : ∀ i ∈ s, f i = 0 ∨ d ≤ pairQTOrder (f i)) :
    ∑ i ∈ s, f i = 0 ∨ d ≤ pairQTOrder (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun x ↦ x = 0 ∨ d ≤ pairQTOrder x)
    (fun _ _ ↦ pairQTOrder_add_ge_twsValZero) (Or.inl rfl) h

/-- The product of a nonzero element of order `d` and an element that is zero or of order at
least `e` is zero or of order at least `d + e`. -/
private theorem pairQTOrder_mul_ge_twsValZero {d e : ℤ} {x y : RatFunc ℚ}
    (hx : x ≠ 0 ∧ pairQTOrder x = d) (hy : y = 0 ∨ e ≤ pairQTOrder y) :
    x * y = 0 ∨ d + e ≤ pairQTOrder (x * y) := by
  by_cases hy0 : y = 0
  · exact Or.inl (by rw [hy0, mul_zero])
  · refine Or.inr ?_
    rw [pairQTOrder_mul hx.1 hy0, hx.2]
    exact add_le_add_right (hy.resolve_left hy0) d

/-- The term `n` of the sum defining `D_j` is zero or of order at least
`2n(n+1) + e`, if `u_n` is zero or of order at least `e`. -/
private theorem pairQTOrder_cycloCoeff_term_ge_twsValZero {u : ℕ → RatFunc ℚ} {e : ℤ} (j n : ℕ)
    (hu : u n = 0 ∨ e ≤ pairQTOrder (u n)) :
    (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) = 0 ∨
      2 * (n : ℤ) * ((n : ℤ) + 1) + e ≤
        pairQTOrder ((-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
          (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))) := by
  have hw := pairQTOrder_div_eq
    (pairQTOrder_mul_eq (pairQTOrder_neg_one_pow_twsValZero n)
      (pairQTOrder_qParam_pow_eq (n * (n + 1) / 2)))
    (pairQTOrder_mul_eq (pairQTOrder_qPochhammer_qParam (j - n))
      (pairQTOrder_qPochhammer_qParam (j + n + 1)))
  have h := pairQTOrder_mul_ge_twsValZero hw hu
  rw [div_mul_eq_mul_div] at h
  have h2 := two_mul_triangle_twsValZero n
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- `D_j` is zero or of order at least `4j + d`, if every `u_n`, `n ≤ j`, is zero or of order at
least `d - 2n(n+1)`. -/
private theorem pairQTOrder_cycloCoeff_ge_twsValZero {u : ℕ → RatFunc ℚ} {d : ℤ} (j : ℕ)
    (hu : ∀ n : ℕ, n ≤ j → u n = 0 ∨ d - 2 * (n : ℤ) * ((n : ℤ) + 1) ≤ pairQTOrder (u n)) :
    pairQCycloCoeff u j = 0 ∨ 4 * (j : ℤ) + d ≤ pairQTOrder (pairQCycloCoeff u j) := by
  have h1 := pairQTOrder_one_sub_qParam_zpow_of_pos (k := 1) one_pos
  rw [zpow_one] at h1
  have hp := pairQTOrder_mul_eq (pairQTOrder_mul_eq (pairQTOrder_qParam_pow_eq j) h1)
    (pairQTOrder_qPochhammer_qParam j)
  have h := pairQTOrder_mul_ge_twsValZero hp (pairQTOrder_sum_ge_twsValZero (d := d)
    (Finset.range (j + 1)) (fun n ↦ (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
      (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))) fun n hn ↦ by
        rcases pairQTOrder_cycloCoeff_term_ge_twsValZero j n
          (hu n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))) with h | h
        · exact Or.inl h
        · exact Or.inr (by linarith))
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [pairQCycloCoeff]; linarith)

/-- The least order of the summands of `F_N` over the triangle `n ≤ j < N` is at least
`-max(2, 4k) N² - |B| N - |B|`. -/
private theorem summand_order_ge_twsValZero {k B j n N : ℤ} (hk : 0 ≤ k) (hn : 0 ≤ n)
    (hnj : n ≤ j) (hjN : j + 1 ≤ N) :
    -(max 2 (4 * k) * N ^ 2 + |B| * N + |B|) ≤
      2 * j * (j + 1) - 4 * j * N + 4 * j + 2 * n * (n + 1) -
        (4 * k * n * (n + 1) + B * (n + 1)) := by
  have hB0 := abs_nonneg B
  have hB1 : B * (n + 1) ≤ |B| * (n + 1) := mul_le_mul_of_nonneg_right (le_abs_self B) (by omega)
  have hB2 : |B| * (n + 1) ≤ |B| * N := mul_le_mul_of_nonneg_left (by omega) hB0
  have hnn : 0 ≤ n * (n + 1) := mul_nonneg hn (by omega)
  have hsq := sq_nonneg (j - N)
  rcases hk.eq_or_lt with h0 | h1
  · rw [← h0, mul_zero, max_eq_left (by norm_num)]
    nlinarith
  · rw [max_eq_right (by omega)]
    have h3 : n * (n + 1) ≤ (N - 1) * N := by nlinarith
    have h4 : (4 * k - 2) * (n * (n + 1)) ≤ (4 * k - 2) * ((N - 1) * N) :=
      mul_le_mul_of_nonneg_left h3 (by omega)
    have h5 : 0 ≤ (4 * k - 2) * N := mul_nonneg (by omega) (by omega)
    nlinarith

/-- Lower bound at `t = 0` for the finite transform of an input of order at least
`-(4 k n(n+1) + B (n+1))`. -/
theorem tws_valClass_tOrder_reducedFormula (u : ℕ → RatFunc ℚ) (k B : ℤ) (hk : 0 ≤ k)
    (hu : ∀ n : ℕ, u n = 0 ∨
      -(4 * k * n * ((n : ℤ) + 1) + B * ((n : ℤ) + 1)) ≤ pairQTOrder (u n)) :
    TwsValClass pairQTOrder (max 2 (4 * k)) (pairQReducedFormulaEven u) := by
  refine ⟨|B|, 0, fun m hm ↦ ?_⟩
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rw [pairQReducedFormulaEven, Int.natAbs_natCast, pairQReducedFormula]
  refine pairQTOrder_sum_ge_twsValZero _ _ fun j hj ↦ ?_
  have hjN : j < N := Finset.mem_range.mp hj
  have h := pairQTOrder_mul_ge_twsValZero (pairQTOrder_cyclotomicKernel_of_lt_twsValZero j hjN)
    (pairQTOrder_cycloCoeff_ge_twsValZero (u := u)
      (d := -(max 2 (4 * k) * (N : ℤ) ^ 2 + |B| * N + |B|) -
        (2 * (j : ℤ) * ((j : ℤ) + 1) - 4 * (j : ℤ) * N) - 4 * (j : ℤ)) j fun n hn ↦ by
        rcases hu n with h0 | h1
        · exact Or.inl h0
        · have h2 := summand_order_ge_twsValZero (k := k) (B := B) (j := j) (n := n) (N := N) hk
            (Int.natCast_nonneg n) (by omega) (by omega)
          exact Or.inr (by linarith))
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- The Gaussian periods have order at least `-max(2, -4ℓ) N² - O(N)` at `t = 0`
(`ν ≥ -h N² - O(N)` for `ℓ = -h < 0`, `ν ≥ -N²/2 - O(N)` for `ℓ ≥ 0`). -/
theorem tws_valClass_tOrder_period (ℓ c : ℤ) :
    TwsValClass pairQTOrder (max 2 (-(4 * ℓ)))
      (pairQReducedFormulaEven (twsPeriodInput ℓ c)) := by
  have hmax : max 2 (-(4 * ℓ)) = max 2 (4 * max 0 (-ℓ)) := by
    rcases le_total 0 ℓ with h | h
    · rw [max_eq_left (show -ℓ ≤ 0 by omega), mul_zero, max_eq_left (show -(4 * ℓ) ≤ 2 by omega),
        max_eq_left (by norm_num)]
    · rw [max_eq_right (show 0 ≤ -ℓ by omega), mul_neg]
  rw [hmax]
  refine tws_valClass_tOrder_reducedFormula _ (max 0 (-ℓ)) (4 * |c|) (le_max_left _ _) fun n ↦ ?_
  rcases tws_tOrder_periodInput_ge ℓ c n with h0 | h1
  · exact Or.inl h0
  · refine Or.inr (le_trans ?_ h1)
    have hnn : (0 : ℤ) ≤ (n : ℤ) * ((n : ℤ) + 1) := mul_nonneg (by omega) (by omega)
    have h2 : 0 ≤ (max 0 (-ℓ) + ℓ) * ((n : ℤ) * ((n : ℤ) + 1)) :=
      mul_nonneg (by have := le_max_right 0 (-ℓ); omega) hnn
    linarith

end AJConjecture
