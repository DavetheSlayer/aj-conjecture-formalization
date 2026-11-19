import Mathlib
import AJConjecture.QAlgEvalAtFieldDegree
import AJConjecture.QAlgEventuallyRational
import AJHandoff.TorusQuantum.PairQReducedDegree
import AJHandoff.TorusQuantum.PairQOddColorDegree
import AJHandoff.TorusQuantum.PairQOddColorRec

/-!
# The reduced sequence of `T(r, s)` is not eventually rational

`pairQ_not_eventuallyRational`: under the hypotheses of `pairQ_intDegree_reducedFormula`, the even
reduced sequence is not eventually the evaluation of a rational function of `t` and `M = t^(2n)`:
its degree `4n(n-1)` is quadratic in `n`, while the degree of an evaluated rational function is
eventually affine (as `not_eventuallyRational_torusReducedFormulaEven`, from
`QAlgEvalAtFieldDegree`). For `T(r, s)`, `r, s ≥ 2`, the hypotheses hold by
`pairQOddColor_zero` and `pairQ_intDegree_oddColor` (`r + s - rs ≤ 0`). This is the
nonrationality of source §5, read at the degree in `t` instead of the `t`-valuation (Q13): the
degree is independent of `(r, s)` and reuses the library's lemmas.
-/

noncomputable section

namespace AJConjecture

/-- The even reduced formula at a colour `n ≥ 1` is nonzero of degree `4n(n-1)` in `t`. -/
private theorem intDegree_pairQReducedFormulaEven_of_one_le (u : ℕ → RatFunc ℚ)
    (h0 : u 0 = 1) (hdeg : ∀ n : ℕ, 1 ≤ n → u n = 0 ∨ (u n).intDegree ≤ 0) {n : ℤ}
    (hn : 1 ≤ n) :
    pairQReducedFormulaEven u n ≠ 0 ∧
      (pairQReducedFormulaEven u n).intDegree = 4 * n * (n - 1) := by
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
  rw [pairQReducedFormulaEven, Int.natAbs_natCast]
  exact pairQ_intDegree_reducedFormula u h0 hdeg (by exact_mod_cast hn)

/-- The polynomial `4n(n-1)` is not an affine function of `n` on a tail of the integers. -/
private theorem not_forall_ge_four_mul_mul_pred_eq_affine_pairQ (A B m : ℤ) :
    ¬ ∀ n : ℤ, m ≤ n → 4 * n * (n - 1) = A * n + B := by
  intro h
  have e1 := h m le_rfl
  have e2 := h (m + 1) (by omega)
  have e3 := h (m + 2) (by omega)
  have h8 : (8 : ℤ) = 0 := by linear_combination e1 - 2 * e2 + e3
  omega

theorem pairQ_not_eventuallyRational (u : ℕ → RatFunc ℚ) (h0 : u 0 = 1)
    (hdeg : ∀ n : ℕ, 1 ≤ n → u n = 0 ∨ (u n).intDegree ≤ 0) :
    ¬ EventuallyRational (pairQReducedFormulaEven u) := by
  rintro ⟨p, b, hb, n₀, h⟩
  obtain ⟨Ab, Bb, nb, hdb⟩ := exists_intDegree_evalAtField_eq hb
  by_cases hp : p = 0
  · have hF := intDegree_pairQReducedFormulaEven_of_one_le u h0 hdeg
      (le_max_right (max n₀ nb) 1)
    have e := h (max (max n₀ nb) 1) ((le_max_left n₀ nb).trans (le_max_left _ 1))
    rw [hp, map_zero] at e
    exact mul_ne_zero (hdb _ ((le_max_right n₀ nb).trans (le_max_left _ 1))).1 hF.1 e
  · obtain ⟨Aa, Ba, na, hda⟩ := exists_intDegree_evalAtField_eq hp
    refine not_forall_ge_four_mul_mul_pred_eq_affine_pairQ (Aa - Ab) (Ba - Bb)
      (max (max n₀ nb) (max na 1)) fun n hn ↦ ?_
    have h1 : n₀ ≤ n := (le_max_left n₀ nb).trans ((le_max_left _ _).trans hn)
    have h2 : nb ≤ n := (le_max_right n₀ nb).trans ((le_max_left _ _).trans hn)
    have h3 : na ≤ n := (le_max_left na 1).trans ((le_max_right _ _).trans hn)
    have h4 : 1 ≤ n := (le_max_right na 1).trans ((le_max_right _ _).trans hn)
    have hF := intDegree_pairQReducedFormulaEven_of_one_le u h0 hdeg h4
    have e := congrArg RatFunc.intDegree (h n h1)
    rw [RatFunc.intDegree_mul (hdb n h2).1 hF.1, (hdb n h2).2, hF.2, (hda n h3).2] at e
    linear_combination e

theorem pairQ_not_eventuallyRational_pair (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) :
    ¬ EventuallyRational (pairQReducedFormulaEven (pairQOddColor r s)) := by
  refine pairQ_not_eventuallyRational _ (pairQOddColor_zero r s) fun n _ ↦ Or.inr ?_
  rw [(pairQ_intDegree_oddColor r s (by omega) (by omega) n).2]
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have hs' : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have hrs : (r : ℤ) + s - r * s ≤ 0 := by nlinarith
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  nlinarith

end AJConjecture
