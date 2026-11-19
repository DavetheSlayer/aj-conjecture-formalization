import Mathlib
import AJConjecture.QAlgEvalAtFieldDegree
import AJConjecture.QAlgEventuallyRational
import AJFamily.Quantum.TorusFormulaEven
import AJFamily.Quantum.TorusReducedFormulaDegree

/-!
# The torus reduced formula is not eventually rational

For `a ≥ 2`, the even reduced formula is not eventually rational in `M = t^(2n)`: its `t`-degree
`4n(n-1)` is not eventually affine in `n`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The even extension of the family's reduced formula at a colour `n ≥ 1` is nonzero of degree
`4n(n-1)` in `t`. -/
private theorem intDegree_torusReducedFormulaEven_of_one_le (a : ℕ) (ha : 2 ≤ a) {n : ℤ}
    (hn : 1 ≤ n) :
    torusReducedFormulaEven a n ≠ 0 ∧
      (torusReducedFormulaEven a n).intDegree = 4 * n * (n - 1) := by
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
  rw [torusReducedFormulaEven, Int.natAbs_natCast]
  exact intDegree_torusReducedFormula a ha (by exact_mod_cast hn)

/-- The polynomial `4n(n-1)` is not an affine function of `n` on a tail of the integers. -/
private theorem not_forall_ge_four_mul_mul_pred_eq_affine_torus (A B m : ℤ) :
    ¬ ∀ n : ℤ, m ≤ n → 4 * n * (n - 1) = A * n + B := by
  intro h
  have e1 := h m le_rfl
  have e2 := h (m + 1) (by omega)
  have e3 := h (m + 2) (by omega)
  have h8 : (8 : ℤ) = 0 := by linear_combination e1 - 2 * e2 + e3
  omega

/-- The family's reduced formula is not a rational function of `M = t^(2n)` on its positive
tail. -/
theorem not_eventuallyRational_torusReducedFormulaEven (a : ℕ) (ha : 2 ≤ a) :
    ¬ EventuallyRational (torusReducedFormulaEven a) := by
  rintro ⟨p, b, hb, n₀, h⟩
  obtain ⟨Ab, Bb, nb, hdb⟩ := exists_intDegree_evalAtField_eq hb
  by_cases hp : p = 0
  · have hF := intDegree_torusReducedFormulaEven_of_one_le a ha (le_max_right (max n₀ nb) 1)
    have e := h (max (max n₀ nb) 1) ((le_max_left n₀ nb).trans (le_max_left _ 1))
    rw [hp, map_zero] at e
    exact mul_ne_zero (hdb _ ((le_max_right n₀ nb).trans (le_max_left _ 1))).1 hF.1 e
  · obtain ⟨Aa, Ba, na, hda⟩ := exists_intDegree_evalAtField_eq hp
    refine not_forall_ge_four_mul_mul_pred_eq_affine_torus (Aa - Ab) (Ba - Bb)
      (max (max n₀ nb) (max na 1)) fun n hn ↦ ?_
    have h1 : n₀ ≤ n := (le_max_left n₀ nb).trans ((le_max_left _ _).trans hn)
    have h2 : nb ≤ n := (le_max_right n₀ nb).trans ((le_max_left _ _).trans hn)
    have h3 : na ≤ n := (le_max_left na 1).trans ((le_max_right _ _).trans hn)
    have h4 : 1 ≤ n := (le_max_right na 1).trans ((le_max_right _ _).trans hn)
    have hF := intDegree_torusReducedFormulaEven_of_one_le a ha h4
    have e := congrArg RatFunc.intDegree (h n h1)
    rw [RatFunc.intDegree_mul (hdb n h2).1 hF.1, (hdb n h2).2, hF.2, (hda n h3).2] at e
    linear_combination e

end AJConjecture
