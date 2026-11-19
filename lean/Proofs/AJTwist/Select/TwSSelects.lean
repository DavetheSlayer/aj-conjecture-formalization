import Mathlib
import AJHandoff.TorusQuantum.PairQFormula
import AJTwist.Select.TwSRelativeForcing
import AJTwist.Select.TwSInput

/-!
# The selection statement and its consequence for tail annihilators

Source: Sections 6.3 and 6.7 of `selection.tex` (revision 5).

* `twsPeriod ℓ c` is the Gaussian period `G_c^{(ℓ)}`: the finite transform of the input
  `twsPeriodInput ℓ c`, as a sequence on `ℤ`.
* `TwsSelects ℓ u`: there is a growth class whose saturation contains all Gaussian periods
  `G_c^{(ℓ)}`, `c ∈ ℤ`, and does not contain the finite transform `F` of the input `u`
  ("`F ∉ 𝒰_ℓ`", with `𝒰_ℓ = ∑_c 𝔻 G_c^{(ℓ)}` replaced by a growth class containing it).
* `TwsForcingInPeriods ℓ u P`: the transfer in module form, eq. (finite-module-force):
  `P F ∈ ∑_c 𝔻 G_c^{(ℓ)}` on a tail, up to a nonzero left coefficient. This is the input taken
  from the transfer package (TwQ).
* `tws_tail_annihilator_of_selects`, `tws_selected_divisor_of_selects`: with Lemma 6.1, every
  tail annihilator of `F` is a left pseudo-multiple of `P` (irreducible case), respectively of a
  right pseudo-factor of `P` of order at least two (no first-order right divisor).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The Gaussian period `G_c^{(ℓ)}`: the finite transform of `twsPeriodInput ℓ c`. -/
def twsPeriod (ℓ c : ℤ) : ℤ → RatFunc ℚ :=
  pairQReducedFormulaEven (twsPeriodInput ℓ c)

/-- The selection statement of Section 6 for the twist `ℓ` and the input `u`: a growth class
whose saturation contains every Gaussian period `G_c^{(ℓ)}` and not the finite transform of
`u`. -/
def TwsSelects (ℓ : ℤ) (u : ℕ → RatFunc ℚ) : Prop :=
  ∃ U : (ℤ → RatFunc ℚ) → Prop, TwsGrowthClass U ∧ (∀ c : ℤ, TwsSat U (twsPeriod ℓ c)) ∧
    ¬ TwsSat U (pairQReducedFormulaEven u)

/-- The transfer in module form (eq. (finite-module-force)): on a tail, a nonzero coefficient
multiple of `P F` is a finite sum of images of Gaussian periods `G_c^{(ℓ)}` under recurrence
operators, where `F` is the finite transform of `u`. -/
def TwsForcingInPeriods (ℓ : ℤ) (u : ℕ → RatFunc ℚ) (P : RecOp) : Prop :=
  TwsInSpan (twsPeriod ℓ) fun n ↦ opApplyField P (pairQReducedFormulaEven u) n

/-- If the selection statement holds, the forcing lies in the module of the periods and `P` has
no right pseudo-factor of intermediate order, then every operator annihilating a tail of `F` is
a left pseudo-multiple of `P`. -/
theorem tws_tail_annihilator_of_selects {ℓ : ℤ} {u : ℕ → RatFunc ℚ} (hsel : TwsSelects ℓ u)
    {P : RecOp} (hP : P ≠ 0)
    (hirr : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree = 0 ∨ R.natDegree = P.natDegree)
    (hforce : TwsForcingInPeriods ℓ u P) {Q : RecOp} {n₁ : ℤ}
    (hQ : ∀ n : ℤ, n₁ ≤ n → opApplyField Q (pairQReducedFormulaEven u) n = 0) :
    ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q = oreMul coeffShift T P := by
  obtain ⟨U, hU, hper, hF⟩ := hsel
  exact tws_exists_C_mul_eq_oreMul_of_relative hU hP hirr (tws_sat_of_inSpan hU hper hforce) hF hQ

/-- If the selection statement holds, the forcing lies in the module of the periods and `P` has
no right pseudo-factor of order one, then some right pseudo-factor `R` of `P` of order at least
two right-divides every operator annihilating a tail of `F`. -/
theorem tws_selected_divisor_of_selects {ℓ : ℤ} {u : ℕ → RatFunc ℚ} (hsel : TwsSelects ℓ u)
    {P : RecOp} (hP : P ≠ 0)
    (hlin : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree ≠ 1)
    (hforce : TwsForcingInPeriods ℓ u P) :
    ∃ R : RecOp, 2 ≤ R.natDegree ∧
      (∃ β : Coeff, β ≠ 0 ∧ ∃ S : RecOp, C β * P = oreMul coeffShift S R) ∧
      ∀ {Q : RecOp} {n₁ : ℤ},
        (∀ n : ℤ, n₁ ≤ n → opApplyField Q (pairQReducedFormulaEven u) n = 0) →
        ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q = oreMul coeffShift T R := by
  obtain ⟨U, hU, hper, hF⟩ := hsel
  exact tws_exists_selected_divisor_of_no_linear hU hP hlin (tws_sat_of_inSpan hU hper hforce) hF

end AJConjecture
