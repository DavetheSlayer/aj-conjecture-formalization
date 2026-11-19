import Mathlib
import AJConjecture.RecurrenceIdeal
import AJConjecture.FieldActionBridge
import AJConjecture.QAlgOpApplyFieldBasic
import AJConjecture.QAlgEvalAtFieldZeros
import AJTwist.Exist.TwHBar

/-!
# The mirror map on recurrence operators and its action on barred sequences (Unit M2)

Source: revision 5, Section 8.2 (`conclusion.tex`): "the knot mirror acts by the Ore map
`Θ(t, M, L) = (t⁻¹, M⁻¹, L)`, preserves the defining relation and satisfies
`(Θ(H) Φ_{S^*})(N; t) = (H Φ_S)(N; t⁻¹)`. It identifies the saturated annihilator ideals."

The library's operators have polynomial coefficients (`Coeff = ℤ[t][M]`), so `Θ` is taken with
cleared denominators: `Θ(∑ D_i L^i) = ∑ t^A M^B D_i(t⁻¹, M⁻¹) L^i` with one common monomial
`t^A M^B`. This is `twHBarOp A B` of the package Exist (`AJTwist/Exist/TwHBar.lean`,
`twHBarCoeff A B c = t^A M^B c(t⁻¹, M⁻¹)`), for any bounds `A`, `B` of the degrees in `t` and
`M` of the coefficients.

* `twmTDeg P`, `twmMDeg P`: the least such bounds, and `twmBarOp P = twHBarOp (twmTDeg P)
  (twmMDeg P) P`, the mirror operator `Θ(P)`.
* `opApplyField_twHBarOp`: `(Θ(P) \bar f)(n) = t^(A + 2nB) \bar{(P f)(n)}` for every sequence
  `f : ℤ → ℚ(t)` (`\bar` is `twQBar`, `t ↦ t⁻¹`).
* `twmBarOp_ne_zero`, `natDegree_twmBarOp`: `Θ` preserves nonzero operators and the order.
* `twm_inLocalizedAnnihilator_barOp`: if `J'` is the bar of `J` (two sequences of Laurent
  polynomials) and `Q` lies in the localized annihilator of `J'`, then `Θ(Q)` lies in the
  localized annihilator of `J`.

With these, `twH_exists_barOp P` of the package Exist is
`⟨twmBarOp P, twmBarOp_ne_zero, _, _, opApplyField_twmBarOp P⟩`.

Checked in exact arithmetic (`SCR/M/py/m01_mirror.py`, items (1) and (5)). The input from the
package Exist is `evalAtField_twHBarCoeff` (the value of a reflected coefficient at a colour);
this file has no `sorry`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The least common bound of the degrees in `t` of the coefficients of `P`. -/
def twmTDeg (P : RecOp) : ℕ :=
  P.support.sup fun i ↦ (P.coeff i).support.sup fun b ↦ ((P.coeff i).coeff b).natDegree

/-- The least common bound of the degrees in `M` of the coefficients of `P`. -/
def twmMDeg (P : RecOp) : ℕ :=
  P.support.sup fun i ↦ (P.coeff i).natDegree

theorem natDegree_coeff_coeff_le_twmTDeg (P : RecOp) (i b : ℕ) :
    ((P.coeff i).coeff b).natDegree ≤ twmTDeg P := by
  by_cases hi : P.coeff i = 0
  · simp [hi]
  by_cases hb : (P.coeff i).coeff b = 0
  · simp [hb]
  exact (Finset.le_sup (f := fun b ↦ ((P.coeff i).coeff b).natDegree)
    (mem_support_iff.mpr hb)).trans
      (Finset.le_sup (f := fun i ↦ (P.coeff i).support.sup fun b ↦
        ((P.coeff i).coeff b).natDegree) (mem_support_iff.mpr hi))

theorem natDegree_coeff_le_twmMDeg (P : RecOp) (i : ℕ) :
    (P.coeff i).natDegree ≤ twmMDeg P := by
  by_cases hi : P.coeff i = 0
  · simp [hi]
  exact Finset.le_sup (f := fun i ↦ (P.coeff i).natDegree) (mem_support_iff.mpr hi)

/-- The mirror operator `Θ(P) = t^A M^B P(t⁻¹, M⁻¹, L)`, with `A`, `B` the degrees of `P` in `t`
and in `M`. -/
def twmBarOp (P : RecOp) : RecOp :=
  twHBarOp (twmTDeg P) (twmMDeg P) P

theorem twHBarCoeff_zero (A B : ℕ) : twHBarCoeff A B 0 = 0 := by
  simp [twHBarCoeff]

/-- The coefficients of `twHBarOp A B P` are the reflected coefficients of `P`. -/
theorem coeff_twHBarOp (A B : ℕ) (P : RecOp) (i : ℕ) :
    (twHBarOp A B P).coeff i = twHBarCoeff A B (P.coeff i) := by
  simp only [twHBarOp, finsetSum_coeff, coeff_monomial, Finsupp.single_apply,
    Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), twHBarCoeff_zero]

/-- **The mirror operator on barred sequences**: for bounds `A`, `B` of the degrees of the
coefficients of `P` in `t` and `M`,
`(twHBarOp A B P · \bar f)(n) = t^(A + 2nB) · \bar{(P f)(n)}`. -/
theorem opApplyField_twHBarOp (A B : ℕ) (P : RecOp)
    (hA : ∀ i b : ℕ, ((P.coeff i).coeff b).natDegree ≤ A)
    (hB : ∀ i : ℕ, (P.coeff i).natDegree ≤ B) (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (twHBarOp A B P) (fun m ↦ twQBar (f m)) n =
      RatFunc.X ^ ((A : ℤ) + 2 * n * B) * twQBar (opApplyField P f n) := by
  have hdeg : (twHBarOp A B P).natDegree < P.natDegree + 1 := by
    refine Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_)
    rw [coeff_twHBarOp, coeff_eq_zero_of_natDegree_lt hN, twHBarCoeff_zero]
  rw [opApplyField, opApplyField,
    sum_over_range' _ (fun i ↦ by rw [map_zero, zero_mul]) _ hdeg,
    sum_over_range' _ (fun i ↦ by rw [map_zero, zero_mul]) _ (Nat.lt_succ_self _), map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_twHBarOp, evalAtField_twHBarCoeff A B _ (hA i) (hB i), map_mul, mul_assoc]

/-- The action of `Θ(P)` on barred sequences. -/
theorem opApplyField_twmBarOp (P : RecOp) (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (twmBarOp P) (fun m ↦ twQBar (f m)) n =
      RatFunc.X ^ ((twmTDeg P : ℤ) + 2 * n * twmMDeg P) * twQBar (opApplyField P f n) :=
  opApplyField_twHBarOp _ _ P (natDegree_coeff_coeff_le_twmTDeg P) (natDegree_coeff_le_twmMDeg P)
    f n

/-- A nonzero coefficient has a nonzero reflection (for bounds of its degrees). -/
theorem twHBarCoeff_ne_zero (A B : ℕ) {c : Coeff} (hc : c ≠ 0)
    (hA : ∀ b : ℕ, (c.coeff b).natDegree ≤ A) (hB : c.natDegree ≤ B) :
    twHBarCoeff A B c ≠ 0 := by
  obtain ⟨n₀, hn₀⟩ := exists_forall_ge_evalAtField_ne_zero hc
  intro h0
  have h := evalAtField_twHBarCoeff A B c hA hB n₀
  rw [h0, map_zero] at h
  exact mul_ne_zero (zpow_ne_zero _ RatFunc.X_ne_zero)
    ((map_ne_zero twQBar).mpr (hn₀ n₀ le_rfl)) h.symm

/-- The mirror operator of a nonzero operator is not zero. -/
theorem twmBarOp_ne_zero {P : RecOp} (hP : P ≠ 0) : twmBarOp P ≠ 0 := by
  intro h0
  have hlc : P.coeff P.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hP
  have h := coeff_twHBarOp (twmTDeg P) (twmMDeg P) P P.natDegree
  rw [← twmBarOp, h0, coeff_zero] at h
  exact twHBarCoeff_ne_zero _ _ hlc (natDegree_coeff_coeff_le_twmTDeg P _)
    (natDegree_coeff_le_twmMDeg P _) h.symm

/-- The mirror operator has the same order in `L`. -/
theorem natDegree_twmBarOp (P : RecOp) : (twmBarOp P).natDegree = P.natDegree := by
  refine le_antisymm (natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_) ?_
  · rw [twmBarOp, coeff_twHBarOp, coeff_eq_zero_of_natDegree_lt hN, twHBarCoeff_zero]
  · by_cases hP : P = 0
    · rw [hP, natDegree_zero]
      exact Nat.zero_le _
    · refine le_natDegree_of_ne_zero ?_
      rw [twmBarOp, coeff_twHBarOp]
      refine twHBarCoeff_ne_zero _ _ ?_ (natDegree_coeff_coeff_le_twmTDeg P _)
        (natDegree_coeff_le_twmMDeg P _)
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hP

/-- **The mirror map carries the localized annihilator of the barred sequence into the
localized annihilator of the sequence** ("it identifies the saturated annihilator ideals"). -/
theorem twm_inLocalizedAnnihilator_barOp {J J' : ℤ → ℤ[T;T⁻¹]}
    (hbar : ∀ n : ℤ, laurentToField (J' n) = twQBar (laurentToField (J n))) {Q : RecOp}
    (hQ : InLocalizedAnnihilator J' Q) : InLocalizedAnnihilator J (twmBarOp Q) := by
  obtain ⟨c, hc, hann⟩ := hQ
  have hA : ∀ b : ℕ, (c.coeff b).natDegree ≤ c.support.sup fun b ↦ (c.coeff b).natDegree := by
    intro b
    by_cases hb : c.coeff b = 0
    · simp [hb]
    · exact Finset.le_sup (f := fun b ↦ (c.coeff b).natDegree) (mem_support_iff.mpr hb)
  refine ⟨twHBarCoeff _ _ c, twHBarCoeff_ne_zero _ _ hc hA le_rfl, fun n ↦ ?_⟩
  apply laurentToField_injective
  have hJ : (fun m ↦ laurentToField (J m)) = fun m ↦ twQBar (laurentToField (J' m)) := by
    funext m
    rw [hbar, twQBar_twQBar]
  have h0 : opApplyField (Polynomial.C c * Q) (fun m ↦ laurentToField (J' m)) n = 0 := by
    rw [← laurentToField_opApply, hann n, map_zero]
  rw [opApplyField_C_mul_left] at h0
  rw [map_zero, laurentToField_opApply, hJ, opApplyField_C_mul_left, opApplyField_twmBarOp,
    evalAtField_twHBarCoeff _ _ c hA le_rfl, mul_mul_mul_comm, ← map_mul, h0, map_zero, mul_zero]

end AJConjecture
