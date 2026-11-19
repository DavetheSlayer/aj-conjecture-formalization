import Mathlib
import AJTwist.Exist.TwHTarget
import AJTwist.Exist.TwHXDegreeIter

/-!
# The cleared target of a nontrivial relation is not zero

Let `I ≤ r` be an index with `ρ_s = 0` for `I < s ≤ r`. In
`twHTarget d q r ρ = ∑_{s ≤ r} (q^d x)^(r-s) (twAdjoint d q)^[s] ρ_s` the term `s` has degree
at most `(r - s) + 2s = r + s` in `x` (`twH_natDegree_swap_iterate_twAdjoint_le`), the terms
with `s > I` vanish (`twAdjoint d q 0 = 0`), and the term `s = I` contributes
`q^(d(r-I)) ∏_{u=1}^{I} (1 - q^u J) · ρ_I(q^I J)` to the coefficient of `x^(r+I)`
(`twH_coeff_swap_iterate_twAdjoint`). This is `twH_coeff_swap_twHTarget`.

Over a domain with `q ≠ 0` this coefficient is not zero when `ρ_I ≠ 0` (the factors
`1 - q^u J` have constant term `1`; `ρ_I(q^I J) ≠ 0` because `q^I ≠ 0`,
`Polynomial.comp_eq_zero_iff` or comparison of leading coefficients). Taking for `I` the largest
index `s ≤ r` with `ρ_s ≠ 0` gives `twHTarget_ne_zero`. No condition on the window `d`.

Checked (scratch `H/h03_pipeline.py`): in the 22 cases of the pipeline the degree in `x` of the
target is `r + I` and its leading coefficient is the one displayed.
-/

open Polynomial Polynomial.Bivariate

noncomputable section

namespace AJConjecture

/-- The cleared adjoint of zero is zero. -/
private theorem twAdjoint_zero_targetNeZero {R : Type*} [CommRing R] (d : ℕ) (q : R) :
    twAdjoint d q (0 : R[X][X]) = 0 := by
  rw [twAdjoint, zero_comp, mul_zero, mul_zero, mul_zero, sub_zero, divX_zero, add_zero]

/-- The swapped cleared target as a sum of monomials in `x` times swapped iterates. -/
private theorem swap_twHTarget_targetNeZero {R : Type*} [CommRing R] (d : ℕ) (q : R) (r : ℕ)
    (ρ : ℕ → R[X]) :
    swap (twHTarget d q r ρ) = ∑ s ∈ Finset.range (r + 1),
      C (C (q ^ (d * (r - s)))) * X ^ (r - s) *
        swap ((twAdjoint d q)^[s] ((ρ s).map C)) := by
  simp only [twHTarget, map_sum, map_mul, map_pow, swap_C, map_C, map_X,
    mul_pow, pow_mul]

/-- The coefficient of `x^(r+I)` of the cleared target, when `ρ_s = 0` for `I < s ≤ r`. -/
theorem twH_coeff_swap_twHTarget {R : Type*} [CommRing R] (d : ℕ) (q : R) (r : ℕ)
    (ρ : ℕ → R[X]) {I : ℕ} (hI : I ≤ r) (hzero : ∀ s, I < s → s ≤ r → ρ s = 0) :
    (swap (twHTarget d q r ρ)).coeff (r + I) =
      C (q ^ (d * (r - I))) * (∏ u ∈ Finset.range I, (1 - C (q ^ (u + 1)) * X)) *
        (ρ I).comp (C (q ^ I) * X) := by
  have hmon : ∀ k : ℕ, (C (C (q ^ (d * k))) * X ^ k : R[X][X]).natDegree ≤ k := fun k ↦
    (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le k)
  rw [swap_twHTarget_targetNeZero, finsetSum_coeff, Finset.sum_eq_single I]
  · rw [show r + I = (r - I) + 2 * I by omega, coeff_mul_add_eq_of_natDegree_le (hmon (r - I))
      (twH_natDegree_swap_iterate_twAdjoint_le d q I (ρ I)), twH_coeff_swap_iterate_twAdjoint,
      coeff_C_mul, coeff_X_pow_self, mul_one, mul_assoc]
  · intro s hs hsI
    rcases lt_or_gt_of_ne hsI with h | h
    · refine coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_mul_le_of_le (hmon (r - s))
        (twH_natDegree_swap_iterate_twAdjoint_le d q s (ρ s))) ?_)
      have hs' := Finset.mem_range.mp hs
      omega
    · rw [hzero s h (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)), Polynomial.map_zero,
        Function.iterate_fixed (twAdjoint_zero_targetNeZero d q), map_zero, mul_zero,
        coeff_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hI)) h

/-- The cleared target of a nontrivial relation is not zero. -/
theorem twHTarget_ne_zero {R : Type*} [CommRing R] [IsDomain R] (d : ℕ) {q : R} (hq : q ≠ 0)
    (r : ℕ) (ρ : ℕ → R[X]) (hρ : ∃ s, s ≤ r ∧ ρ s ≠ 0) : twHTarget d q r ρ ≠ 0 := by
  classical
  obtain ⟨s₀, hs₀, hne₀⟩ := hρ
  have hI : Nat.findGreatest (fun s ↦ ρ s ≠ 0) r ≤ r := Nat.findGreatest_le r
  have hne : ρ (Nat.findGreatest (fun s ↦ ρ s ≠ 0) r) ≠ 0 :=
    Nat.findGreatest_spec (P := fun s ↦ ρ s ≠ 0) hs₀ hne₀
  have hzero : ∀ s, Nat.findGreatest (fun s ↦ ρ s ≠ 0) r < s → s ≤ r → ρ s = 0 := fun s h1 h2 ↦
    not_not.mp (Nat.findGreatest_is_greatest (P := fun s ↦ ρ s ≠ 0) h1 h2)
  intro h0
  have hc := twH_coeff_swap_twHTarget d q r ρ hI hzero
  rw [h0, map_zero, coeff_zero] at hc
  have hfac : ∀ u ∈ Finset.range (Nat.findGreatest (fun s ↦ ρ s ≠ 0) r),
      (1 - C (q ^ (u + 1)) * X : R[X]) ≠ 0 := by
    intro u _ h
    have h1 := congrArg (eval (0 : R)) h
    rw [eval_sub, eval_one, eval_mul, eval_X, mul_zero, sub_zero, eval_zero] at h1
    exact one_ne_zero h1
  have hcomp : (ρ (Nat.findGreatest (fun s ↦ ρ s ≠ 0) r)).comp
      (C (q ^ Nat.findGreatest (fun s ↦ ρ s ≠ 0) r) * X) ≠ 0 := fun h ↦
    hne ((comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hq))).mp h)
  exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr (pow_ne_zero _ hq))
    (Finset.prod_ne_zero_iff.mpr hfac)) hcomp hc.symm

end AJConjecture
