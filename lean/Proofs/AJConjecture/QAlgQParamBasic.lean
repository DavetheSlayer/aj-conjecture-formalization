import Mathlib
import AJConjecture.WhiteheadFormula

/-!
# Basic facts on `q = t⁴` in `ℚ(t)`

The indeterminate `t` of `ℚ(t)` is transcendental over `ℚ`, so its integer powers are pairwise
distinct; the same holds for `q = t⁴`. Consequently `1 - q^n ≠ 0` for `n ≠ 0`, the `q`-Pochhammer
symbols `(q; q)_j` do not vanish, and `q^n` has degree `4n` in `t`.
-/

namespace AJConjecture

/-- An integer power of the indeterminate `t` of `ℚ(t)` has degree its exponent. -/
private theorem intDegree_ratFuncX_zpow_eq (n : ℤ) :
    ((RatFunc.X : RatFunc ℚ) ^ n).intDegree = n := by
  have hnat : ∀ m : ℕ, ((RatFunc.X : RatFunc ℚ) ^ m).intDegree = m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero m RatFunc.X_ne_zero) RatFunc.X_ne_zero, ih,
        RatFunc.intDegree_X]
      push_cast
      rfl
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, hnat]
  · rw [zpow_neg, RatFunc.intDegree_inv, zpow_natCast, hnat]

/-- An integer power of `q` is an integer power of `t`. -/
theorem qParam_zpow_eq_ratFuncX_zpow (n : ℤ) :
    qParam ^ n = (RatFunc.X : RatFunc ℚ) ^ (4 * n) := by
  rw [qParam, ← zpow_natCast, ← zpow_mul]
  rfl

/-- Distinct integer powers of the indeterminate of `ℚ(t)` are distinct. -/
theorem ratFuncX_zpow_injective :
    Function.Injective fun n : ℤ ↦ (RatFunc.X : RatFunc ℚ) ^ n := by
  intro m n h
  have h' := congrArg RatFunc.intDegree h
  simpa only [intDegree_ratFuncX_zpow_eq] using h'

/-- `q = t⁴` is not zero. -/
theorem qParam_ne_zero : qParam ≠ 0 :=
  pow_ne_zero 4 RatFunc.X_ne_zero

/-- Distinct integer powers of `q = t⁴` are distinct. -/
theorem qParam_zpow_injective : Function.Injective fun n : ℤ ↦ qParam ^ n := by
  intro m n h
  simp only [qParam_zpow_eq_ratFuncX_zpow] at h
  have h4 : 4 * m = 4 * n := ratFuncX_zpow_injective h
  omega

/-- `1 - q^n ≠ 0` for `n ≠ 0`: `q` is not a root of unity. -/
theorem one_sub_qParam_zpow_ne_zero {n : ℤ} (hn : n ≠ 0) : 1 - qParam ^ n ≠ 0 := by
  intro h
  have h1 : qParam ^ n = qParam ^ (0 : ℤ) := by
    rw [zpow_zero]
    exact (sub_eq_zero.mp h).symm
  exact hn (qParam_zpow_injective h1)

/-- The `q`-Pochhammer symbol `(q; q)_j` is not zero. -/
theorem qPochhammer_qParam_ne_zero (j : ℕ) : qPochhammer qParam j ≠ 0 := by
  rw [qPochhammer, Finset.prod_ne_zero_iff]
  intro s _
  have h := one_sub_qParam_zpow_ne_zero (n := (s : ℤ) + 1) (by omega)
  rwa [zpow_add₀ qParam_ne_zero, zpow_one, zpow_natCast, mul_comm] at h

/-- `q^n` has degree `4n` in `t`. -/
theorem intDegree_qParam_zpow (n : ℤ) : (qParam ^ n).intDegree = 4 * n := by
  rw [qParam_zpow_eq_ratFuncX_zpow, intDegree_ratFuncX_zpow_eq]

end AJConjecture
