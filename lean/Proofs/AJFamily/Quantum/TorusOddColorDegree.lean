import Mathlib
import AJConjecture.QAlgQParamBasic
import AJFamily.Quantum.TorusFormula

/-!
# Degree of the odd colours

For `a ≥ 2`, the odd colour `u_n` of `T(2, a)` is nonzero of `t`-degree `4(2 - a)n`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- A sum of two elements of `ℚ(t)` that are zero or of degree less than `d` is zero or of
degree less than `d`. -/
theorem intDegree_add_lt_of_lt {d : ℤ} {x y : RatFunc ℚ}
    (hx : x = 0 ∨ x.intDegree < d) (hy : y = 0 ∨ y.intDegree < d) :
    x + y = 0 ∨ (x + y).intDegree < d := by
  rcases hx with rfl | hx
  · rwa [zero_add]
  rcases hy with rfl | hy
  · rw [add_zero]
    exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  · exact Or.inr ((RatFunc.intDegree_add_le hxy).trans_lt (max_lt hx hy))

/-- A finite sum of elements of `ℚ(t)` that are zero or of degree less than `d` is zero or of
degree less than `d`. -/
theorem intDegree_sum_lt_of_lt {ι : Type*} {d : ℤ} (s : Finset ι)
    (f : ι → RatFunc ℚ) (h : ∀ i ∈ s, f i = 0 ∨ (f i).intDegree < d) :
    ∑ i ∈ s, f i = 0 ∨ (∑ i ∈ s, f i).intDegree < d :=
  Finset.sum_induction f (fun x ↦ x = 0 ∨ x.intDegree < d)
    (fun _ _ ↦ intDegree_add_lt_of_lt) (Or.inl rfl) h

/-- Strict dominance: adding a term of smaller degree does not change the degree. -/
theorem intDegree_add_eq_of_lt {d : ℤ} {a b : RatFunc ℚ}
    (ha : a ≠ 0 ∧ a.intDegree = d) (hb : b = 0 ∨ b.intDegree < d) :
    a + b ≠ 0 ∧ (a + b).intDegree = d := by
  obtain ⟨ha0, rfl⟩ := ha
  rcases hb with rfl | hb
  · rw [add_zero]
    exact ⟨ha0, rfl⟩
  have hab : a + b ≠ 0 := by
    intro h
    rw [eq_neg_of_add_eq_zero_left h, RatFunc.intDegree_neg] at hb
    exact lt_irrefl _ hb
  refine ⟨hab, le_antisymm ((RatFunc.intDegree_add_le hab).trans (max_le le_rfl hb.le)) ?_⟩
  have h1 : a + b + -b ≠ 0 := by rwa [add_neg_cancel_right]
  have h2 := RatFunc.intDegree_add_le h1
  rw [add_neg_cancel_right, RatFunc.intDegree_neg] at h2
  rcases le_max_iff.mp h2 with h | h
  · exact h
  · exact absurd h (not_le.mpr hb)

/-- A finite sum with a unique term of maximal degree has the degree of that term. -/
theorem intDegree_sum_eq_of_lt {ι : Type*} [DecidableEq ι] {d : ℤ}
    {s : Finset ι} {f : ι → RatFunc ℚ} {a : ι} (has : a ∈ s)
    (ha : f a ≠ 0 ∧ (f a).intDegree = d)
    (h : ∀ i ∈ s, i ≠ a → f i = 0 ∨ (f i).intDegree < d) :
    ∑ i ∈ s, f i ≠ 0 ∧ (∑ i ∈ s, f i).intDegree = d := by
  rw [← Finset.add_sum_erase s f has]
  exact intDegree_add_eq_of_lt ha (intDegree_sum_lt_of_lt _ _ fun i hi ↦
    h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))

/-- The degree of a product of nonzero elements of `ℚ(t)`. -/
theorem intDegree_mul_eq {d e : ℤ} {x y : RatFunc ℚ}
    (hx : x ≠ 0 ∧ x.intDegree = d) (hy : y ≠ 0 ∧ y.intDegree = e) :
    x * y ≠ 0 ∧ (x * y).intDegree = d + e :=
  ⟨mul_ne_zero hx.1 hy.1, by rw [RatFunc.intDegree_mul hx.1 hy.1, hx.2, hy.2]⟩

/-- The degree of a quotient of nonzero elements of `ℚ(t)`. -/
theorem intDegree_div_eq {d e : ℤ} {x y : RatFunc ℚ}
    (hx : x ≠ 0 ∧ x.intDegree = d) (hy : y ≠ 0 ∧ y.intDegree = e) :
    x / y ≠ 0 ∧ (x / y).intDegree = d - e :=
  ⟨div_ne_zero hx.1 hy.1, by rw [RatFunc.intDegree_div hx.1 hy.1, hx.2, hy.2]⟩

/-- An integer power of `t` is nonzero of degree its exponent. -/
private theorem intDegree_ratFuncX_zpow_torusOdd (n : ℤ) :
    (RatFunc.X : RatFunc ℚ) ^ n ≠ 0 ∧ ((RatFunc.X : RatFunc ℚ) ^ n).intDegree = n := by
  refine ⟨zpow_ne_zero n RatFunc.X_ne_zero, ?_⟩
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

/-- A difference of distinct powers of `t` is nonzero of degree the larger exponent. -/
private theorem intDegree_ratFuncX_zpow_sub_zpow_torusOdd {a b : ℤ} (hab : a ≠ b) :
    (RatFunc.X : RatFunc ℚ) ^ a - RatFunc.X ^ b ≠ 0 ∧
      ((RatFunc.X : RatFunc ℚ) ^ a - RatFunc.X ^ b).intDegree = max a b := by
  have key : ∀ c d : ℤ, d < c → (RatFunc.X : RatFunc ℚ) ^ c - RatFunc.X ^ d ≠ 0 ∧
      ((RatFunc.X : RatFunc ℚ) ^ c - RatFunc.X ^ d).intDegree = c := by
    intro c d hdc
    rw [sub_eq_add_neg]
    refine intDegree_add_eq_of_lt (intDegree_ratFuncX_zpow_torusOdd c) (Or.inr ?_)
    rwa [RatFunc.intDegree_neg, (intDegree_ratFuncX_zpow_torusOdd d).2]
  rcases lt_or_gt_of_ne hab with h | h
  · have h1 := key b a h
    rw [max_eq_right h.le, ← neg_sub, RatFunc.intDegree_neg]
    exact ⟨neg_ne_zero.mpr h1.1, h1.2⟩
  · rw [max_eq_left h.le]
    exact key a b h

/-- The quantum integer `[m]`, `m ≠ 0`, is nonzero of degree `2|m| - 2` in `t`. -/
private theorem intDegree_quantumInt_torusOdd {m : ℤ} (hm : m ≠ 0) :
    quantumInt m ≠ 0 ∧ (quantumInt m).intDegree = max (2 * m) (-(2 * m)) - 2 := by
  have h1 := intDegree_ratFuncX_zpow_sub_zpow_torusOdd (a := 2 * m) (b := -(2 * m)) (by omega)
  have h2 := intDegree_ratFuncX_zpow_sub_zpow_torusOdd (a := 2) (b := -2) (by omega)
  exact intDegree_div_eq h1 h2

set_option linter.unusedVariables false in
/-- The odd colour `u_n` of `T(2, a)` is nonzero of degree `4(2 - a)n` in `t`. -/
theorem intDegree_torusOddColor (a : ℕ) (ha : 2 ≤ a) (n : ℕ) :
    torusOddColor a n ≠ 0 ∧ (torusOddColor a n).intDegree = 4 * (2 - (a : ℤ)) * n := by
  have hterm : ∀ s : ℤ, qParam ^ ((a : ℤ) * s * (2 * s + 1)) * quantumInt (4 * s + 1) ≠ 0 ∧
      (qParam ^ ((a : ℤ) * s * (2 * s + 1)) * quantumInt (4 * s + 1)).intDegree =
        4 * ((a : ℤ) * s * (2 * s + 1)) + (max (2 * (4 * s + 1)) (-(2 * (4 * s + 1))) - 2) :=
    fun s ↦ intDegree_mul_eq ⟨zpow_ne_zero _ qParam_ne_zero, intDegree_qParam_zpow _⟩
      (intDegree_quantumInt_torusOdd (by omega))
  have ha0 : (0 : ℤ) ≤ a := Int.natCast_nonneg a
  have hsum : ∑ s ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        qParam ^ ((a : ℤ) * s * (2 * s + 1)) * quantumInt (4 * s + 1) ≠ 0 ∧
      (∑ s ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        qParam ^ ((a : ℤ) * s * (2 * s + 1)) * quantumInt (4 * s + 1)).intDegree =
        8 * (a : ℤ) * (n : ℤ) ^ 2 + 4 * a * n + 8 * n := by
    refine intDegree_sum_eq_of_lt (a := (n : ℤ))
      (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩) ⟨(hterm n).1, ?_⟩ fun s hs hsn ↦ Or.inr ?_
    · rw [(hterm n).2, max_eq_left (by omega)]
      ring
    · rw [(hterm s).2]
      obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.mp hs
      have hs3 : s < n := lt_of_le_of_ne hs2 hsn
      have h1 : 0 ≤ (a : ℤ) * (((n : ℤ) - s) * ((n : ℤ) + s)) :=
        mul_nonneg ha0 (mul_nonneg (by omega) (by omega))
      have h2 : 0 ≤ (a : ℤ) * ((n : ℤ) - s) := mul_nonneg ha0 (by omega)
      rcases le_or_gt 0 s with h0 | h0
      · rw [max_eq_left (by omega)]
        nlinarith
      · rw [max_eq_right (by omega)]
        nlinarith
  have h := intDegree_mul_eq
    ⟨zpow_ne_zero (-(2 * (a : ℤ) * (n : ℤ) * ((n : ℤ) + 1))) qParam_ne_zero,
      intDegree_qParam_zpow _⟩ hsum
  refine ⟨h.1, h.2.trans ?_⟩
  ring

end AJConjecture
