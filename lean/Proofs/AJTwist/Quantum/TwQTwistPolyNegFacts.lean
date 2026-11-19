import Mathlib
import AJFamily.Quantum.TwistPolyBasic
import AJTwist.Quantum.TwQTwistPolyNeg

/-!
# Degree, leading and constant coefficient of `C_b` (Unit Q3)

Source: revision 5, Section 5.1 (`operators.tex`, "Retention of the shift endpoints"): "It
follows that `C_b` is monic of degree `2b - 1`, has constant `x^(4b-1)`, and
`C_b(x, -x) = x^b (x² - 1)^(2b-1)`. For the constant induction use
`Z_num(x, 0) = x² (x² + 1)`."

Route: joint induction along the recurrence `twistPolyNeg_one`, `twistPolyNeg_two`,
`twistPolyNeg_add_three` (as `natDegree_coeff_twistPoly_pair` in
`AJFamily/Quantum/TwistPolyBasic.lean`). Checked exactly for `b ≤ 6` (scratch
`check_symbol_mod.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value of `Ẑ` at any `r`. -/
private theorem eval_zetaMoebiusM_twistPolyNegFacts (r : ℤ[X]) :
    zetaMoebiusM.eval r = (X ^ 4 + 1) * r ^ 2 -
      (X ^ 8 - 2 * X ^ 6 - 2 * X ^ 4 - 2 * X ^ 2 + 1) * r + X ^ 4 * (X ^ 4 + 1) := by
  rw [zetaMoebiusM_eq_explicit]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X]

/-- The value of `C_1` at any `r`. -/
private theorem eval_twistPolyNeg_one_twistPolyNegFacts (r : ℤ[X]) :
    (twistPolyNeg 1).eval r = r + X ^ 6 := by
  rw [twistPolyNeg_one, eval_add, eval_X, eval_C]

/-- The value of `C_2` at any `r`, from the recurrence. -/
private theorem eval_twistPolyNeg_two_twistPolyNegFacts (r : ℤ[X]) :
    (twistPolyNeg 2).eval r =
      zetaMoebiusM.eval r * (twistPolyNeg 1).eval r - X ^ 4 * (X ^ 2 + r) ^ 3 := by
  rw [twistPolyNeg_two]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X]

/-- The value of `C_(k+3)` at any `r`, from the recurrence. -/
private theorem eval_twistPolyNeg_add_three_twistPolyNegFacts (r : ℤ[X]) (k : ℕ) :
    (twistPolyNeg (k + 3)).eval r = zetaMoebiusM.eval r * (twistPolyNeg (k + 2)).eval r -
      X ^ 4 * (X ^ 2 + r) ^ 4 * (twistPolyNeg (k + 1)).eval r := by
  rw [twistPolyNeg_add_three]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X]

/-- `C_(k+1)(M, 0) = M^(8k+6)`, two consecutive indices at a time. -/
private theorem eval_zero_twistPolyNeg_pair_twistPolyNegFacts (k : ℕ) :
    (twistPolyNeg (k + 1)).eval 0 = X ^ (8 * k + 6) ∧
      (twistPolyNeg (k + 2)).eval 0 = X ^ (8 * (k + 1) + 6) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [eval_twistPolyNeg_one_twistPolyNegFacts]
      ring
    · rw [eval_twistPolyNeg_two_twistPolyNegFacts, eval_twistPolyNeg_one_twistPolyNegFacts,
        eval_zetaMoebiusM_twistPolyNegFacts]
      ring
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [eval_twistPolyNeg_add_three_twistPolyNegFacts, ih.1, ih.2,
      eval_zetaMoebiusM_twistPolyNegFacts]
    ring

/-- `C_(k+1)(x, -x) = x^(k+1) (x² - 1)^(2k+1)`, two consecutive indices at a time. -/
private theorem eval_neg_twistPolyNeg_pair_twistPolyNegFacts (k : ℕ) :
    (twistPolyNeg (k + 1)).eval (-(X ^ 2)) = X ^ (2 * (k + 1)) * (X ^ 4 - 1) ^ (2 * k + 1) ∧
      (twistPolyNeg (k + 2)).eval (-(X ^ 2)) =
        X ^ (2 * (k + 1 + 1)) * (X ^ 4 - 1) ^ (2 * (k + 1) + 1) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [eval_twistPolyNeg_one_twistPolyNegFacts]
      ring
    · rw [eval_twistPolyNeg_two_twistPolyNegFacts, eval_twistPolyNeg_one_twistPolyNegFacts,
        eval_zetaMoebiusM_twistPolyNegFacts]
      ring
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [eval_twistPolyNeg_add_three_twistPolyNegFacts, ih.1, ih.2,
      eval_zetaMoebiusM_twistPolyNegFacts]
    ring

/-- `Ẑ` has degree at most `2` in `L`. -/
private theorem natDegree_zetaMoebiusM_le_twistPolyNegFacts : zetaMoebiusM.natDegree ≤ 2 := by
  rw [zetaMoebiusM_eq_explicit]
  compute_degree

/-- The coefficient of `L²` in `Ẑ` is `x² + 1`. -/
private theorem coeff_two_zetaMoebiusM_twistPolyNegFacts : zetaMoebiusM.coeff 2 = X ^ 4 + 1 := by
  rw [zetaMoebiusM_eq_explicit]
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

/-- Degree bound and top coefficient of `x² (L + x)^e`. -/
private theorem natDegree_coeff_padding_twistPolyNegFacts (e : ℕ) :
    (C (X ^ 4 : ℤ[X]) * (C (X ^ 2) + X) ^ e).natDegree ≤ e ∧
      (C (X ^ 4 : ℤ[X]) * (C (X ^ 2) + X) ^ e).coeff e = X ^ 4 := by
  refine ⟨?_, ?_⟩
  · compute_degree
  · rw [coeff_C_mul, add_comm, coeff_X_add_C_pow]
    simp

/-- Degree bound and top coefficient of `C_(k+1)`, two consecutive indices at a time. -/
private theorem natDegree_coeff_twistPolyNeg_pair_twistPolyNegFacts (k : ℕ) :
    ((twistPolyNeg (k + 1)).natDegree ≤ 2 * k + 1 ∧
        (twistPolyNeg (k + 1)).coeff (2 * k + 1) = 1) ∧
      ((twistPolyNeg (k + 2)).natDegree ≤ 2 * (k + 1) + 1 ∧
        (twistPolyNeg (k + 2)).coeff (2 * (k + 1) + 1) = 1) := by
  have hZd := natDegree_zetaMoebiusM_le_twistPolyNegFacts
  have hZc := coeff_two_zetaMoebiusM_twistPolyNegFacts
  have h1 : (twistPolyNeg 1).natDegree ≤ 1 ∧ (twistPolyNeg 1).coeff 1 = 1 := by
    rw [twistPolyNeg_one]
    refine ⟨by compute_degree, ?_⟩
    rw [coeff_add, coeff_X_one, coeff_C_succ, add_zero]
  induction k with
  | zero =>
    refine ⟨h1, ?_⟩
    obtain ⟨hFd, hFc⟩ := natDegree_coeff_padding_twistPolyNegFacts 3
    rw [twistPolyNeg_two]
    refine ⟨(natDegree_sub_le _ _).trans (max_le (natDegree_mul_le_of_le hZd h1.1) hFd), ?_⟩
    rw [coeff_sub, show 2 * (0 + 1) + 1 = 2 + 1 from rfl,
      coeff_mul_add_eq_of_natDegree_le hZd h1.1, hZc, h1.2, hFc]
    ring
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    obtain ⟨⟨hd0, hc0⟩, hd1, hc1⟩ := ih
    obtain ⟨hFd, hFc⟩ := natDegree_coeff_padding_twistPolyNegFacts 4
    have e1 : 2 * (k + 1 + 1) + 1 = 2 + (2 * (k + 1) + 1) := by ring
    have e2 : 2 * (k + 1 + 1) + 1 = 4 + (2 * k + 1) := by ring
    rw [show k + 1 + 2 = k + 3 from rfl, twistPolyNeg_add_three]
    refine ⟨?_, ?_⟩
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · rw [e1]
        exact natDegree_mul_le_of_le hZd hd1
      · rw [e2]
        exact natDegree_mul_le_of_le hFd hd0
    · rw [coeff_sub, e1, coeff_mul_add_eq_of_natDegree_le hZd hd1, ← e1, e2,
        coeff_mul_add_eq_of_natDegree_le hFd hd0, hZc, hc1, hFc, hc0]
      ring

/-- `C_b` has degree `2b - 1` in `L`. -/
theorem natDegree_twistPolyNeg (b : ℕ) (hb : 1 ≤ b) : (twistPolyNeg b).natDegree = 2 * b - 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hb
  obtain ⟨⟨hd, hc⟩, -⟩ := natDegree_coeff_twistPolyNeg_pair_twistPolyNegFacts n
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  refine natDegree_eq_of_le_of_coeff_ne_zero hd ?_
  rw [hc]
  exact one_ne_zero

/-- `C_b` is monic in `L`. -/
theorem monic_twistPolyNeg (b : ℕ) (hb : 1 ≤ b) : (twistPolyNeg b).Monic := by
  rw [Monic, leadingCoeff, natDegree_twistPolyNeg b hb]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hb
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  exact (natDegree_coeff_twistPolyNeg_pair_twistPolyNegFacts n).1.2

/-- The constant coefficient of `C_b` is `x^(4b-1) = M^(8b-2)`. -/
theorem coeff_zero_twistPolyNeg (b : ℕ) (hb : 1 ≤ b) :
    (twistPolyNeg b).coeff 0 = X ^ (8 * b - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hb
  rw [coeff_zero_eq_eval_zero, (eval_zero_twistPolyNeg_pair_twistPolyNegFacts n).1,
    show 8 * (n + 1) - 2 = 8 * n + 6 by omega]

/-- `C_b(x, -x) = x^b (x² - 1)^(2b-1)`. -/
theorem eval_neg_twistPolyNeg (b : ℕ) (hb : 1 ≤ b) :
    (twistPolyNeg b).eval (-(X ^ 2)) = X ^ (2 * b) * (X ^ 4 - 1) ^ (2 * b - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hb
  rw [(eval_neg_twistPolyNeg_pair_twistPolyNegFacts n).1,
    show 2 * (n + 1) - 1 = 2 * n + 1 by omega]

end AJConjecture
