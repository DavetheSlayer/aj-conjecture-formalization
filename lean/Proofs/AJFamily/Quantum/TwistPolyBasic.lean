import Mathlib
import AJFamily.Quantum.TwistPoly

/-!
# Basic properties of the twist polynomial

Degree, leading and constant coefficients of `B_k`, and its values at `L = 1` and `L = -M²`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- Explicit form of `Ẑ = zetaMoebiusM` in `ℤ[M][L]`. -/
theorem zetaMoebiusM_eq_explicit :
    zetaMoebiusM = C (X ^ 4 + 1) * X ^ 2 - C (X ^ 8 - 2 * X ^ 6 - 2 * X ^ 4 - 2 * X ^ 2 + 1) * X
      + C (X ^ 4 * (X ^ 4 + 1)) := by
  simp only [zetaMoebiusM, symbolZetaMoebius, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, coe_compRingHom_apply]
  simp only [add_comp, sub_comp, mul_comp, pow_comp, X_comp, one_comp, ofNat_comp]
  push_cast
  ring_nf

/-- Explicit form of `B_1`. -/
theorem twistPoly_one_eq_explicit :
    twistPoly 1 = C (X ^ 4) * X ^ 2 + C (-X ^ 8 + X ^ 6 + 2 * X ^ 4 + X ^ 2 - 1) * X
      + C (X ^ 4) := by
  rw [twistPoly, zetaMoebiusM_eq_explicit]
  simp only [C_add, C_mul, C_pow, C_sub, C_neg, C_1, C_ofNat]
  ring

/-- The value of `B_(k+2)` at any `r`, from the recursion. -/
private theorem eval_twistPoly_add_two (r : ℤ[X]) (k : ℕ) :
    (twistPoly (k + 2)).eval r = zetaMoebiusM.eval r * (twistPoly (k + 1)).eval r -
      X ^ 4 * (X ^ 2 + r) ^ 4 * (twistPoly k).eval r := by
  rw [twistPoly]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X]

/-- The value of `Ẑ` at any `r`. -/
private theorem eval_zetaMoebiusM (r : ℤ[X]) :
    zetaMoebiusM.eval r = (X ^ 4 + 1) * r ^ 2 -
      (X ^ 8 - 2 * X ^ 6 - 2 * X ^ 4 - 2 * X ^ 2 + 1) * r + X ^ 4 * (X ^ 4 + 1) := by
  rw [zetaMoebiusM_eq_explicit]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X]

/-- The value of `B_1` at any `r`. -/
private theorem eval_twistPoly_one (r : ℤ[X]) :
    (twistPoly 1).eval r = X ^ 4 * r ^ 2 + (-X ^ 8 + X ^ 6 + 2 * X ^ 4 + X ^ 2 - 1) * r
      + X ^ 4 := by
  rw [twistPoly_one_eq_explicit]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X]

/-- `B_k(M, 0) = M^(4k)`, two consecutive indices at a time. -/
private theorem eval_zero_twistPoly_pair (k : ℕ) :
    (twistPoly k).eval 0 = X ^ (4 * k) ∧ (twistPoly (k + 1)).eval 0 = X ^ (4 * (k + 1)) := by
  induction k with
  | zero =>
    refine ⟨by simp [twistPoly], ?_⟩
    rw [eval_twistPoly_one]
    ring
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [eval_twistPoly_add_two, ih.1, ih.2, eval_zetaMoebiusM]
    ring

/-- `B_k(M, -x) = x^k (1 - x²)^(2k)`, two consecutive indices at a time. -/
private theorem eval_neg_twistPoly_pair (k : ℕ) :
    (twistPoly k).eval (-(X ^ 2)) = X ^ (2 * k) * (1 - X ^ 4) ^ (2 * k) ∧
      (twistPoly (k + 1)).eval (-(X ^ 2)) = X ^ (2 * (k + 1)) * (1 - X ^ 4) ^ (2 * (k + 1)) := by
  induction k with
  | zero =>
    refine ⟨by simp [twistPoly], ?_⟩
    rw [eval_twistPoly_one]
    ring
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [eval_twistPoly_add_two, ih.1, ih.2, eval_zetaMoebiusM]
    ring

/-- `B_(k+1)(M, 1)` in closed form, two consecutive indices at a time. -/
private theorem eval_one_twistPoly_pair (k : ℕ) :
    (twistPoly (k + 1)).eval 1 = -(X ^ (2 * k) * (1 + X ^ 2) ^ (2 * (k + 1)) *
      (((k : ℤ[X]) + 1) * X ^ 4 - (2 * ((k : ℤ[X]) + 1) + 1) * X ^ 2 + ((k : ℤ[X]) + 1))) ∧
    (twistPoly (k + 2)).eval 1 = -(X ^ (2 * (k + 1)) * (1 + X ^ 2) ^ (2 * (k + 2)) *
      (((k : ℤ[X]) + 2) * X ^ 4 - (2 * ((k : ℤ[X]) + 2) + 1) * X ^ 2 +
        ((k : ℤ[X]) + 2))) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [eval_twistPoly_one]
      push_cast
      ring
    · rw [eval_twistPoly_add_two, eval_twistPoly_one, eval_zetaMoebiusM]
      simp only [twistPoly, eval_one]
      push_cast
      ring
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · rw [ih.2]
      push_cast
      ring
    · rw [eval_twistPoly_add_two, ih.1, ih.2, eval_zetaMoebiusM]
      push_cast
      ring

/-- Degree bound and top coefficient of `B_k`, two consecutive indices at a time. -/
private theorem natDegree_coeff_twistPoly_pair (k : ℕ) :
    ((twistPoly k).natDegree ≤ 2 * k ∧ (twistPoly k).coeff (2 * k) = X ^ (4 * k)) ∧
      ((twistPoly (k + 1)).natDegree ≤ 2 * (k + 1) ∧
        (twistPoly (k + 1)).coeff (2 * (k + 1)) = X ^ (4 * (k + 1))) := by
  induction k with
  | zero =>
    refine ⟨by simp [twistPoly], ?_, ?_⟩
    · rw [twistPoly_one_eq_explicit]
      compute_degree
    · rw [twistPoly_one_eq_explicit]
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
      norm_num
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    obtain ⟨⟨hd0, hc0⟩, hd1, hc1⟩ := ih
    have hZd : zetaMoebiusM.natDegree ≤ 2 := by
      rw [zetaMoebiusM_eq_explicit]
      compute_degree
    have hZc : zetaMoebiusM.coeff 2 = X ^ 4 + 1 := by
      rw [zetaMoebiusM_eq_explicit]
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
      norm_num
    have hFd : (C (X ^ 4 : ℤ[X]) * (C (X ^ 2) + X) ^ 4).natDegree ≤ 4 := by
      compute_degree
    have hFc : (C (X ^ 4 : ℤ[X]) * (C (X ^ 2) + X) ^ 4).coeff 4 = X ^ 4 := by
      rw [coeff_C_mul, add_comm, coeff_X_add_C_pow]
      simp
    have e1 : 2 * (k + 1 + 1) = 2 + 2 * (k + 1) := by ring
    have e2 : 2 * (k + 1 + 1) = 4 + 2 * k := by ring
    rw [twistPoly]
    refine ⟨?_, ?_⟩
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · rw [e1]
        exact natDegree_mul_le_of_le hZd hd1
      · rw [e2]
        exact natDegree_mul_le_of_le hFd hd0
    · rw [coeff_sub, e1, coeff_mul_add_eq_of_natDegree_le hZd hd1, ← e1, e2,
        coeff_mul_add_eq_of_natDegree_le hFd hd0, hZc, hc1, hFc, hc0]
      ring

/-- `B_k` has degree `2k` in `L`. -/
theorem natDegree_twistPoly (k : ℕ) : (twistPoly k).natDegree = 2 * k := by
  obtain ⟨⟨hd, hc⟩, -⟩ := natDegree_coeff_twistPoly_pair k
  refine natDegree_eq_of_le_of_coeff_ne_zero hd ?_
  rw [hc]
  exact pow_ne_zero _ X_ne_zero

/-- The leading coefficient of `B_k` is `M^(4k)`. -/
theorem leadingCoeff_twistPoly (k : ℕ) : (twistPoly k).leadingCoeff = X ^ (4 * k) := by
  rw [leadingCoeff, natDegree_twistPoly]
  exact (natDegree_coeff_twistPoly_pair k).1.2

/-- The constant coefficient of `B_k` is `M^(4k)`. -/
theorem coeff_zero_twistPoly (k : ℕ) : (twistPoly k).coeff 0 = X ^ (4 * k) := by
  rw [coeff_zero_eq_eval_zero]
  exact (eval_zero_twistPoly_pair k).1

/-- `B_k(M, 1) = -M^(2k-2) (1 + M²)^(2k) (k M⁴ - (2k+1) M² + k)` for `k ≥ 1`. -/
theorem eval_one_twistPoly {k : ℕ} (hk : 1 ≤ k) :
    (twistPoly k).eval 1 = -(X ^ (2 * (k - 1)) * (1 + X ^ 2) ^ (2 * k) *
      (C (k : ℤ) * X ^ 4 - C (2 * (k : ℤ) + 1) * X ^ 2 + C (k : ℤ))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [(eval_one_twistPoly_pair n).1, Nat.add_sub_cancel]
  simp only [map_add, map_mul, map_natCast, map_one, map_ofNat]
  push_cast
  ring

/-- `B_k(M, -M²) = M^(2k) (1 - M⁴)^(2k)`. -/
theorem eval_neg_twistPoly (k : ℕ) :
    (twistPoly k).eval (-(X ^ 2)) = X ^ (2 * k) * (1 - X ^ 4) ^ (2 * k) :=
  (eval_neg_twistPoly_pair k).1

end AJConjecture
