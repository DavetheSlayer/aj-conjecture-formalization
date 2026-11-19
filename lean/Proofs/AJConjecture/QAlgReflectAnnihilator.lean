import Mathlib
import AJConjecture.QAlgEvalAtFieldZeros
import AJConjecture.QAlgOpApplyFieldBasic

/-!
# Reflection of an annihilator of an even sequence

If `G = ∑ g_k(t, M) L^k` of degree `r` annihilates an even sequence `f` at the colours
`n ≥ n₀`, the reflected operator `∑ g_(r-k)(t, t^(-2r) M⁻¹) L^k`, multiplied by a power of
`t^(2r) M` to clear denominators, annihilates `f` at the colours `n ≤ -n₀ - r`.
-/

open Polynomial

namespace AJConjecture

/-- The reflected coefficient `(t^(2r) M)^d g(t, t^(-2r) M⁻¹)` of a coefficient `g` of degree
at most `d` in `M`. -/
private noncomputable def reflectedCoeff (r d : ℕ) (g : Coeff) : Coeff :=
  ∑ i ∈ Finset.range (d + 1), C (g.coeff i) * (C (X ^ (2 * r)) * X) ^ (d - i)

/-- The value of the reflected coefficient at the colour `m` is, up to a unit, the value of the
coefficient at the colour `-m - r`. -/
private theorem evalAtField_reflectedCoeff (r d : ℕ) {g : Coeff} (hg : g.natDegree ≤ d) (m : ℤ) :
    evalAtField m (reflectedCoeff r d g) =
      (RatFunc.X ^ (2 * (m + r))) ^ d * evalAtField (-m - r) g := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hy : (RatFunc.X : RatFunc ℚ) ^ (2 * (m + r)) ≠ 0 := zpow_ne_zero _ hX
  have h1 : evalAtField (-m - r) g = ∑ i ∈ Finset.range (d + 1),
      eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X (g.coeff i) *
        (RatFunc.X ^ (2 * (-m - r))) ^ i := by
    simp only [evalAtField, coe_eval₂RingHom]
    exact eval₂_eq_sum_range' _ (by omega) _
  have e1 : (RatFunc.X : RatFunc ℚ) ^ (2 * r) * RatFunc.X ^ (2 * m) =
      RatFunc.X ^ (2 * (m + r)) := by
    rw [← zpow_natCast, ← zpow_add₀ hX]
    congr 1
    push_cast
    ring
  have e2 : (RatFunc.X : RatFunc ℚ) ^ (2 * (-m - r)) = (RatFunc.X ^ (2 * (m + r)))⁻¹ := by
    rw [← zpow_neg]
    congr 1
    ring
  rw [h1, Finset.mul_sum, reflectedCoeff, map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  obtain ⟨k, rfl⟩ : ∃ k, d = i + k := ⟨d - i, by rw [Finset.mem_range] at hi; omega⟩
  simp only [evalAtField, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow]
  rw [e1, e2, Nat.add_sub_cancel_left, pow_add, inv_pow]
  field_simp

/-- The reflected coefficient of a nonzero coefficient is not zero. -/
private theorem reflectedCoeff_ne_zero (r d : ℕ) {g : Coeff} (hg : g.natDegree ≤ d)
    (h0 : g ≠ 0) : reflectedCoeff r d g ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_forall_ge_evalAtField_ne_zero h0
  intro hzero
  have h1 := evalAtField_reflectedCoeff r d hg (-n - r)
  rw [hzero, map_zero] at h1
  have h2 : evalAtField (-(-n - (r : ℤ)) - r) g ≠ 0 := hn _ (by omega)
  exact mul_ne_zero (pow_ne_zero _ (zpow_ne_zero _ RatFunc.X_ne_zero)) h2 h1.symm

/-- The action of an operator given by its coefficients. -/
private theorem opApplyField_sum_range_monomial (N : ℕ) (c : ℕ → Coeff) (f : ℤ → RatFunc ℚ)
    (n : ℤ) :
    opApplyField (∑ j ∈ Finset.range N, monomial j (c j)) f n =
      ∑ j ∈ Finset.range N, evalAtField n (c j) * f (n + j) := by
  induction N with
  | zero => simp [opApplyField]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, opApplyField_add_left, ih,
      opApplyField_monomial]

/-- An annihilator of the positive tail of an even sequence gives an annihilator of its
negative tail. -/
theorem exists_annihilator_neg_tail_of_even {f : ℤ → RatFunc ℚ} (hf : ∀ n : ℤ, f (-n) = f n)
    {G : RecOp} (hG : G ≠ 0) {n₀ : ℤ} (h : ∀ n : ℤ, n₀ ≤ n → opApplyField G f n = 0) :
    ∃ G' : RecOp, G' ≠ 0 ∧ ∀ n : ℤ, n ≤ -n₀ - G.natDegree → opApplyField G' f n = 0 := by
  set r : ℕ := G.natDegree with hr
  set d : ℕ := (Finset.range (r + 1)).sup fun k ↦ (G.coeff k).natDegree with hd
  have hdeg : ∀ j ∈ Finset.range (r + 1), (G.coeff (r - j)).natDegree ≤ d := fun j _ ↦
    Finset.le_sup (f := fun k ↦ (G.coeff k).natDegree) (Finset.mem_range.mpr (by omega))
  refine ⟨∑ j ∈ Finset.range (r + 1), monomial j (reflectedCoeff r d (G.coeff (r - j))),
    fun hzero ↦ ?_, fun m hm ↦ ?_⟩
  · have h0 : (∑ j ∈ Finset.range (r + 1),
        monomial j (reflectedCoeff r d (G.coeff (r - j)))).coeff 0 = 0 := by
      rw [hzero, coeff_zero]
    rw [finsetSum_coeff, Finset.sum_eq_single 0
      (fun j _ hj ↦ coeff_monomial_of_ne _ (Ne.symm hj))
      (fun h ↦ absurd (Finset.mem_range.mpr (Nat.succ_pos r)) h), coeff_monomial_same] at h0
    exact reflectedCoeff_ne_zero r d (hdeg 0 (Finset.mem_range.mpr (Nat.succ_pos r)))
      (by rw [Nat.sub_zero, hr, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hG) h0
  · have hann := h (-m - r) (by omega)
    rw [opApplyField_eq_sum_range, ← hr, ← Finset.sum_range_reflect] at hann
    rw [opApplyField_sum_range_monomial]
    have hmul := congrArg (fun x ↦ (RatFunc.X ^ (2 * (m + r))) ^ d * x) hann
    simp only [mul_zero, Finset.mul_sum] at hmul
    rw [← hmul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [evalAtField_reflectedCoeff r d (hdeg j hj), mul_assoc]
    have hj' : j ≤ r := by rw [Finset.mem_range] at hj; omega
    have harg : -m - (r : ℤ) + ((r + 1 - 1 - j : ℕ) : ℤ) = -(m + j) := by
      rw [Nat.add_sub_cancel, Nat.cast_sub hj']
      ring
    rw [harg, hf, Nat.add_sub_cancel]

end AJConjecture
