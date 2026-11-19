import Mathlib
import AJConjecture.QAlgOpApplyFieldBasic
import AJConjecture.QAlgEvalAtFieldZeros
import AJTwist.Quantum.TwQBarBasic

/-!
# Transport of annihilators under the bar involution

Source: revision 5, Section 8.2 (`conclusion.tex`, "Transport under the satellite mirror"):
`Φ_{S^*}(N; t) = Φ_S(N; t⁻¹)`, and a recurrence of `Φ_S` becomes one of `Φ_{S^*}` after the
substitution `(t, M) ↦ (t⁻¹, M⁻¹)` in its coefficients. Only the existence part is needed here:
if a sequence `f : ℤ → ℚ(t)` has a nonzero annihilator, so has `n ↦ \bar{f(n)}`
(`twQBar`, `t ↦ t⁻¹`).

* `twHBarCoeff A B c = t^A M^B c(t⁻¹, M⁻¹)` for a coefficient `c ∈ ℤ[t][M]` of degree at most
  `A` in `t` and at most `B` in `M` (two reflections); then
  `(twHBarCoeff A B c)(t, t^(2n)) = t^(A + 2nB) \bar{c(t, t^(2n))}` (`evalAtField_twHBarCoeff`;
  `Polynomial.eval₂_reflect_mul_pow` or a direct expansion in monomials, `twQBar_X_zpow`).
* `twHBarOp A B P` applies this to every coefficient of an operator; with `A`, `B` bounding
  the degrees of all coefficients of `P`,
  `(twHBarOp A B P · \bar f)(n) = t^(A + 2nB) \bar{(P f)(n)}`, and `twHBarOp A B P ≠ 0` when
  `P ≠ 0` (a nonzero coefficient `c` has `c(t, t^(2n)) ≠ 0` for large `n`,
  `exists_forall_ge_evalAtField_ne_zero`). This is `twH_exists_barOp`.
* `twH_exists_annihilator_bar`: the transport of the existence statement.

The mirror-transport package needs the finer statement that the transport preserves
primitivity, the order and the specialization at `t = -1`; if it defines its own operator
involution, `twH_exists_annihilator_bar` is a corollary of it and this file can be dropped.

Checked in exact arithmetic on random operators (scratch `H/h04_bar.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `t^A M^B c(t⁻¹, M⁻¹)`: the coefficient `c` reflected in both variables. -/
def twHBarCoeff (A B : ℕ) (c : Coeff) : Coeff :=
  ∑ b ∈ Finset.range (B + 1), monomial (B - b) (Polynomial.reflect A (c.coeff b))

/-- The operator whose coefficients are the reflections of those of `P`. -/
def twHBarOp (A B : ℕ) (P : RecOp) : RecOp :=
  ∑ i ∈ Finset.range (P.natDegree + 1), monomial i (twHBarCoeff A B (P.coeff i))

/-- The coefficient map `ℤ[t] → ℚ(t)` on a reflected polynomial: `t^A` times the bar. -/
private theorem eval₂_reflect_twHBar (A : ℕ) (p : ℤ[X]) (hp : p.natDegree ≤ A) :
    eval₂ (Int.castRingHom (RatFunc ℚ)) RatFunc.X (reflect A p) =
      RatFunc.X ^ A * twQBar (eval₂ (Int.castRingHom (RatFunc ℚ)) RatFunc.X p) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hr : (reflect A p).natDegree < A + 1 :=
    Nat.lt_succ_of_le (natDegree_reflect_le.trans (max_le le_rfl hp))
  rw [eval₂_eq_sum_range' _ hr, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hp), map_sum,
    Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ A := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.add_sub_cancel, coeff_reflect, revAt_le (Nat.sub_le A i), Nat.sub_sub_self hi',
    map_mul, map_pow, twQBar_X, eq_intCast, map_intCast, pow_sub₀ _ hX hi', inv_pow]
  ring

/-- The value of a reflected coefficient at the colour `n` is `t^(A + 2nB)` times the bar of
the value of the coefficient. -/
theorem evalAtField_twHBarCoeff (A B : ℕ) (c : Coeff) (hA : ∀ b, (c.coeff b).natDegree ≤ A)
    (hB : c.natDegree ≤ B) (n : ℤ) :
    evalAtField n (twHBarCoeff A B c) =
      RatFunc.X ^ ((A : ℤ) + 2 * n * B) * twQBar (evalAtField n c) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hc : evalAtField n c = ∑ b ∈ Finset.range (B + 1),
      eval₂ (Int.castRingHom (RatFunc ℚ)) RatFunc.X (c.coeff b) * (RatFunc.X ^ (2 * n)) ^ b :=
    eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hB) _
  rw [hc, map_sum, Finset.mul_sum, twHBarCoeff, map_sum]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  have hb' : b ≤ B := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  have hm : evalAtField n (monomial (B - b) (reflect A (c.coeff b))) =
      eval₂ (Int.castRingHom (RatFunc ℚ)) RatFunc.X (reflect A (c.coeff b)) *
        (RatFunc.X ^ (2 * n)) ^ (B - b) := eval₂_monomial _ _
  have hpow : (RatFunc.X : RatFunc ℚ) ^ A * (RatFunc.X ^ (2 * n)) ^ (B - b) =
      RatFunc.X ^ ((A : ℤ) + 2 * n * B) * (RatFunc.X ^ (-(2 * n))) ^ b := by
    rw [← zpow_natCast (RatFunc.X ^ (2 * n)), ← zpow_natCast (RatFunc.X ^ (-(2 * n))),
      ← zpow_natCast RatFunc.X A, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hX, ← zpow_add₀ hX,
      Nat.cast_sub hb']
    congr 1
    ring
  rw [hm, eval₂_reflect_twHBar A _ (hA b), map_mul, map_pow, twQBar_X_zpow, mul_right_comm,
    hpow]
  ring

/-- The action is additive in the operator, for finite sums. -/
private theorem opApplyField_finsetSum_left_twHBar {ι : Type*} (s : Finset ι) (P : ι → RecOp)
    (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (∑ k ∈ s, P k) f n = ∑ k ∈ s, opApplyField (P k) f n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, opApplyField, sum_zero_index]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, opApplyField_add_left, ih]

/-- The reflected operator acts on the barred sequence as the bar of the action, up to a
monomial in `t`. -/
private theorem opApplyField_twHBarOp_twHBar (A B : ℕ) (P : RecOp)
    (hA : ∀ i b, ((P.coeff i).coeff b).natDegree ≤ A) (hB : ∀ i, (P.coeff i).natDegree ≤ B)
    (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (twHBarOp A B P) (fun m ↦ twQBar (f m)) n =
      RatFunc.X ^ ((A : ℤ) + 2 * n * B) * twQBar (opApplyField P f n) := by
  rw [twHBarOp, opApplyField_finsetSum_left_twHBar, opApplyField_eq_sum_range P f n, map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [opApplyField_monomial, evalAtField_twHBarCoeff A B _ (hA i) (hB i), map_mul, mul_assoc]

/-- The reflected operator of a nonzero operator is not zero. -/
private theorem twHBarOp_ne_zero_twHBar (A B : ℕ) (P : RecOp)
    (hA : ∀ i b, ((P.coeff i).coeff b).natDegree ≤ A) (hB : ∀ i, (P.coeff i).natDegree ≤ B)
    (hP : P ≠ 0) : twHBarOp A B P ≠ 0 := by
  intro h0
  have hlc : P.coeff P.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hP
  obtain ⟨n₀, hn₀⟩ := exists_forall_ge_evalAtField_ne_zero hlc
  have hcoeff : (twHBarOp A B P).coeff P.natDegree = twHBarCoeff A B (P.coeff P.natDegree) := by
    rw [twHBarOp, finsetSum_coeff, Finset.sum_eq_single P.natDegree]
    · rw [coeff_monomial_same]
    · intro k _ hk
      exact coeff_monomial_of_ne _ hk.symm
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h
  have h1 := evalAtField_twHBarCoeff A B _ (hA P.natDegree) (hB P.natDegree) n₀
  rw [← hcoeff, h0, coeff_zero, map_zero] at h1
  rcases mul_eq_zero.mp h1.symm with h2 | h2
  · exact zpow_ne_zero _ RatFunc.X_ne_zero h2
  · exact hn₀ n₀ le_rfl ((map_eq_zero twQBar).mp h2)

/-- Every operator has a bar transform: nonzero when the operator is, and acting on the barred
sequence as the bar of the action, up to a monomial in `t`. -/
theorem twH_exists_barOp (P : RecOp) :
    ∃ P' : RecOp, (P ≠ 0 → P' ≠ 0) ∧ ∃ A B : ℕ, ∀ (f : ℤ → RatFunc ℚ) (n : ℤ),
      opApplyField P' (fun m ↦ twQBar (f m)) n =
        RatFunc.X ^ ((A : ℤ) + 2 * n * B) * twQBar (opApplyField P f n) := by
  have hB : ∀ i, (P.coeff i).natDegree ≤ P.support.sup fun i ↦ (P.coeff i).natDegree := by
    intro i
    by_cases hi : i ∈ P.support
    · exact Finset.le_sup (f := fun i ↦ (P.coeff i).natDegree) hi
    · rw [notMem_support_iff.mp hi, natDegree_zero]
      exact Nat.zero_le _
  have hA : ∀ i b, ((P.coeff i).coeff b).natDegree ≤ P.support.sup fun i ↦
      (P.coeff i).support.sup fun b ↦ ((P.coeff i).coeff b).natDegree := by
    intro i b
    by_cases hi : i ∈ P.support
    · by_cases hb : b ∈ (P.coeff i).support
      · exact (Finset.le_sup (f := fun b ↦ ((P.coeff i).coeff b).natDegree) hb).trans
          (Finset.le_sup (f := fun i ↦
            (P.coeff i).support.sup fun b ↦ ((P.coeff i).coeff b).natDegree) hi)
      · rw [notMem_support_iff.mp hb, natDegree_zero]
        exact Nat.zero_le _
    · rw [notMem_support_iff.mp hi, coeff_zero, natDegree_zero]
      exact Nat.zero_le _
  exact ⟨twHBarOp _ _ P, twHBarOp_ne_zero_twHBar _ _ P hA hB, _, _,
    opApplyField_twHBarOp_twHBar _ _ P hA hB⟩

/-- A sequence with a nonzero annihilator has a barred sequence with a nonzero annihilator. -/
theorem twH_exists_annihilator_bar {f : ℤ → RatFunc ℚ}
    (h : ∃ Q : RecOp, Q ≠ 0 ∧ ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) f n = 0) :
    ∃ Q : RecOp, Q ≠ 0 ∧ ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (fun m ↦ twQBar (f m)) n = 0 := by
  obtain ⟨Q, hQ, c, hc, hann⟩ := h
  obtain ⟨P', hP', A, B, hact⟩ := twH_exists_barOp (Polynomial.C c * Q)
  refine ⟨P', hP' (mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hQ), 1, one_ne_zero, fun n ↦ ?_⟩
  rw [Polynomial.C_1, one_mul, hact, hann n, map_zero, mul_zero]

end AJConjecture
