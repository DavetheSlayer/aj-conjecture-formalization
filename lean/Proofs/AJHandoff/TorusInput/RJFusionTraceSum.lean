import Mathlib
import AJHandoff.TorusInput.RJDefs
import AJConjecture.SkeinJwTrace
import AJConjecture.SkeinJwAbsorb
import AJConjecture.SkeinTurnbackEigenBasic

/-!
# Traces for the completeness of the fusion (node RA1.11)

`qtr (f_a ⊗ f_b) = Δ_a Δ_b` and the Clebsch–Gordan identity
`∑_(j ≤ min a b) Δ_(a+b-2j) = Δ_a Δ_b` (`Δ_k = (-1)^k [k+1]`).

Route. The trace of a tensor product of placements is the product of the traces
(`qtr` of `skPlace`: split the states, `qtr_jwAt`); or close the second bundle first
(`qtr_eq_qtr_ptrTail`, iterate `ptrTail_jwAt`). The identity: `(-1)^(a+b-2j) = (-1)^(a+b)`, and
`∑_(j=0)^(min a b) [a+b+1-2j] = [a+1][b+1]` by induction on `min a b` with
`quantumInt_mul_shift_sub`, or by multiplying by `t² - t⁻²` and telescoping. Estimate 80–130
lines.
-/

noncomputable section

namespace AJConjecture

/-- An operator on `V^{⊗ 0}` is its quantum trace times the identity. -/
private theorem rj_skMat_zero_eq_qtr_smul_one (M : SkMat 0 0) : M = qtr 0 M • 1 := by
  ext x y
  have hxy : x = y := Subsingleton.elim x y
  subst hxy
  simp [qtr, skWeight, Matrix.trace, Subsingleton.elim _ x]

/-- Closing the second bundle of `1_a ⊗ f_b` gives `Δ_b`. -/
private theorem rj_ptrTail_jwAt_shift (a b : ℕ) :
    ptrTail a (a + b) (jwAt (a + b) a b) = loopScalar b • (1 : SkMat a a) := by
  have h := ptrTail_skPlace_shift a 0 b (by omega) (jwAt b 0 b)
  simp only [Nat.add_zero] at h
  rw [jwAt_eq_skPlace (a + b) a b le_rfl, h, rj_skMat_zero_eq_qtr_smul_one (ptrTail 0 b _),
    ← qtr_eq_qtr_ptrTail 0 b (by omega), qtr_jwAt, skPlace_smul, skPlace_one a a 0 (by omega)]

/-- `[1] = 1`. -/
private theorem rj_quantumInt_one : quantumInt 1 = 1 := by
  rw [quantumInt]
  exact div_self (by simpa using claspAlg_ratFuncX_sq_sub_ne_zero)

/-- `∑_(j ≤ m) [a+b+1-2j] = [a+1][b+1] - [a-m][b-m]`. -/
private theorem rj_sum_quantumInt_telescope (a b : ℤ) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), quantumInt (a + b + 1 - 2 * j) =
      quantumInt (a + 1) * quantumInt (b + 1) - quantumInt (a - m) * quantumInt (b - m) := by
  induction m with
  | zero =>
    have h := quantumInt_mul_shift_sub a b 1
    rw [rj_quantumInt_one, one_mul] at h
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero,
      sub_zero, h]
  | succ m ih =>
    have h := quantumInt_mul_shift_sub (a - m - 1) (b - m - 1) 1
    rw [rj_quantumInt_one, one_mul] at h
    rw [Finset.sum_range_succ, ih]
    push_cast
    rw [show a - m - 1 + 1 = a - m by ring, show b - m - 1 + 1 = b - m by ring] at h
    rw [show a + b + 1 - 2 * ((m : ℤ) + 1) = a - m - 1 + (b - m - 1) + 1 by ring, ← h,
      show a - ((m : ℤ) + 1) = a - m - 1 by ring, show b - ((m : ℤ) + 1) = b - m - 1 by ring]
    ring

/-- The quantum trace of `f_a ⊗ f_b`. -/
theorem rj_qtr_bundleProj (a b : ℕ) :
    qtr (a + b) (rjBundleProj a b) = loopScalar a * loopScalar b := by
  rw [rjBundleProj, jwAt_eq_skPlace (a + b) 0 a (by omega), qtr_eq_qtr_ptrTail a (a + b) (by omega),
    ptrTail_skPlace_mul a (a + b) (by omega), rj_ptrTail_jwAt_shift, Matrix.mul_smul,
    Matrix.mul_one, qtr_smul, qtr_jwAt, mul_comm]

/-- The Clebsch–Gordan identity for the loop scalars. -/
theorem rj_sum_loopScalar (a b : ℕ) :
    ∑ j ∈ Finset.range (min a b + 1), loopScalar (a + b - 2 * j) = loopScalar a * loopScalar b := by
  have h := rj_sum_quantumInt_telescope a b (min a b)
  have h0 : quantumInt ((a : ℤ) - (min a b : ℕ)) * quantumInt ((b : ℤ) - (min a b : ℕ)) = 0 := by
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab, sub_self]; simp [quantumInt]
    · rw [min_eq_right hab, sub_self]; simp [quantumInt]
  rw [h0, sub_zero] at h
  have hterm : ∀ j ∈ Finset.range (min a b + 1), loopScalar (a + b - 2 * j) =
      (-1) ^ (a + b) * quantumInt ((a : ℤ) + b + 1 - 2 * j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hle : 2 * j ≤ a + b := by omega
    rw [loopScalar]
    congr 1
    · obtain ⟨e, he⟩ : ∃ e, a + b = e + 2 * j := ⟨a + b - 2 * j, by omega⟩
      rw [he, Nat.add_sub_cancel, pow_add, pow_mul]
      norm_num
    · congr 1
      push_cast [hle]
      ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, h, loopScalar, loopScalar, pow_add]
  ring

end AJConjecture
