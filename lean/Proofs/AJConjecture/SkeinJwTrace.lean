import Mathlib
import AJConjecture.SkeinJwCupCap
import AJConjecture.SkeinJwAbsorb
import AJConjecture.SkeinPtrTailBasic
import AJConjecture.SkeinPtrTailPlace
import AJConjecture.SkeinScalars

/-!
# Traces of the Jones–Wenzl projector

The partial trace of `f_{k+1}` over its last strand is `(Δ_{k+1}/Δ_k) f_k = -([k+2]/[k+1]) f_k`
(Wenzl's recursion, `ptr(e_k) = 1`, `ptr(1) = δ` and `[2][k+1] = [k+2] + [k]`), hence
`qtr f_k = Δ_k = (-1)^k [k+1]` by induction, with `qtr = qtr ∘ ptr`.
-/

namespace AJConjecture

/-- The linear system `x P + x⁻¹ Q = -x³ I`, `x⁻¹ P + x Q = -x⁻³ I` has the solution
`P = (-x² - x⁻²) I`, `Q = I`. -/
private theorem solve_kauffman_system_jwTrace {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] (x : K) (hx : x ≠ 0) (hd : x ^ 2 - x⁻¹ ^ 2 ≠ 0) (P Q I : M)
    (h1 : x • P + x⁻¹ • Q = (-x ^ 3) • I) (h2 : x⁻¹ • P + x • Q = (-x⁻¹ ^ 3) • I) :
    P = (-x ^ 2 - x⁻¹ ^ 2) • I ∧ Q = I := by
  have hP : P = (-x ^ 2 - x⁻¹ ^ 2) • I := by
    apply smul_right_injective M hd
    change (x ^ 2 - x⁻¹ ^ 2) • P = (x ^ 2 - x⁻¹ ^ 2) • (-x ^ 2 - x⁻¹ ^ 2) • I
    have h3 : (x ^ 2 - x⁻¹ ^ 2) • P = x • (x • P + x⁻¹ • Q) - x⁻¹ • (x⁻¹ • P + x • Q) := by
      module
    rw [h3, h1, h2]
    module
  refine ⟨hP, ?_⟩
  have hQ : x⁻¹ • Q = (-x ^ 3) • I - x • P := eq_sub_of_add_eq' h1
  calc Q = (x * x⁻¹) • Q := by rw [mul_inv_cancel₀ hx, one_smul]
    _ = x • ((-x ^ 3) • I - x • P) := by rw [mul_smul, hQ]
    _ = (x * x⁻¹) ^ 2 • I := by rw [hP]; module
    _ = I := by rw [mul_inv_cancel₀ hx, one_pow, one_smul]

/-- The partial trace over the last strand of the identity and of the last generator. -/
private theorem ptrTail_one_and_tlGenF_jwTrace (n : ℕ) :
    ptrTail (n + 1) (n + 2) (1 : SkMat (n + 2) (n + 2)) =
        (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) • (1 : SkMat (n + 1) (n + 1)) ∧
      ptrTail (n + 1) (n + 2) (tlGenF (n + 2) n) = 1 := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have e2 : (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) = RatFunc.X ^ 2 := by norm_cast
  have e2' : (RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ) = RatFunc.X⁻¹ ^ 2 := by
    rw [zpow_neg, inv_pow]; norm_cast
  have e3 : (RatFunc.X : RatFunc ℚ) ^ (3 : ℤ) = RatFunc.X ^ 3 := by norm_cast
  have e3' : (RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ) = RatFunc.X⁻¹ ^ 3 := by
    rw [zpow_neg, inv_pow]; norm_cast
  have hd : (RatFunc.X : RatFunc ℚ) ^ 2 - RatFunc.X⁻¹ ^ 2 ≠ 0 := by
    rw [← e2, ← e2']; exact claspAlg_ratFuncX_sq_sub_ne_zero
  have hp := ptrTail_crossingF_last n true
  have hm := ptrTail_crossingF_last n false
  rw [crossingF_pos, ptrTail_add, ptrTail_smul, ptrTail_smul] at hp
  rw [crossingF_neg, ptrTail_add, ptrTail_smul, ptrTail_smul] at hm
  simp only [↓reduceIte, e3] at hp
  simp only [Bool.false_eq_true, ↓reduceIte, e3'] at hm
  rw [e2, e2']
  exact solve_kauffman_system_jwTrace RatFunc.X hX hd _ _ _ hp hm

/-- The partial trace of the identity of one strand is `δ`. -/
private theorem ptrTail_zero_one_one_jwTrace :
    ptrTail 0 1 (1 : SkMat 1 1) =
      (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) • (1 : SkMat 0 0) := by
  ext a b
  obtain rfl : a = b := Subsingleton.elim _ _
  simp only [ptrTail, Matrix.of_apply, Matrix.one_apply_eq, mul_one, Matrix.smul_apply,
    smul_eq_mul]
  change ∑ s : Fin 1 → Bool, ∏ x, skWeightEntry (s x) = _
  rw [← Fintype.sum_pow, pow_one, Fintype.sum_bool, skWeightEntry, skWeightEntry]
  simp only [↓reduceIte, Bool.false_eq_true]
  ring

/-- The partial trace of `f_{k+1}` over its last strand is `-([k+2]/[k+1]) f_k`. -/
theorem ptrTail_jwAt (k : ℕ) :
    ptrTail k (k + 1) (jwAt (k + 1) 0 (k + 1)) =
      -(quantumInt ((k : ℤ) + 2) / quantumInt ((k : ℤ) + 1)) • jwAt k 0 k := by
  cases k with
  | zero =>
    have h0 : quantumInt ((0 : ℕ) : ℤ) = 0 := by simp [quantumInt]
    have hs := loop_add_quantumInt_div 0
    rw [h0, zero_div, add_zero] at hs
    rw [← hs, jwAt, jwAt]
    exact ptrTail_zero_one_one_jwTrace
  | succ m =>
    obtain ⟨hone, hgen⟩ := ptrTail_one_and_tlGenF_jwTrace m
    have hF : jwAt (m + 2) 0 (m + 1) = skPlace (m + 2) (m + 2) 0 (jwAt (m + 1) 0 (m + 1)) :=
      jwAt_eq_skPlace (m + 2) 0 (m + 1) (by omega)
    have hs := loop_add_quantumInt_div (m + 1)
    rw [show (((m + 1 : ℕ) : ℤ)) = (m : ℤ) + 1 from by push_cast; ring,
      show (m : ℤ) + 1 + 1 = (m : ℤ) + 2 from by ring] at hs ⊢
    have h1 : ptrTail (m + 1) (m + 2) (jwAt (m + 2) 0 (m + 1)) =
        (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) • jwAt (m + 1) 0 (m + 1) := by
      rw [hF]
      nth_rewrite 1 [← Matrix.mul_one (skPlace (m + 2) (m + 2) 0 (jwAt (m + 1) 0 (m + 1)))]
      rw [ptrTail_skPlace_mul (m + 1) (m + 2) (by omega), hone, Matrix.mul_smul, Matrix.mul_one]
    have h2 : ptrTail (m + 1) (m + 2)
        (jwAt (m + 2) 0 (m + 1) * tlGenF (m + 2) (0 + m) * jwAt (m + 2) 0 (m + 1)) =
        jwAt (m + 1) 0 (m + 1) := by
      rw [hF, Matrix.mul_assoc, ptrTail_skPlace_mul (m + 1) (m + 2) (by omega),
        ptrTail_mul_skPlace (m + 1) (m + 2) (by omega), Nat.zero_add, hgen, Matrix.one_mul,
        jwAt_mul_self]
    rw [show jwAt (m + 1 + 1) 0 (m + 1 + 1) = jwAt (m + 2) 0 (m + 1) +
      (quantumInt ((m : ℤ) + 1) / quantumInt ((m : ℤ) + 2)) • (jwAt (m + 2) 0 (m + 1) *
        tlGenF (m + 2) (0 + m) * jwAt (m + 2) 0 (m + 1)) from by rw [jwAt],
      ptrTail_add, ptrTail_smul, h1, h2, ← add_smul, hs]

/-- The quantum trace of a scalar multiple. -/
theorem qtr_smul (n : ℕ) (x : RatFunc ℚ) (A : SkMat n n) :
    qtr n (x • A) = x * qtr n A := by
  rw [qtr, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, qtr]

/-- The quantum trace of `f_k` is `Δ_k = (-1)^k [k+1]`. -/
theorem qtr_jwAt (k : ℕ) : qtr k (jwAt k 0 k) = loopScalar k := by
  induction k with
  | zero =>
    have h1 : quantumInt ((0 : ℕ) + 1 : ℤ) = 1 := by
      rw [quantumInt]
      exact div_self (by simpa using claspAlg_ratFuncX_sq_sub_ne_zero)
    rw [loopScalar, pow_zero, one_mul, h1, jwAt]
    simp [qtr, skWeight, Matrix.trace]
  | succ k ih =>
    have h1 : quantumInt ((k : ℤ) + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
    rw [qtr_eq_qtr_ptrTail k (k + 1) (by omega), ptrTail_jwAt, qtr_smul, ih, loopScalar,
      loopScalar, show (((k + 1 : ℕ) : ℤ)) + 1 = (k : ℤ) + 2 from by push_cast; ring, pow_succ]
    field_simp

end AJConjecture
