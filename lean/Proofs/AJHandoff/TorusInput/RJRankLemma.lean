import Mathlib
import AJHandoff.TorusInput.RJDefs

/-!
# An idempotent with zero quantum trace vanishes (node RA1.10)

If `E` is idempotent, commutes with the weight `μ^{⊗ m}` and `qtr_m E = 0`, then `E = 0`.

Route. The weight of a state `a` is `(-1)^m t^(2(m - 2|a|))`, `|a|` the number of `true`
entries, so it takes distinct values on distinct weight classes. Since `μ E = E μ`, `E (a, b) = 0`
unless `|a| = |b|`, and `E` is block diagonal; each block `E_w` is idempotent, so its trace is its
rank `n_w ∈ ℕ` (characteristic `0`; `LinearMap.IsProj`, `Matrix.trace` of an idempotent, or
diagonalize `E_w` by `Module.End` idempotents). Then
`0 = qtr E = (-1)^m ∑_w n_w t^(2(m-2w))`, a Laurent polynomial with nonnegative integer
coefficients at distinct exponents; so every `n_w = 0`, every block vanishes and `E = 0`.
Generic linear algebra, independent of the skein theory. Estimate 120–200 lines.
-/

noncomputable section

namespace AJConjecture

/-- The trace of an idempotent matrix is the dimension of its range. -/
private theorem rj_trace_eq_finrank_of_idempotent {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (E : Matrix ι ι K) (hE : E * E = E) :
    E.trace = (Module.finrank K (LinearMap.range (Matrix.toLin' E)) : K) := by
  have hi : IsIdempotentElem (Matrix.toLin' E) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE]
  rw [← (LinearMap.IsIdempotentElem.isProj_range _ hi).trace, Matrix.trace_toLin'_eq]

/-- An idempotent matrix of trace zero over a field of characteristic zero vanishes. -/
private theorem rj_matrix_eq_zero_of_idempotent {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
    [DecidableEq ι] (E : Matrix ι ι K) (hE : E * E = E) (htr : E.trace = 0) : E = 0 := by
  have hi : IsIdempotentElem (Matrix.toLin' E) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE]
  have h0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hi
    (by rw [Matrix.trace_toLin'_eq, htr])
  exact Matrix.toLin'.injective (by rw [h0, map_zero])

/-- The number of `false` entries of a state. -/
private def rjFalseCount {m : ℕ} (a : Fin m → Bool) : ℕ :=
  ∑ k, if a k then 0 else 1

/-- A state of `m` factors has at most `m` entries `false`. -/
private theorem rjFalseCount_le {m : ℕ} (a : Fin m → Bool) : rjFalseCount a ≤ m := by
  calc rjFalseCount a ≤ ∑ _k : Fin m, 1 :=
        Finset.sum_le_sum fun k _ ↦ by split_ifs <;> omega
    _ = m := by simp

/-- The weight of a state: `μ(a) = (-t⁻²)^m (t⁴)^(#false a)`. -/
private theorem rj_prod_skWeightEntry {m : ℕ} (a : Fin m → Bool) :
    ∏ k, skWeightEntry (a k) =
      (-(RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ)) ^ m * (RatFunc.X ^ 4) ^ rjFalseCount a := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have he : ∀ b : Bool, skWeightEntry b =
      -(RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ) * (RatFunc.X ^ 4) ^ (if b then 0 else 1) := by
    intro b
    cases b
    · simp only [skWeightEntry, Bool.false_eq_true, ↓reduceIte, pow_one]
      rw [← zpow_natCast, neg_mul, ← zpow_add₀ hX]
      norm_num
    · simp [skWeightEntry]
  rw [Finset.prod_congr rfl fun k _ ↦ he (a k), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum, rjFalseCount]

/-- `n ↦ (t⁴)^n` is injective. -/
private theorem rj_X_pow_four_pow_injective :
    Function.Injective fun n : ℕ ↦ ((RatFunc.X : RatFunc ℚ) ^ 4) ^ n := by
  intro a b hab
  simp only [← pow_mul] at hab
  rw [← RatFunc.algebraMap_X, ← map_pow, ← map_pow] at hab
  have h := congrArg Polynomial.natDegree (RatFunc.algebraMap_injective ℚ hab)
  simp only [Polynomial.natDegree_X_pow] at h
  omega

/-- A matrix commuting with the weight has no entries between states with different
numbers of `false` entries. -/
private theorem rj_entry_eq_zero_of_falseCount_ne (m : ℕ) (E : SkMat m m)
    (hw : skWeight m * E = E * skWeight m) (a b : Fin m → Bool)
    (hab : rjFalseCount a ≠ rjFalseCount b) : E a b = 0 := by
  have h := congrFun (congrFun hw a) b
  simp only [skWeight, Matrix.diagonal_mul, Matrix.mul_diagonal, rj_prod_skWeightEntry] at h
  by_contra hE
  have hc : (-(RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ)) ^ m ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr (zpow_ne_zero _ RatFunc.X_ne_zero))
  apply hab
  apply rj_X_pow_four_pow_injective
  have h2 := mul_right_cancel₀ hE (h.trans (mul_comm _ _))
  exact mul_left_cancel₀ hc h2

/-- The projector onto the states with `c` entries `false`. -/
private def rjCountProj (m c : ℕ) : SkMat m m :=
  Matrix.diagonal fun a ↦ if rjFalseCount a = c then 1 else 0

/-- The projector onto a weight class commutes with a matrix commuting with the weight. -/
private theorem rj_countProj_comm (m : ℕ) (E : SkMat m m) (hw : skWeight m * E = E * skWeight m)
    (c : ℕ) : rjCountProj m c * E = E * rjCountProj m c := by
  ext a b
  simp only [rjCountProj, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hab : rjFalseCount a = rjFalseCount b
  · rw [hab, mul_comm]
  · rw [rj_entry_eq_zero_of_falseCount_ne m E hw a b hab, mul_zero, zero_mul]

/-- The block of an idempotent on a weight class is idempotent. -/
private theorem rj_countProj_mul_idempotent (m : ℕ) (E : SkMat m m) (hE : E * E = E)
    (hw : skWeight m * E = E * skWeight m) (c : ℕ) :
    (rjCountProj m c * E) * (rjCountProj m c * E) = rjCountProj m c * E := by
  have hDD : rjCountProj m c * rjCountProj m c = rjCountProj m c := by
    simp only [rjCountProj, Matrix.diagonal_mul_diagonal, mul_ite, mul_one, mul_zero]
    congr 1
    funext a
    split_ifs <;> rfl
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, ← rj_countProj_comm m E hw, Matrix.mul_assoc, hE,
    ← Matrix.mul_assoc, hDD]

/-- The quantum trace as a sum over the weight classes. -/
private theorem rj_qtr_eq_sum_countProj (m : ℕ) (E : SkMat m m) :
    qtr m E = (-(RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ)) ^ m *
      ∑ c ∈ Finset.range (m + 1), (RatFunc.X ^ 4) ^ c * (rjCountProj m c * E).trace := by
  rw [qtr, Matrix.trace]
  simp only [skWeight, Matrix.diag_apply, Matrix.diagonal_mul, rj_prod_skWeightEntry]
  rw [← Finset.sum_fiberwise_of_maps_to (g := rjFalseCount) (t := Finset.range (m + 1))
    fun a _ ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (rjFalseCount_le a)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [Matrix.trace, Matrix.diag_apply, rjCountProj, Matrix.diagonal_mul, Finset.mul_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  split_ifs with h
  · rw [h]; ring
  · ring

/-- An idempotent commuting with the weight and with zero quantum trace is zero. -/
theorem rj_eq_zero_of_idempotent_of_qtr_eq_zero (m : ℕ) (E : SkMat m m) (hE : E * E = E)
    (hw : skWeight m * E = E * skWeight m) (htr : qtr m E = 0) : E = 0 := by
  set n : ℕ → ℕ := fun c ↦
    Module.finrank (RatFunc ℚ) (LinearMap.range (Matrix.toLin' (rjCountProj m c * E)))
  have hn : ∀ c, (rjCountProj m c * E).trace = n c := fun c ↦
    rj_trace_eq_finrank_of_idempotent _ (rj_countProj_mul_idempotent m E hE hw c)
  have hc : (-(RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ)) ^ m ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr (zpow_ne_zero _ RatFunc.X_ne_zero))
  rw [rj_qtr_eq_sum_countProj, mul_eq_zero, or_iff_right hc] at htr
  simp only [hn] at htr
  have hp : (∑ c ∈ Finset.range (m + 1), Polynomial.C (n c : ℚ) * Polynomial.X ^ (4 * c) :
      Polynomial ℚ) = 0 := by
    apply RatFunc.algebraMap_injective ℚ
    rw [map_zero, ← htr, map_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, pow_mul, mul_comm]
    simp
  have hn0 : ∀ c ∈ Finset.range (m + 1), n c = 0 := by
    have h1 := congrArg (Polynomial.eval 1) hp
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one, Polynomial.eval_zero] at h1
    exact Finset.sum_eq_zero_iff.mp (by exact_mod_cast h1)
  ext a b
  have hblock : rjCountProj m (rjFalseCount a) * E = 0 :=
    rj_matrix_eq_zero_of_idempotent _ (rj_countProj_mul_idempotent m E hE hw _)
      (by rw [hn, hn0 _ (Finset.mem_range.mpr (Nat.lt_succ_of_le (rjFalseCount_le a))),
        Nat.cast_zero])
  have h := congrFun (congrFun hblock a) b
  simpa [rjCountProj, Matrix.diagonal_mul] using h

end AJConjecture
