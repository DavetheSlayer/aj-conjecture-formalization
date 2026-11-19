import Mathlib
import AJConjecture.QAlgGaugeToUnreduced
import AJConjecture.QAlgGaugeOpApply
import AJConjecture.QAlgHomogenizeOpApply
import AJFamily.Quantum.TailMinimalDegreeGeneric

/-!
# The exact minimal order of tail annihilators from a transfer identity

Let `P` be a recurrence operator of order `d` without right pseudo-factors of intermediate order,
and `F` a sequence, not eventually rational, with `δ P F = β` on positive colours and `P F`
eventually nonzero (the transfer identity `P_m F = ρ` with rational forcing `ρ = β/δ ≠ 0`). Then
the annihilators of positive tails of `F` have minimal order exactly `d + 1`: the homogenized row
`(L - τ(ρ)/ρ) P` (`homogenizeOp`) has order `d + 1` and annihilates `F` on positive colours, and
every nonzero tail annihilator has order `> d` (`natDegree_lt_of_tail_annihilator_of_irreducible`).
The same holds for the unreduced sequence `J(n) = [n] F(n)`: the quantum-dimension gauge
preserves the order in both directions (`exists_gauge_quantumInt_mul_natDegree`, `gaugeOp`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The weight `t^(2k) ∏_{l ≤ r, l ≠ k} (t^(4l) M² - 1)` multiplying the coefficient of `L^k`. -/
private def tailGaugeWeight (r k : ℕ) : Coeff :=
  C (X ^ (2 * k)) * ∏ l ∈ (Finset.range (r + 1)).erase k, (C (X ^ (4 * l)) * X ^ 2 - 1)

/-- The value of `t^(4l) M² - 1` at the colour `n`. -/
private theorem evalAtField_tailGaugeFactor (n : ℤ) (l : ℕ) :
    evalAtField n (C (X ^ (4 * l)) * X ^ 2 - 1 : Coeff) =
      RatFunc.X ^ (4 * l) * (RatFunc.X ^ (2 * n)) ^ 2 - 1 := by
  simp only [evalAtField, coe_eval₂RingHom, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow,
    eval₂_one]

/-- The factor `t^(4l) M² - 1` is not zero. -/
private theorem tailGaugeFactor_ne_zero (l : ℕ) :
    (C (X ^ (4 * l)) * X ^ 2 - 1 : Coeff) ≠ 0 := by
  intro h0
  have h1 := congrArg (fun p : Coeff ↦ p.coeff 2) h0
  simp only [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_one, coeff_zero] at h1
  norm_num at h1

/-- The gauge weight is not zero. -/
private theorem tailGaugeWeight_ne_zero (r k : ℕ) : tailGaugeWeight r k ≠ 0 :=
  mul_ne_zero (C_ne_zero.mpr (pow_ne_zero _ X_ne_zero))
    (Finset.prod_ne_zero_iff.mpr fun l _ ↦ tailGaugeFactor_ne_zero l)

/-- `t^(2k) [n + k] = t^(-2n) (t² - t⁻²)⁻¹ (t^(4k) M² - 1)` at `M = t^(2n)`. -/
private theorem ratFuncX_pow_mul_quantumInt_add_tail (n : ℤ) (k : ℕ) :
    (RatFunc.X : RatFunc ℚ) ^ (2 * k) * quantumInt (n + k) =
      RatFunc.X ^ (-(2 * n)) * (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))⁻¹ *
        (RatFunc.X ^ (4 * k) * (RatFunc.X ^ (2 * n)) ^ 2 - 1) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have e1 : (RatFunc.X : RatFunc ℚ) ^ (2 * (n + k)) =
      RatFunc.X ^ n * RatFunc.X ^ n * (RatFunc.X ^ k * RatFunc.X ^ k) := by
    have h2 : (2 * (n + k) : ℤ) = n + n + (k + k) := by ring
    rw [h2, zpow_add₀ hX, zpow_add₀ hX, zpow_add₀ hX, zpow_natCast]
  have e2 : (RatFunc.X : RatFunc ℚ) ^ (2 * n) = RatFunc.X ^ n * RatFunc.X ^ n := by
    rw [two_mul, zpow_add₀ hX]
  have e3 : (RatFunc.X : RatFunc ℚ) ^ (2 * k) = RatFunc.X ^ k * RatFunc.X ^ k := by
    rw [two_mul, pow_add]
  have e4 : (RatFunc.X : RatFunc ℚ) ^ (4 * k) =
      RatFunc.X ^ k * RatFunc.X ^ k * (RatFunc.X ^ k * RatFunc.X ^ k) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  have hT : (RatFunc.X : RatFunc ℚ) ^ n ≠ 0 := zpow_ne_zero _ hX
  have hS : (RatFunc.X : RatFunc ℚ) ^ k ≠ 0 := pow_ne_zero _ hX
  rw [quantumInt, zpow_neg, zpow_neg, zpow_neg, e1, e2, e3, e4, div_eq_mul_inv]
  generalize ((RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - (RatFunc.X ^ (2 : ℤ))⁻¹)⁻¹ = c
  generalize (RatFunc.X : RatFunc ℚ) ^ n = T at hT ⊢
  generalize (RatFunc.X : RatFunc ℚ) ^ k = S at hS ⊢
  field_simp

/-- The value of the gauge weight at the colour `n`, times `[n + k]`, does not depend on `k`. -/
private theorem evalAtField_tailGaugeWeight_mul_quantumInt (r : ℕ) (n : ℤ) {k : ℕ}
    (hk : k ∈ Finset.range (r + 1)) :
    evalAtField n (tailGaugeWeight r k) * quantumInt (n + k) =
      RatFunc.X ^ (-(2 * n)) * (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))⁻¹ *
        ∏ l ∈ Finset.range (r + 1), (RatFunc.X ^ (4 * l) * (RatFunc.X ^ (2 * n)) ^ 2 - 1) := by
  have hC : evalAtField n (C (X ^ (2 * k)) : Coeff) = RatFunc.X ^ (2 * k) := by
    simp only [evalAtField, coe_eval₂RingHom, eval₂_C, eval₂_X, eval₂_pow]
  rw [tailGaugeWeight, map_mul, map_prod, hC, ← Finset.mul_prod_erase _ _ hk,
    Finset.prod_congr rfl fun l _ ↦ evalAtField_tailGaugeFactor n l,
    mul_right_comm, ratFuncX_pow_mul_quantumInt_add_tail, mul_assoc]

/-- The action of an operator given by its coefficients up to a degree. -/
private theorem opApplyField_sum_range_monomial_tail (N : ℕ) (c : ℕ → Coeff)
    (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (∑ k ∈ Finset.range N, monomial k (c k)) f n =
      ∑ k ∈ Finset.range N, evalAtField n (c k) * f (n + k) := by
  induction N with
  | zero => simp [opApplyField]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, opApplyField_add_left, ih,
      opApplyField_monomial]

/-- The specialisation of the gauge weight at `t = -1` is `(M² - 1) ^ r`. -/
private theorem map_tailGaugeWeight {r k : ℕ} (hk : k ≤ r) :
    (tailGaugeWeight r k).map (Polynomial.evalRingHom (-1 : ℤ)) = (X ^ 2 - 1) ^ r := by
  have hmem : k ∈ Finset.range (r + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  have h4 : ∀ l : ℕ, 4 * l = 2 * (2 * l) := fun l ↦ by ring
  simp only [tailGaugeWeight, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, coe_evalRingHom,
    eval_pow, eval_X, h4, pow_mul, neg_one_sq, one_pow, C_1, one_mul, Finset.prod_const,
    Finset.card_erase_of_mem hmem, Finset.card_range, Nat.add_sub_cancel]

/-- The forward gauge, with its order bound and its specialisation. -/
private theorem exists_tailGauge (Q₀ : RecOp) :
    ∃ Q : RecOp, (Q₀ ≠ 0 → Q ≠ 0) ∧ Q.natDegree ≤ Q₀.natDegree ∧
      specialize Q = C ((X ^ 2 - 1) ^ Q₀.natDegree) * specialize Q₀ ∧
      ∀ (g : ℤ → RatFunc ℚ) (n : ℤ),
        opApplyField Q₀ g n = 0 → opApplyField Q (fun m ↦ quantumInt m * g m) n = 0 := by
  set r : ℕ := Q₀.natDegree with hr
  have hcoeff : ∀ k : ℕ, (∑ j ∈ Finset.range (r + 1),
      monomial j (Q₀.coeff j * tailGaugeWeight r j)).coeff k =
        if k ≤ r then Q₀.coeff k * tailGaugeWeight r k else 0 := fun k ↦ by
    rw [finsetSum_coeff]
    split_ifs with hk
    · rw [Finset.sum_eq_single k]
      · exact coeff_monomial_same _ _
      · exact fun j _ hj ↦ coeff_monomial_of_ne _ (Ne.symm hj)
      · exact fun h ↦ absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) h
    · exact Finset.sum_eq_zero fun j hj ↦ coeff_monomial_of_ne _ fun h ↦ hk
        (h ▸ Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  refine ⟨∑ k ∈ Finset.range (r + 1), monomial k (Q₀.coeff k * tailGaugeWeight r k),
    fun hQ₀ hzero ↦ ?_, ?_, ?_, fun g n hann ↦ ?_⟩
  · have h0 := hcoeff r
    simp only [hzero, coeff_zero, le_refl, ite_true] at h0
    exact mul_ne_zero (by rw [hr, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hQ₀)
      (tailGaugeWeight_ne_zero r r) h0.symm
  · refine natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  · ext k : 2
    simp only [specialize, coe_mapRingHom, coeff_map, coeff_C_mul, hcoeff]
    split_ifs with hk
    · rw [Polynomial.map_mul, map_tailGaugeWeight hk, mul_comm]
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hk), Polynomial.map_zero, mul_zero]
  · rw [opApplyField_eq_sum_range, ← hr] at hann
    rw [opApplyField_sum_range_monomial_tail]
    have hmul := congrArg (fun x ↦ RatFunc.X ^ (-(2 * n)) *
      (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))⁻¹ *
        (∏ l ∈ Finset.range (r + 1), (RatFunc.X ^ (4 * l) * (RatFunc.X ^ (2 * n)) ^ 2 - 1)) *
          x) hann
    simp only [mul_zero, Finset.mul_sum] at hmul
    rw [← hmul]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← evalAtField_tailGaugeWeight_mul_quantumInt r n hk, map_mul]
    ring

/-- The library's gauge from `g` to `n ↦ [n] g(n)`, with the order bound made explicit. -/
theorem exists_gauge_quantumInt_mul_natDegree (Q₀ : RecOp) :
    ∃ Q : RecOp, (Q₀ ≠ 0 → Q ≠ 0) ∧ Q.natDegree ≤ Q₀.natDegree ∧ ∀ (g : ℤ → RatFunc ℚ) (n : ℤ),
      opApplyField Q₀ g n = 0 → opApplyField Q (fun m ↦ quantumInt m * g m) n = 0 := by
  obtain ⟨Q, h0, hdeg, -, hann⟩ := exists_tailGauge Q₀
  exact ⟨Q, h0, hdeg, hann⟩

/-- The coefficients of the gauged operator. -/
private theorem coeff_gaugeOp_tail (Q : RecOp) (k : ℕ) :
    (gaugeOp Q).coeff k =
      Q.coeff k * (C (X ^ (2 * (Q.natDegree - k))) * (C (X ^ (4 * k)) * X ^ 2 - 1)) := by
  rw [gaugeOp, Polynomial.sum_def, finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · exact coeff_monomial_same _ _
  · intro j _ hj
    exact coeff_monomial_of_ne _ (Ne.symm hj)
  · intro hk
    rw [notMem_support_iff.mp hk, zero_mul, monomial_zero_right, coeff_zero]

/-- The gauge does not raise the order. -/
private theorem natDegree_gaugeOp_le_tail (Q : RecOp) : (gaugeOp Q).natDegree ≤ Q.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ by
    rw [coeff_gaugeOp_tail, coeff_eq_zero_of_natDegree_lt hk, zero_mul]

/-- The gauge of a nonzero operator is nonzero. -/
private theorem gaugeOp_ne_zero_tail {Q : RecOp} (hQ : Q ≠ 0) : gaugeOp Q ≠ 0 := by
  intro h0
  have h1 := congrArg (fun p : RecOp ↦ p.coeff Q.natDegree) h0
  simp only [coeff_gaugeOp_tail, coeff_zero, coeff_natDegree] at h1
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hQ)
    (mul_ne_zero (C_ne_zero.mpr (pow_ne_zero _ X_ne_zero)) (tailGaugeFactor_ne_zero _)) h1

/-- A nonzero annihilator of a tail of `[n] F` gives one of `F` of no larger order. -/
private theorem exists_tail_annihilator_of_quantumInt_mul {F J : ℤ → RatFunc ℚ}
    (hJ : ∀ n : ℤ, 1 ≤ n → J n = quantumInt n * F n) {G : RecOp} (hG : G ≠ 0)
    (hann : ∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n → opApplyField G J n = 0) :
    ∃ G' : RecOp, G' ≠ 0 ∧ G'.natDegree ≤ G.natDegree ∧
      ∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n → opApplyField G' F n = 0 := by
  obtain ⟨n₁, hn₁⟩ := hann
  refine ⟨gaugeOp G, gaugeOp_ne_zero_tail hG, natDegree_gaugeOp_le_tail G, max n₁ 1,
    fun n hn ↦ ?_⟩
  rw [opApplyField_gaugeOp]
  have hval : opApplyField G (fun m ↦ quantumInt m * F m) n = opApplyField G J n := by
    rw [opApplyField_eq_sum_range, opApplyField_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hJ (n + k) (by have := le_of_max_le_right hn; omega)]
  rw [hval, hn₁ n (le_of_max_le_left hn), mul_zero]

/-- The tail minimal order is `d + 1`, for `F` and for `J = [n] F`. -/
theorem tailOrder_of_transfer {P : RecOp} (hP : 0 < P.natDegree)
    (hirr : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree = 0 ∨ R.natDegree = P.natDegree)
    {F : ℤ → RatFunc ℚ} (hnr : ¬ EventuallyRational F)
    (hrhs : ∃ β δ : Coeff, δ ≠ 0 ∧ ∀ n : ℤ, 1 ≤ n →
      evalAtField n δ * opApplyField P F n = evalAtField n β)
    (hne : ∃ n₂ : ℤ, ∀ n : ℤ, n₂ ≤ n → opApplyField P F n ≠ 0) {J : ℤ → RatFunc ℚ}
    (hJ : ∀ n : ℤ, 1 ≤ n → J n = quantumInt n * F n) :
    (∃ G : RecOp, G ≠ 0 ∧ G.natDegree = P.natDegree + 1 ∧
        ∀ n : ℤ, 1 ≤ n → opApplyField G F n = 0) ∧
      (∀ G : RecOp, G ≠ 0 → (∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n → opApplyField G F n = 0) →
        P.natDegree + 1 ≤ G.natDegree) ∧
      (∃ G : RecOp, G ≠ 0 ∧ G.natDegree = P.natDegree + 1 ∧
        ∀ n : ℤ, 1 ≤ n → opApplyField G J n = 0) ∧
      (∀ G : RecOp, G ≠ 0 → (∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n → opApplyField G J n = 0) →
        P.natDegree + 1 ≤ G.natDegree) := by
  have hP0 : P ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hP; exact lt_irrefl 0 hP
  have hlow : ∀ G : RecOp, G ≠ 0 → (∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n → opApplyField G F n = 0) →
      P.natDegree + 1 ≤ G.natDegree := fun G hG ⟨n₁, hn₁⟩ ↦
    natDegree_lt_of_tail_annihilator_of_irreducible hP0 hirr hnr hrhs hne hG hn₁
  have hlowJ : ∀ G : RecOp, G ≠ 0 → (∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n → opApplyField G J n = 0) →
      P.natDegree + 1 ≤ G.natDegree := fun G hG hann ↦ by
    obtain ⟨G', hG', hdeg, hann'⟩ := exists_tail_annihilator_of_quantumInt_mul hJ hG hann
    exact (hlow G' hG' hann').trans hdeg
  obtain ⟨β, δ, hδ, hβδ⟩ := hrhs
  have hβ : β ≠ 0 := by
    rintro rfl
    obtain ⟨n₂, hn₂⟩ := hne
    obtain ⟨n₀, hn₀⟩ := exists_forall_ge_evalAtField_ne_zero hδ
    have h := hβδ (max (max n₂ n₀) 1) (le_max_right _ _)
    rw [map_zero] at h
    exact mul_ne_zero (hn₀ _ ((le_max_right _ _).trans (le_max_left _ _)))
      (hn₂ _ ((le_max_left _ _).trans (le_max_left _ _))) h
  have hH : ∀ n : ℤ, 1 ≤ n → opApplyField (homogenizeOp β δ P) F n = 0 := fun n hn ↦
    opApplyField_homogenizeOp_eq_zero (hβδ n hn) (hβδ (n + 1) (by omega))
  have hHdeg := natDegree_homogenizeOp hβ hδ hP0
  have hH0 : homogenizeOp β δ P ≠ 0 := fun h ↦ by
    rw [h, natDegree_zero] at hHdeg
    omega
  obtain ⟨Q, hQ0, hQdeg, hQ⟩ := exists_gauge_quantumInt_mul_natDegree (homogenizeOp β δ P)
  have hQJ : ∀ n : ℤ, 1 ≤ n → opApplyField Q J n = 0 := fun n hn ↦ by
    have h := hQ F n (hH n hn)
    rw [opApplyField_eq_sum_range] at h ⊢
    rw [← h]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hJ (n + k) (by omega)]
  refine ⟨⟨_, hH0, hHdeg, hH⟩, hlow, ⟨Q, hQ0 hH0, ?_, hQJ⟩, hlowJ⟩
  exact le_antisymm (hQdeg.trans hHdeg.le) (hlowJ Q (hQ0 hH0) ⟨1, hQJ⟩)

/-- The gauge from `g` to `n ↦ [n] g(n)`, with its order bound and its specialisation at
`t = -1`: the specialisation is multiplied by `(M² - 1) ^ deg Q₀`. -/
theorem exists_gauge_quantumInt_mul_specialize (Q₀ : RecOp) :
    ∃ Q : RecOp, (Q₀ ≠ 0 → Q ≠ 0) ∧ Q.natDegree ≤ Q₀.natDegree ∧
      specialize Q = C ((X ^ 2 - 1) ^ Q₀.natDegree) * specialize Q₀ ∧
      ∀ (g : ℤ → RatFunc ℚ) (n : ℤ),
        opApplyField Q₀ g n = 0 → opApplyField Q (fun m ↦ quantumInt m * g m) n = 0 :=
  exists_tailGauge Q₀

end AJConjecture
