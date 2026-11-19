import Mathlib
import AJConjecture.QAlgToComparisonUnit
import AJConjecture.QAlgSpecializeOreMul
import AJHandoff.LocalTheory.LocToyMinimum

/-!
# I-CTRL: the constant-output oversized row has minimum `u - 1`

The constant sequence `f_n = 1` is annihilated by `L - 1`, which is its actual minimum: every
annihilator of a tail is a left multiple of `L - 1` up to a nonzero scalar (Theorem S,
homogeneous form). The oversized row `P ⋆ (L - 1)`, `P` the toy operator, also annihilates it,
and its special symbol `(L - M)(L + M - 2)(L - 1)` carries both toy blocks; neither survives in
the minimum. The selected-solution premise of Theorem S fails for this sequence: it is eventually
rational, and it is not a solution of `P` (`P · 1 = -(M - 1)²`). This complements the
predecessor's twist-knot control.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The constant sequence `1`. -/
def constSeq : ℤ → RatFunc ℚ := fun _ ↦ 1

/-- `L - 1` annihilates the constant sequence. -/
private theorem opApplyField_X_sub_one_constSeq (n : ℤ) :
    opApplyField (X - 1) constSeq n = 0 := by
  have h : (X - 1 : RecOp) = monomial 1 1 - monomial 0 1 := by
    rw [monomial_zero_left, ← C_mul_X_pow_eq_monomial, map_one, one_mul, pow_one]
  rw [h, opApplyField_sub_left, opApplyField_monomial, opApplyField_monomial]
  simp [constSeq]

/-- An operator of order one has no right pseudo-factor of intermediate order. -/
private theorem X_sub_one_pseudoIrreducible {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * (X - 1) = oreMul coeffShift S R) :
    R.natDegree = 0 ∨ R.natDegree = (X - 1 : RecOp).natDegree := by
  have hd : (X - 1 : RecOp).natDegree = 1 := natDegree_X_sub_C 1
  have hle : R.natDegree ≤ 1 := by
    have h1 := natDegree_oreMul_le coeffShift S R
    rw [← h, natDegree_C_mul hβ, hd] at h1
    have hS : S ≠ 0 := by
      rintro rfl
      rw [oreMul_zero_left, mul_eq_zero, C_eq_zero] at h
      exact (X_sub_C_ne_zero 1) (h.resolve_left hβ)
    have hR : R ≠ 0 := by
      rintro rfl
      rw [oreMul_zero_right, mul_eq_zero, C_eq_zero] at h
      exact (X_sub_C_ne_zero 1) (h.resolve_left hβ)
    have h2 := natDegree_oreMul coeffShift_injective hS hR
    rw [← h, natDegree_C_mul hβ, hd] at h2
    omega
  rw [hd]
  omega

theorem constSeq_minimum :
    (∀ n : ℤ, opApplyField (X - 1) constSeq n = 0) ∧
      ∀ {Q : RecOp} {n₁ : ℤ}, (∀ n : ℤ, n₁ ≤ n → opApplyField Q constSeq n = 0) →
        ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q = oreMul coeffShift T (X - 1) := by
  refine ⟨opApplyField_X_sub_one_constSeq, fun hQ ↦ ?_⟩
  refine exists_C_mul_eq_oreMul_of_tail_annihilator_of_homogeneous
    (by
      have hd : (X - 1 : RecOp).natDegree = 1 := natDegree_X_sub_C 1
      omega) X_sub_one_pseudoIrreducible ?_ (n₀ := 0)
    (fun n _ ↦ opApplyField_X_sub_one_constSeq n) hQ
  rintro ⟨n₀, hn₀⟩
  exact one_ne_zero (hn₀ n₀ le_rfl)

/-- Evaluating the image in the comparison ring at a unit `L = x`. -/
private theorem eval₂_toComparison_const (p : ℤ[X][X]) (x : (RatFunc ℚ)ˣ) :
    LaurentPolynomial.eval₂ (RingHom.id _) x (toComparison p) =
      p.eval₂ ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)))
        (x : RatFunc ℚ) := by
  simp only [toComparison, RingHom.coe_comp, Function.comp_apply, coe_mapRingHom,
    LaurentPolynomial.eval₂_toLaurent, eval₂_map, RingHom.id_comp]

/-- If `toComparison A ∣ toComparison B` and `A` vanishes at a unit, so does `B`. -/
private theorem eval₂_eq_zero_of_toComparison_dvd {A B : ℤ[X][X]}
    (h : toComparison A ∣ toComparison B) (x : (RatFunc ℚ)ˣ)
    (hA : A.eval₂ ((algebraMap ℚ[X] (RatFunc ℚ)).comp
      (Polynomial.mapRingHom (Int.castRingHom ℚ))) (x : RatFunc ℚ) = 0) :
    B.eval₂ ((algebraMap ℚ[X] (RatFunc ℚ)).comp
      (Polynomial.mapRingHom (Int.castRingHom ℚ))) (x : RatFunc ℚ) = 0 := by
  obtain ⟨c, hc⟩ := h
  rw [← eval₂_toComparison_const, hc, map_mul, eval₂_toComparison_const, hA, zero_mul]

/-- `M - α ≠ 0` in `ℚ(M)`. -/
private theorem ratFunc_X_sub_ne_zero_const (α : ℚ) :
    (RatFunc.X - RatFunc.C α : RatFunc ℚ) ≠ 0 := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
  exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).2 (X_sub_C_ne_zero α)

/-- The oversized row annihilates the constant sequence, but neither toy block divides the
special symbol of the minimum. -/
theorem constSeq_oversized :
    (∀ n : ℤ, opApplyField (oreMul coeffShift toyRecOp (X - 1)) constSeq n = 0) ∧
      specialize (oreMul coeffShift toyRecOp (X - 1)) = (X - C X) * (X + C (X - 2)) * (X - 1) ∧
      ¬ toComparison (X - C X) ∣ toComparison (specialize (X - 1)) ∧
      ¬ toComparison (X + C (X - 2)) ∣ toComparison (specialize (X - 1)) := by
  have hspec : specialize (X - 1) = X - 1 := by simp [specialize]
  refine ⟨fun n ↦ ?_, ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [opApplyField_oreMul]
    simp only [opApplyField_X_sub_one_constSeq]
    rw [opApplyField_eq_sum_range]
    simp
  · rw [specialize_oreMul, toyRecOp_primitive_specialize.2.2, hspec]
  · rw [hspec] at h
    have hx : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
    have := eval₂_eq_zero_of_toComparison_dvd h (Units.mk0 _ hx) (by simp)
    simp only [eval₂_sub, eval₂_X, eval₂_one, Units.val_mk0] at this
    exact ratFunc_X_sub_ne_zero_const 1 (by rw [map_one]; exact this)
  · rw [hspec] at h
    have hx : (2 - RatFunc.X : RatFunc ℚ) ≠ 0 := by
      rw [← neg_sub, neg_ne_zero]
      simpa using ratFunc_X_sub_ne_zero_const 2
    have := eval₂_eq_zero_of_toComparison_dvd h (Units.mk0 _ hx) (by
      simp
      exact sub_eq_zero.2 (map_ofNat _ 2).symm)
    simp only [eval₂_sub, eval₂_X, eval₂_one, Units.val_mk0] at this
    refine ratFunc_X_sub_ne_zero_const 1 ?_
    rw [map_one]
    linear_combination -this

/-- The premise of Theorem S fails: `1` is eventually rational and not a toy solution
(`(P · 1)(n) = -(q^n - 1)²` vanishes only at `n = 0`). -/
theorem constSeq_not_selected :
    EventuallyRational constSeq ∧ ∀ n : ℤ, n ≠ 0 → opApplyField toyRecOp constSeq n ≠ 0 := by
  refine ⟨⟨1, 1, one_ne_zero, 0, fun n _ ↦ by simp [constSeq]⟩, fun n hn h ↦ ?_⟩
  rw [opApplyField_toyRecOp_apply] at h
  simp only [constSeq, mul_one] at h
  have hsq : ((RatFunc.X : RatFunc ℚ) ^ (2 * n) - 1) ^ 2 = 0 := by linear_combination -h
  have h1 : (RatFunc.X : RatFunc ℚ) ^ (2 * n) = 1 :=
    sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hsq)
  have h2 := congrArg RatFunc.intDegree h1
  rw [intDegree_ratFunc_X_zpow, RatFunc.intDegree_one] at h2
  omega

end AJConjecture
