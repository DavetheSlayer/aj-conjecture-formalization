import Mathlib
import AJConjecture.RecurrenceIdeal
import AJConjecture.UnknotColoredJones

/-!
# The recurrence polynomial of the unknot

The coloured Jones function `[n]` of the unknot has recurrence polynomial
`t² (M² - 1) L - (t⁴ M² - 1)`, whose specialisation at `t = -1` is `(M² - 1) (L - 1)`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The operator `t² (M² - 1) L - (t⁴ M² - 1)` (inner variable `t`, then `M`, outer `L`). -/
def unknotRecurrence : RecOp :=
  Polynomial.C (Polynomial.C (X ^ 2 : ℤ[X]) * (X ^ 2 - 1)) * X
    - Polynomial.C (Polynomial.C (X ^ 4 : ℤ[X]) * X ^ 2 - 1)

/-- The monomials `T a` of the Laurent polynomial ring are pairwise distinct. -/
private theorem laurentT_injective : Function.Injective (T : ℤ → ℤ[T;T⁻¹]) := by
  intro a b hab
  exact (AddMonoidAlgebra.single_left_inj (one_ne_zero (α := ℤ))).mp hab

/-- The action of an operator of `L`-degree at most one. -/
private theorem opApply_C_mul_X_add_C (a b : Coeff) (f : ℤ → ℤ[T;T⁻¹]) (n : ℤ) :
    opApply (Polynomial.C a * X + Polynomial.C b) f n =
      evalAt n a * f (n + 1) + evalAt n b * f n := by
  unfold opApply
  rw [Polynomial.sum_add_index _ _ _ (fun i ↦ by simp) (fun i x y ↦ by simp [add_mul]),
    Polynomial.C_mul_X_eq_monomial, Polynomial.sum_monomial_index _ _ (by simp),
    Polynomial.sum_C_index (by simp)]
  simp

/-- The action of an operator of `L`-degree zero. -/
private theorem opApply_C_coeff (b : Coeff) (f : ℤ → ℤ[T;T⁻¹]) (n : ℤ) :
    opApply (Polynomial.C b) f n = evalAt n b * f n := by
  unfold opApply
  rw [Polynomial.sum_C_index (by simp)]
  simp

/-- The value at any colour of a power of `t`. -/
private theorem evalAt_C_X_pow (n : ℤ) (k : ℕ) :
    evalAt n (Polynomial.C (X ^ k : ℤ[X])) = T (k : ℤ) := by
  rw [evalAt, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X_pow, T_pow, mul_one]

/-- The value at the colour `n` of the variable `M`. -/
private theorem evalAt_X (n : ℤ) : evalAt n (X : Coeff) = T (2 * n) := by
  rw [evalAt, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

/-- The value at the colour `n` of the leading coefficient `t² (M² - 1)`. -/
private theorem evalAt_unknotRecurrence_leading (n : ℤ) :
    evalAt n (Polynomial.C (X ^ 2 : ℤ[X]) * (X ^ 2 - 1)) =
      T 2 * (T (2 * n) * T (2 * n) - 1) := by
  rw [map_mul, map_sub, evalAt_C_X_pow, map_pow, map_one, evalAt_X, pow_two]
  rfl

/-- The value at the colour `n` of the constant coefficient `-(t⁴ M² - 1)`. -/
private theorem evalAt_unknotRecurrence_constant (n : ℤ) :
    evalAt n (-(Polynomial.C (X ^ 4 : ℤ[X]) * X ^ 2 - 1)) =
      -(T 2 * T 2 * (T (2 * n) * T (2 * n)) - 1) := by
  have h4 : (T ((4 : ℕ) : ℤ) : ℤ[T;T⁻¹]) = T 2 * T 2 := by rw [← T_add]; norm_num
  rw [map_neg, map_sub, map_mul, evalAt_C_X_pow, map_pow, map_one, evalAt_X, pow_two, h4]

/-- The operator `t² (M² - 1) L - (t⁴ M² - 1)` annihilates the coloured Jones function of the
unknot. -/
private theorem annihilates_unknotRecurrence :
    Annihilates unknotRecurrence (coloredJones unknot) := by
  intro n
  have hδ : (T 2 : ℤ[T;T⁻¹]) - T (-2) ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ absurd (laurentT_injective h) (by norm_num)
  have huv : (T 2 : ℤ[T;T⁻¹]) * T (-2) = 1 := by rw [← T_add]; simp
  have hxy : (T (2 * n) : ℤ[T;T⁻¹]) * T (-(2 * n)) = 1 := by rw [← T_add]; simp
  have h0 := coloredJones_unknot n
  have h1 := coloredJones_unknot (n + 1)
  have hA : (T (2 * (n + 1)) : ℤ[T;T⁻¹]) = T 2 * T (2 * n) := by
    rw [← T_add]; exact congrArg T (by ring)
  have hB : (T (-(2 * (n + 1))) : ℤ[T;T⁻¹]) = T (-2) * T (-(2 * n)) := by
    rw [← T_add]; exact congrArg T (by ring)
  rw [hA, hB] at h1
  have hP : unknotRecurrence =
      Polynomial.C (Polynomial.C (X ^ 2 : ℤ[X]) * (X ^ 2 - 1)) * X +
        Polynomial.C (-(Polynomial.C (X ^ 4 : ℤ[X]) * X ^ 2 - 1)) := by
    rw [unknotRecurrence, Polynomial.C_neg, sub_eq_add_neg]
  rw [hP, opApply_C_mul_X_add_C, evalAt_unknotRecurrence_leading,
    evalAt_unknotRecurrence_constant]
  apply mul_left_cancel₀ hδ
  linear_combination T 2 * (T (2 * n) * T (2 * n) - 1) * h1 +
    (-(T 2 * T 2 * (T (2 * n) * T (2 * n)) - 1)) * h0 +
    (T (-(2 * n)) - T (2 * n) * T (2 * n) * T (-(2 * n))) * huv +
    T (2 * n) * (T 2 * T 2 - 1) * hxy

/-- The coloured Jones function of the unknot does not vanish at a nonzero colour. -/
private theorem coloredJones_unknot_ne_zero {n : ℤ} (hn : n ≠ 0) : coloredJones unknot n ≠ 0 := by
  intro h
  have h0 := coloredJones_unknot n
  rw [h, mul_zero] at h0
  have := laurentT_injective (sub_eq_zero.mp h0.symm)
  omega

/-- The inner evaluation `t ↦ T 1` from `ℤ[t]` to the Laurent polynomials is injective. -/
private theorem innerEval_injective : Function.Injective
    (Polynomial.eval₂RingHom (Int.castRingHom ℤ[T;T⁻¹]) (T 1)) := by
  have h : Polynomial.eval₂RingHom (Int.castRingHom ℤ[T;T⁻¹]) (T 1) =
      (Polynomial.toLaurent : ℤ[X] →+* ℤ[T;T⁻¹]) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp
    · simp
  rw [h]
  exact Polynomial.toLaurent_injective

/-- A nonzero coefficient `E(t, M)` has a nonzero value at some nonzero colour. -/
private theorem exists_evalAt_ne_zero {E : Coeff} (hE : E ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ evalAt n E ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hmap : E.map (Polynomial.eval₂RingHom (Int.castRingHom ℤ[T;T⁻¹]) (T 1)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff innerEval_injective).mpr hE
  refine hmap (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ ↦ (T (2 * ((k : ℤ) + 1)) : ℤ[T;T⁻¹]))
    (fun a b hab ↦ ?_) fun k ↦ ?_
  · have := laurentT_injective hab
    omega
  · have hk := hcon ((k : ℤ) + 1) (by omega)
    simpa [evalAt, Polynomial.eval₂_eq_eval_map] using hk

/-- No nonzero operator of `L`-degree zero lies in the localised annihilator of the coloured
Jones function of the unknot. -/
private theorem one_le_natDegree_of_inLocalizedAnnihilator_unknot {Q : RecOp} (hQ : Q ≠ 0)
    (h : InLocalizedAnnihilator (coloredJones unknot) Q) : 1 ≤ Q.natDegree := by
  by_contra hdeg
  obtain ⟨c, hc, hann⟩ := h
  have hQC := Polynomial.eq_C_of_natDegree_eq_zero (by omega : Q.natDegree = 0)
  have hD : Q.coeff 0 ≠ 0 := fun h0 ↦ hQ (by rw [hQC, h0, Polynomial.C_0])
  obtain ⟨n, hn, hne⟩ := exists_evalAt_ne_zero (mul_ne_zero hc hD)
  have h0 := hann n
  rw [hQC, ← Polynomial.C_mul, opApply_C_coeff] at h0
  exact (mul_ne_zero hne (coloredJones_unknot_ne_zero hn)) h0

/-- The coefficients `t² (M² - 1)` and `t⁴ M² - 1` have no common non-unit factor. -/
private theorem isPrimitive_unknotRecurrence : unknotRecurrence.IsPrimitive := by
  intro r hr
  rw [Polynomial.C_dvd_iff_dvd_coeff] at hr
  have h1 : r ∣ Polynomial.C (X ^ 2 : ℤ[X]) * (X ^ 2 - 1) := by
    have := hr 1
    rwa [unknotRecurrence, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
      mul_one, Polynomial.coeff_C_of_ne_zero one_ne_zero, sub_zero] at this
  have h0 : r ∣ Polynomial.C (X ^ 4 : ℤ[X]) * X ^ 2 - 1 := by
    have := hr 0
    rw [unknotRecurrence, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
      mul_zero, Polynomial.coeff_C_zero, zero_sub] at this
    exact (dvd_neg).mp this
  have hconst : r ∣ Polynomial.C (1 - X ^ 4 : ℤ[X]) := by
    have := dvd_sub (Dvd.dvd.mul_left h1 (Polynomial.C (X ^ 2 : ℤ[X]))) h0
    convert this using 1
    simp only [Polynomial.C_sub, Polynomial.C_pow, Polynomial.C_1]
    ring
  have hne : (1 - X ^ 4 : ℤ[X]) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  have hdeg : r.natDegree = 0 := by
    have := Polynomial.natDegree_le_of_dvd hconst (Polynomial.C_ne_zero.mpr hne)
    rw [Polynomial.natDegree_C] at this
    exact Nat.le_zero.mp this
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at h1 hconst ⊢
  rw [Polynomial.C_dvd_iff_dvd_coeff] at h1 hconst
  have h2 : r.coeff 0 ∣ (X ^ 2 : ℤ[X]) := by
    have := h1 2
    simpa only [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_one, ↓reduceIte, OfNat.ofNat_ne_zero, sub_zero, mul_one] using this
  have h3 : r.coeff 0 ∣ (1 - X ^ 4 : ℤ[X]) := by
    have := hconst 0
    rwa [Polynomial.coeff_C_zero] at this
  have h4 : r.coeff 0 ∣ 1 := by
    have := dvd_add h3 (Dvd.dvd.mul_left h2 (X ^ 2 : ℤ[X]))
    convert this using 1
    ring
  exact Polynomial.isUnit_C.mpr (isUnit_of_dvd_one h4)

/-- `t² (M² - 1) L - (t⁴ M² - 1)` is the recurrence polynomial of the unknot. -/
theorem isRecurrencePolynomial_unknot :
    IsRecurrencePolynomial (coloredJones unknot) unknotRecurrence := by
  have hlead : Polynomial.C (X ^ 2 : ℤ[X]) * (X ^ 2 - 1) ≠ (0 : Coeff) :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr (pow_ne_zero 2 Polynomial.X_ne_zero))
      (Polynomial.X_pow_sub_C_ne_zero (by norm_num) (1 : ℤ[X]))
  have hdeg : unknotRecurrence.natDegree = 1 := by
    rw [unknotRecurrence, Polynomial.natDegree_sub_C, Polynomial.natDegree_C_mul_X _ hlead]
  refine ⟨fun h ↦ ?_, ⟨1, one_ne_zero, ?_⟩, fun Q hQ hQann ↦ ?_, isPrimitive_unknotRecurrence⟩
  · rw [h, Polynomial.natDegree_zero] at hdeg
    exact zero_ne_one hdeg
  · rw [Polynomial.C_1, one_mul]
    exact annihilates_unknotRecurrence
  · rw [hdeg]
    exact one_le_natDegree_of_inLocalizedAnnihilator_unknot hQ hQann

/-- The specialisation at `t = -1` of the recurrence polynomial of the unknot is
`(M² - 1) (L - 1)`. -/
theorem specialize_unknotRecurrence :
    specialize unknotRecurrence = Polynomial.C (X ^ 2 - 1 : ℤ[X]) * (X - 1) := by
  simp only [specialize, unknotRecurrence, Polynomial.coe_mapRingHom, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow,
    Polynomial.map_one, Polynomial.coe_evalRingHom, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num
  ring

end AJConjecture
