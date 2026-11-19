import Mathlib
import AJConjecture.RecurrenceIdeal

/-!
# Uniqueness of the recurrence polynomial

Two recurrence polynomials of the same sequence are associated (they differ by a sign): both
have minimal degree, a combination cancelling the leading terms lies in the localised
annihilator and has smaller degree, hence vanishes, and both are primitive.
-/

open Polynomial LaurentPolynomial

namespace AJConjecture

/-- The action of recurrence operators on a sequence is additive in the operator. -/
private theorem opApply_add_op (P Q : RecOp) (f : ℤ → ℤ[T;T⁻¹]) (n : ℤ) :
    opApply (P + Q) f n = opApply P f n + opApply Q f n := by
  unfold opApply
  exact Polynomial.sum_add_index P Q _ (by simp) (by intros; simp [add_mul])

/-- A left coefficient multiple of an operator acts by the evaluated coefficient. -/
private theorem opApply_C_mul_op (c : Coeff) (P : RecOp) (f : ℤ → ℤ[T;T⁻¹]) (n : ℤ) :
    opApply (Polynomial.C c * P) f n = evalAt n c * opApply P f n := by
  unfold opApply
  rw [Polynomial.C_mul', Polynomial.sum_smul_index _ _ _ (by simp), Polynomial.sum_def,
    Polynomial.sum_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_mul, mul_assoc]

/-- If nonzero coefficient multiples of `α` and `β` annihilate `f`, then every coefficient
combination `C b * α - C a * β` lies in the localised annihilator of `f`. -/
private theorem inLocalizedAnnihilator_C_mul_sub_C_mul {f : ℤ → ℤ[T;T⁻¹]} {α β : RecOp}
    (hα : InLocalizedAnnihilator f α) (hβ : InLocalizedAnnihilator f β) (a b : Coeff) :
    InLocalizedAnnihilator f (Polynomial.C b * α - Polynomial.C a * β) := by
  obtain ⟨c₁, hc₁, h₁⟩ := hα
  obtain ⟨c₂, hc₂, h₂⟩ := hβ
  refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, fun n ↦ ?_⟩
  have hsplit : Polynomial.C (c₁ * c₂) * (Polynomial.C b * α - Polynomial.C a * β) =
      Polynomial.C (c₂ * b) * (Polynomial.C c₁ * α) +
        Polynomial.C (-(c₁ * a)) * (Polynomial.C c₂ * β) := by
    simp only [map_mul, map_neg]
    ring
  rw [hsplit, opApply_add_op, opApply_C_mul_op (c₂ * b), opApply_C_mul_op (-(c₁ * a)), h₁ n,
    h₂ n, mul_zero, mul_zero, add_zero]

/-- The combination of two operators of the same degree that cancels the leading terms is zero
as soon as its degree is not smaller than the common degree. -/
private theorem leadingCoeff_cancel_eq_zero_of_natDegree_le {α β : RecOp}
    (hdeg : α.natDegree = β.natDegree)
    (hle : α.natDegree ≤
      (Polynomial.C β.leadingCoeff * α - Polynomial.C α.leadingCoeff * β).natDegree) :
    Polynomial.C β.leadingCoeff * α - Polynomial.C α.leadingCoeff * β = 0 := by
  set Q : RecOp := Polynomial.C β.leadingCoeff * α - Polynomial.C α.leadingCoeff * β with hQ
  have hub : Q.natDegree ≤ α.natDegree := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_C_mul_le _ _
    · exact (Polynomial.natDegree_C_mul_le _ _).trans hdeg.ge
  have hcoeff : Q.coeff α.natDegree = 0 := by
    rw [hQ, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
    nth_rewrite 2 [hdeg]
    rw [Polynomial.coeff_natDegree, Polynomial.coeff_natDegree, mul_comm, sub_self]
  rw [← Polynomial.leadingCoeff_eq_zero, Polynomial.leadingCoeff, le_antisymm hub hle]
  exact hcoeff

/-- Two primitive operators with `C b * α = C a * β` and `a ≠ 0` are associated. -/
private theorem associated_of_isPrimitive_of_C_mul_eq_C_mul {α β : RecOp} {a b : Coeff}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (ha : a ≠ 0)
    (h : Polynomial.C b * α = Polynomial.C a * β) : Associated α β := by
  have hcont : normalize b = normalize a := by
    have := congrArg Polynomial.content h
    rwa [Polynomial.content_C_mul, Polynomial.content_C_mul, hα.content_eq_one,
      hβ.content_eq_one, mul_one, mul_one] at this
  have hassoc : Associated a b :=
    (associated_normalize a).trans (hcont ▸ (associated_normalize b).symm)
  obtain ⟨u, rfl⟩ := hassoc
  have hCa : (Polynomial.C a : RecOp) ≠ 0 := by
    rwa [Ne, Polynomial.C_eq_zero]
  have hβeq : Polynomial.C (u : Coeff) * α = β := by
    apply mul_left_cancel₀ hCa
    rw [← h, map_mul, mul_assoc]
  refine ⟨(u.isUnit.map (Polynomial.C : Coeff →+* RecOp)).unit, ?_⟩
  rw [IsUnit.unit_spec, ← hβeq]
  exact mul_comm α _

/-- Two recurrence polynomials of the same sequence are associated. -/
theorem isRecurrencePolynomial_associated {f : ℤ → ℤ[T;T⁻¹]} {α β : RecOp}
    (hα : IsRecurrencePolynomial f α) (hβ : IsRecurrencePolynomial f β) : Associated α β := by
  obtain ⟨hα0, hαin, hαmin, hαprim⟩ := hα
  obtain ⟨hβ0, hβin, hβmin, hβprim⟩ := hβ
  have hdeg : α.natDegree = β.natDegree := le_antisymm (hαmin β hβ0 hβin) (hβmin α hα0 hαin)
  have hQin := inLocalizedAnnihilator_C_mul_sub_C_mul hαin hβin α.leadingCoeff β.leadingCoeff
  have hQ : Polynomial.C β.leadingCoeff * α - Polynomial.C α.leadingCoeff * β = 0 := by
    by_contra hne
    exact hne (leadingCoeff_cancel_eq_zero_of_natDegree_le hdeg (hαmin _ hne hQin))
  exact associated_of_isPrimitive_of_C_mul_eq_C_mul hαprim hβprim
    (Polynomial.leadingCoeff_ne_zero.mpr hα0) (sub_eq_zero.mp hQ)

end AJConjecture
