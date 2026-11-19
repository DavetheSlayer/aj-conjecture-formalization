import Mathlib
import AJTwist.Quantum.TwQSymbol
import AJFamily.Quantum.FamSymbolFacts
import AJTwist.Quantum.TwQTwistPolyNegFacts

/-!
# Order, nonvanishing and endpoints of the operators `P_a` (Unit Q3)

Source: revision 5, Section 5.1 (`operators.tex`, "Retention of the shift endpoints": "both shift
endpoints are units at all such `x₀` in every case"), and the table of Section 3.4.

For every integer `a`, with `d = twWindow a`:

`natDegree_twTransferOp`: `P_a` has order `d`, and so has its symbol at `t = -1`
(`natDegree_specialize_twTransferOp`); in particular `P_a ≠ 0` and its symbol is nonzero.

For `a ≥ 1` these are the library's `natDegree_famTransferOp`, `specialize_famTransferOp_ne_zero`;
the cases `a ≤ 0` follow in the same way from `specialize_twTransferOp_mul_eq`, the nonvanishing
of the two scalars (`twDet_one_eval_ne_zero`) and the degree of `twistPolyNeg`. The divisibility
by `E` and the endpoints are in `AJTwist.Quantum.TwQSymbolEnds`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The three shapes of the varying block. -/
private theorem twBlock_cases_twSymbolFacts (a : ℤ) :
    (∃ m : ℕ, 1 ≤ m ∧ a = (m : ℤ) ∧ twBlock a = twistPoly m) ∨ (a = 0 ∧ twBlock a = 1) ∨
      ∃ b : ℕ, 1 ≤ b ∧ a = -(b : ℤ) ∧ twBlock a = twistPolyNeg b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · obtain ⟨b, rfl⟩ : ∃ b : ℕ, a = -(b : ℤ) := ⟨(-a).toNat, by omega⟩
    have h1 : ¬ (1 : ℤ) ≤ -(b : ℤ) := by omega
    have h2 : ¬ -(b : ℤ) = 0 := by omega
    refine Or.inr (Or.inr ⟨b, by omega, rfl, ?_⟩)
    rw [twBlock, ite_eq_right h1, ite_eq_right h2, neg_neg, Int.toNat_natCast]
  · exact Or.inr (Or.inl ⟨rfl, by simp [twBlock]⟩)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = (m : ℤ) := ⟨a.toNat, by omega⟩
    have h1 : (1 : ℤ) ≤ (m : ℤ) := by omega
    refine Or.inl ⟨m, by omega, rfl, ?_⟩
    rw [twBlock, ite_eq_left h1, Int.toNat_natCast]

/-- The varying block has degree `2a`, `0`, `2b - 1`: with `(L - 1) E` the degree is the
window. -/
theorem natDegree_twBlock_add_three (a : ℤ) : (twBlock a).natDegree + 3 = twWindow a := by
  rcases twBlock_cases_twSymbolFacts a with ⟨m, -, rfl, h⟩ | ⟨rfl, h⟩ | ⟨b, hb, rfl, h⟩
  · rw [h, natDegree_twistPoly, twWindow_natCast]
  · rw [h, natDegree_one, twWindow_zero]
  · rw [h, natDegree_twistPolyNeg b hb, twWindow_neg_natCast b hb]
    omega

/-- The varying block is not zero. -/
private theorem twBlock_ne_zero_twSymbolFacts (a : ℤ) : twBlock a ≠ 0 := by
  rcases twBlock_cases_twSymbolFacts a with ⟨m, -, -, h⟩ | ⟨-, h⟩ | ⟨b, hb, -, h⟩
  · rw [h]
    intro h0
    have h' := leadingCoeff_twistPoly m
    rw [h0, leadingCoeff_zero] at h'
    exact pow_ne_zero (4 * m) X_ne_zero h'.symm
  · rw [h]
    exact one_ne_zero
  · rw [h]
    exact (monic_twistPolyNeg b hb).ne_zero

/-- The product `(L - 1) E · twBlock a` has degree `twWindow a` in `L`. -/
private theorem natDegree_symbolProduct_twSymbolFacts (a : ℤ) :
    ((X - 1) * extraFactor * twBlock a : ℤ[X][X]).natDegree = twWindow a := by
  have h1 : (X - 1 : ℤ[X][X]) ≠ 0 :=
    ne_zero_of_natDegree_gt (n := 0) (by rw [natDegree_X_sub_one]; norm_num)
  have h2 : extraFactor ≠ 0 :=
    ne_zero_of_natDegree_gt (n := 0) (by rw [natDegree_extraFactor]; norm_num)
  rw [natDegree_mul (mul_ne_zero h1 h2) (twBlock_ne_zero_twSymbolFacts a), natDegree_mul h1 h2,
    natDegree_X_sub_one, natDegree_extraFactor, ← natDegree_twBlock_add_three a]
  ring

/-- The polynomial in `M` on the left of the symbol identity is not zero. -/
private theorem symbolLeft_ne_zero_twSymbolFacts (d : ℕ) :
    ((X ^ 2 - 1) ^ d * (X ^ 4 - 1) ^ d : ℤ[X]) ≠ 0 := by
  have h2 : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval 0) h
    simp at h0
  have h4 : (X ^ 4 - 1 : ℤ[X]) ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval 0) h
    simp at h0
  exact mul_ne_zero (pow_ne_zero d h2) (pow_ne_zero d h4)

/-- The polynomial in `M` on the right of the symbol identity is not zero. -/
private theorem symbolRight_ne_zero_twSymbolFacts (d : ℕ) :
    ((-1) ^ (d + 1) * ((twDet d (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1))) :
      ℤ[X]) ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) fun h ↦ ?_
  have h0 := twDet_one_eval_ne_zero d (x₀ := 0) (by norm_num) (by norm_num)
  have h1 := congrArg (fun p : ℤ[X] ↦ (p.map (Int.castRingHom ℂ)).eval 0) h
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_comp, map_X, eval_mul, eval_pow, eval_sub, eval_add,
    eval_X, eval_one, eval_comp, Polynomial.map_zero, eval_zero] at h1
  rw [zero_pow two_ne_zero] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact h0 h2
  · norm_num at h2

/-- The symbol of `P_a` is not zero. -/
theorem specialize_twTransferOp_ne_zero (a : ℤ) : specialize (twTransferOp a) ≠ 0 := by
  intro h
  have h1 := specialize_twTransferOp_mul_eq a
  rw [h, mul_zero] at h1
  have h2 : ((X - 1) * extraFactor * twBlock a : ℤ[X][X]) ≠ 0 :=
    mul_ne_zero (mul_ne_zero
      (ne_zero_of_natDegree_gt (n := 0) (by rw [natDegree_X_sub_one]; norm_num))
      (ne_zero_of_natDegree_gt (n := 0) (by rw [natDegree_extraFactor]; norm_num)))
      (twBlock_ne_zero_twSymbolFacts a)
  exact mul_ne_zero (C_ne_zero.mpr (symbolRight_ne_zero_twSymbolFacts (twWindow a))) h2 h1.symm

/-- The symbol of `P_a` has degree `twWindow a` in `L`. -/
theorem natDegree_specialize_twTransferOp (a : ℤ) :
    (specialize (twTransferOp a)).natDegree = twWindow a := by
  have h := congrArg natDegree (specialize_twTransferOp_mul_eq a)
  rwa [natDegree_C_mul (symbolLeft_ne_zero_twSymbolFacts (twWindow a)),
    natDegree_C_mul (symbolRight_ne_zero_twSymbolFacts (twWindow a)),
    natDegree_symbolProduct_twSymbolFacts] at h

/-- The operator `P_a` has order `twWindow a`. -/
theorem natDegree_twTransferOp (a : ℤ) : (twTransferOp a).natDegree = twWindow a := by
  refine le_antisymm ?_ ?_
  · unfold twTransferOp twCramerOp
    refine natDegree_sum_le_of_forall_le _ _ fun k _ ↦ ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · have h : (specialize (twTransferOp a)).natDegree ≤ (twTransferOp a).natDegree := by
      rw [specialize, coe_mapRingHom]
      exact natDegree_map_le
    rwa [natDegree_specialize_twTransferOp a] at h

/-- The operator `P_a` is not zero. -/
theorem twTransferOp_ne_zero (a : ℤ) : twTransferOp a ≠ 0 := by
  intro h
  have h1 := specialize_twTransferOp_ne_zero a
  rw [h, map_zero] at h1
  exact h1 rfl

end AJConjecture
