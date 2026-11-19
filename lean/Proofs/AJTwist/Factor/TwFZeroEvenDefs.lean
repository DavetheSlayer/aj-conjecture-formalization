import Mathlib
import AJConjecture.QAlgCoeffShift
import AJTwist.Quantum.TwQZeroCoeff

/-!
# The variable `x = M²` for the operator `P_0` (TwF, unit F4)

Source: revision 5, Section 5.6 (`operators.tex`): "The involution `M ↦ -M` commutes with the
shift and fixes `P` … Here `σ(x) = x/q`."

* `twfNegM`, `twfSq`, `twfShiftX`: the automorphism `M ↦ -M`, the substitution `x ↦ M²` and the
  shift `x ↦ t⁴ x` of `ℤ[t][x]` (forward convention: `x = M²`, `M ↦ t² M`);
  `twfSq ∘ twfShiftX = coeffShift ∘ twfSq`; `twfSq` is injective.
* `twfZeroOpX = ∑_k b_(3-k)(t⁴, t¹² x) L^k`, the explicit operator of eq. (zero-coeff) in the
  variable `x`: `twfZeroOpX.map twfSq = twZeroExplicitOp`.
* `exists_twfSq_eq_of_twfNegM_eq`: an element of `ℤ[t][M]` fixed by `M ↦ -M` is a polynomial in
  `M²` (the coefficients of odd degree satisfy `c = -c` in the torsion-free `ℤ[t]`;
  `Polynomial.expand ℤ[X] 2` is `twfSq`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The automorphism `M ↦ -M` of `ℤ[t][M]`. -/
def twfNegM : Coeff →+* Coeff := Polynomial.compRingHom (-X)

/-- The substitution `x ↦ M²` on `ℤ[t][x]`. -/
def twfSq : Coeff →+* Coeff := Polynomial.compRingHom (X ^ 2)

/-- The shift `x ↦ t⁴ x` of `ℤ[t][x]` (`x = M²`, `M ↦ t² M`). -/
def twfShiftX : Coeff →+* Coeff := Polynomial.compRingHom (C (X ^ 4) * X)

/-- The explicit operator `∑_k b_(3-k)(t⁴, t¹² x) L^k` of eq. (zero-coeff) in the variable
`x`. -/
def twfZeroOpX : RecOp :=
  ∑ k : Fin 4, C ((twZeroB (X ^ 4 : ℤ[X]) (Fin.rev k)).comp (C (X ^ 12) * X)) * X ^ (k : ℕ)

theorem twfSq_twfShiftX (c : Coeff) : twfSq (twfShiftX c) = coeffShift (twfSq c) := by
  have hq : (C (X ^ 4) * X : Coeff).comp (X ^ 2) = (X ^ 2 : Coeff).comp (C (X ^ 2) * X) := by
    rw [mul_comp, C_comp, X_comp, X_pow_comp, mul_pow, ← C_pow, ← pow_mul]
  change (c.comp (C (X ^ 4) * X)).comp (X ^ 2) = (c.comp (X ^ 2)).comp (C (X ^ 2) * X)
  rw [comp_assoc, comp_assoc, hq]

theorem twfSq_injective : Function.Injective twfSq :=
  expand_injective (R := ℤ[X]) two_pos

theorem map_twfSq_twfZeroOpX : twfZeroOpX.map twfSq = twZeroExplicitOp := by
  rw [twfZeroOpX, twZeroExplicitOp, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hq : (C (X ^ 12) * X : Coeff).comp (X ^ 2) = C (X ^ 12) * X ^ 2 := by
    rw [mul_comp, C_comp, X_comp]
  have hsq : ∀ b : Coeff, twfSq (b.comp (C (X ^ 12) * X)) = b.comp (C (X ^ 12) * X ^ 2) := by
    intro b
    change (b.comp (C (X ^ 12) * X)).comp (X ^ 2) = b.comp (C (X ^ 12) * X ^ 2)
    rw [comp_assoc, hq]
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, hsq]

/-- An element of `ℤ[t][M]` fixed by `M ↦ -M` is a polynomial in `M²`. -/
theorem exists_twfSq_eq_of_twfNegM_eq {c : Coeff} (h : twfNegM c = c) :
    ∃ c' : Coeff, twfSq c' = c := by
  have h2 : (2 : ℤ[X]) ≠ 0 := by
    rw [← C_ofNat]
    exact C_ne_zero.mpr (by norm_num)
  have hodd : ∀ n : ℕ, ¬ 2 ∣ n → c.coeff n = 0 := by
    intro n hn
    have hc := congrArg (fun p : Coeff ↦ p.coeff n) h
    have hX : (-X : Coeff) = C (-1) * X := by
      rw [C_neg, C_1]
      exact (neg_one_mul (X : Coeff)).symm
    change (c.comp (-X)).coeff n = c.coeff n at hc
    rw [hX, comp_C_mul_X_coeff, (Nat.not_even_iff_odd.mp (mt Even.two_dvd hn)).neg_one_pow]
      at hc
    have h0 : 2 * c.coeff n = 0 := by linear_combination -hc
    exact (mul_eq_zero.mp h0).resolve_left h2
  refine ⟨contract 2 c, ?_⟩
  change expand ℤ[X] 2 (contract 2 c) = c
  ext n : 2
  rw [coeff_expand two_pos, coeff_contract two_ne_zero]
  split_ifs with hn
  · rw [Nat.div_mul_cancel hn]
  · exact (hodd n hn).symm

end AJConjecture
