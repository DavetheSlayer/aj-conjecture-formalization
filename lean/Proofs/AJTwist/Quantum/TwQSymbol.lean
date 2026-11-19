import Mathlib
import AJTwist.Quantum.TwQTransferOp
import AJTwist.Quantum.TwQCramerSymbol
import AJTwist.Quantum.TwQTargetAtOne
import AJFamily.Quantum.FamSymbol

/-!
# The symbols of the operators `P_a` (Unit Q3)

Source: revision 5, Section 3.4 (`transfer.tex`), the table after eq. (B): up to units, the
symbol of `P_a` is `(L - 1) E B_a` for `a ≥ 1`, `(L - 1) E` for `a = 0` and `(L - 1) E C_b` for
`a = -b < 0`; Section 5.1 (`operators.tex`), eq. (negative-residue), (Eb).

In the form of the library's `specialize_famTransferOp_mul_eq`, with `d = twWindow a`,
`κ₁ = (M² - 1)^d (M⁴ - 1)^d` and `κ₂ = (-1)^(d+1) det|_{q=1}(M²) (M² + 1)² (M² - 1)`:
`C κ₁ * specialize (twTransferOp a) = C κ₂ * ((L - 1) * E * twBlock a)`,
where `twBlock a` is `twistPoly a`, `1` or `twistPolyNeg b`. The sign is `+` for the odd windows
(`a ≥ 0`) and `-` for the even windows (`a < 0`). For `a ≥ 1` this is the library's theorem.

Checked at random points for `-6 ≤ a ≤ 6` (scratch `check_symbol_mod.py`) and symbolically for
`a = -1, 0, 1`; eq. (negative-residue) and (Eb) of the paper were checked in the paper's
normalization at random points (scratch `check_residue.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The varying block of the symbol of `P_a`: `B_a` for `a ≥ 1`, `1` for `a = 0`, `C_b` for
`a = -b < 0`. -/
def twBlock (a : ℤ) : ℤ[X][X] :=
  if 1 ≤ a then twistPoly a.toNat else if a = 0 then 1 else twistPolyNeg (-a).toNat

/-- The stationary substitution of degree one of `1 - J`. -/
private theorem moebiusSubst_one_sub_X_twSymbol :
    moebiusSubst 1 (1 - X) = -(C (X - 1) * (X - 1)) := by
  rw [moebiusSubst_sub, moebiusSubst_one, show (1 : ℕ) = 0 + 1 from rfl, moebiusSubst_X]
  simp only [C_sub, C_1]
  ring

/-- `(1 - J)(ζ + 2x)` has degree at most three in `J`. -/
private theorem natDegree_one_sub_X_mul_symbolZeta_add_le_twSymbol :
    ((1 - X) * (symbolZeta + C (2 * X)) : ℤ[X][X]).natDegree ≤ 3 := by
  unfold symbolZeta
  compute_degree

/-- The stationary substitution of `(1 - J)(ζ + 2x)`, after `x = M²`. -/
private theorem map_moebiusSubst_commonFactor_twSymbol :
    (moebiusSubst 3 ((1 - X) * (symbolZeta + C (2 * X)))).map (Polynomial.compRingHom (X ^ 2)) =
      -(C (X ^ 2 - 1) * (X - 1)) * (C ((X ^ 2 + 1) ^ 2) * extraFactor) := by
  have hz : (symbolZeta + C (2 * X) : ℤ[X][X]).natDegree ≤ 2 := by
    unfold symbolZeta
    compute_degree
  have h1 : (1 - X : ℤ[X][X]).natDegree ≤ 1 := by compute_degree
  rw [show (3 : ℕ) = 1 + 2 from rfl, moebiusSubst_mul h1 hz, moebiusSubst_one_sub_X_twSymbol,
    Polynomial.map_mul, map_moebiusSubst_symbolZeta_add]
  simp only [Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_sub, map_C, map_X,
    Polynomial.map_one, coe_compRingHom_apply, sub_comp, X_comp, one_comp]

/-- The cleared numerator at `t = -1` is the cleared numerator at `q = 1`. -/
private theorem map_twTarget_specialize_twSymbol (a : ℤ) :
    (twTarget a (X ^ 4 : ℤ[X])).map (Polynomial.mapRingHom (Polynomial.evalRingHom (-1 : ℤ))) =
      twTarget a (1 : ℤ) := by
  rw [map_twTarget, coe_evalRingHom, eval_pow, eval_X]
  norm_num

/-- The symbol of `P_0` is `(L - 1) E` up to nonzero polynomials in `M`. -/
theorem specialize_twTransferOp_zero_mul_eq :
    C ((X ^ 2 - 1) ^ 3 * (X ^ 4 - 1) ^ 3) * specialize (twTransferOp 0) =
      C ((twDet 3 (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1))) *
        ((X - 1) * extraFactor) := by
  have hT : (twZeroTarget (X ^ 4 : ℤ[X])).natDegree ≤ 3 := by
    have h := natDegree_twTarget_le 0 (X ^ 4 : ℤ[X])
    rwa [twTarget_zero, twWindow_zero] at h
  have h := specialize_twCramerOp_mul_eq 3 (twZeroTarget (X ^ 4)) hT
  have hm := map_twTarget_specialize_twSymbol 0
  rw [twTarget_zero, twTarget_zero] at hm
  rw [hm, twZeroTarget_one_eq, map_moebiusSubst_commonFactor_twSymbol,
    ← twTransferOp_zero] at h
  simp only [C_mul, C_pow, C_neg, C_1] at h ⊢
  linear_combination (-1 : ℤ[X][X]) * h

/-- The symbol of `P_(-b)`, `b ≥ 1`, is `(L - 1) E C_b` up to nonzero polynomials in `M`. -/
theorem specialize_twTransferOp_neg_mul_eq (b : ℕ) (hb : 1 ≤ b) :
    C ((X ^ 2 - 1) ^ (2 * b + 2) * (X ^ 4 - 1) ^ (2 * b + 2)) *
        specialize (twTransferOp (-(b : ℤ))) =
      C (-((twDet (2 * b + 2) (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1)))) *
        ((X - 1) * extraFactor * twistPolyNeg b) := by
  have hT : (twNegTarget b (X ^ 4 : ℤ[X])).natDegree ≤ 2 * b + 2 := by
    have h := natDegree_twTarget_le (-(b : ℤ)) (X ^ 4 : ℤ[X])
    rwa [twTarget_neg_natCast b hb, twWindow_neg_natCast b hb] at h
  have h := specialize_twCramerOp_mul_eq (2 * b + 2) (twNegTarget b (X ^ 4)) hT
  have hm := map_twTarget_specialize_twSymbol (-(b : ℤ))
  rw [twTarget_neg_natCast b hb, twTarget_neg_natCast b hb] at hm
  have hsub : moebiusSubst (2 * b + 2)
      ((1 - X) * (symbolZeta + C (2 * X)) * symbolTwistNeg b) =
      moebiusSubst 3 ((1 - X) * (symbolZeta + C (2 * X))) *
        moebiusSubst (2 * b - 1) (symbolTwistNeg b) := by
    rw [show 2 * b + 2 = 3 + (2 * b - 1) by omega,
      moebiusSubst_mul natDegree_one_sub_X_mul_symbolZeta_add_le_twSymbol
        (natDegree_symbolTwistNeg_le b hb)]
  have he : ((-1 : ℤ[X]) ^ (2 * b + 2)) = 1 := (Even.neg_one_pow ⟨b + 1, by ring⟩)
  rw [hm, twNegTarget_one_eq b hb, hsub, Polynomial.map_mul,
    map_moebiusSubst_commonFactor_twSymbol, ← twistPolyNeg, ← twTransferOp_neg_natCast b hb,
    he, one_mul] at h
  simp only [C_mul, C_pow, C_neg] at h ⊢
  linear_combination h

/-- The symbol of `P_a` for every integer `a`. -/
theorem specialize_twTransferOp_mul_eq (a : ℤ) :
    C ((X ^ 2 - 1) ^ twWindow a * (X ^ 4 - 1) ^ twWindow a) * specialize (twTransferOp a) =
      C ((-1) ^ (twWindow a + 1) * ((twDet (twWindow a) (1 : ℤ)).comp (X ^ 2) *
        ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1)))) * ((X - 1) * extraFactor * twBlock a) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · obtain ⟨b, rfl⟩ : ∃ b : ℕ, a = -(b : ℤ) := ⟨(-a).toNat, by omega⟩
    have hb : 1 ≤ b := by omega
    have h1 : ¬ (1 : ℤ) ≤ -(b : ℤ) := by omega
    have h2 : ¬ -(b : ℤ) = 0 := by omega
    have hblock : twBlock (-(b : ℤ)) = twistPolyNeg b := by
      rw [twBlock, ite_eq_right h1, ite_eq_right h2, neg_neg, Int.toNat_natCast]
    have he : ((-1 : ℤ[X]) ^ (2 * b + 2 + 1)) = -1 := (Odd.neg_one_pow ⟨b + 1, by ring⟩)
    rw [twWindow_neg_natCast b hb, hblock, he, neg_one_mul]
    exact specialize_twTransferOp_neg_mul_eq b hb
  · have hblock : twBlock 0 = 1 := by simp [twBlock]
    rw [twWindow_zero, hblock, mul_one, show ((-1 : ℤ[X]) ^ (3 + 1)) = 1 by norm_num, one_mul]
    exact specialize_twTransferOp_zero_mul_eq
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = (m : ℤ) := ⟨a.toNat, by omega⟩
    have hm : 1 ≤ m := by omega
    have h1 : (1 : ℤ) ≤ (m : ℤ) := by omega
    have hblock : twBlock (m : ℤ) = twistPoly m := by
      rw [twBlock, ite_eq_left h1, Int.toNat_natCast]
    have he : ((-1 : ℤ[X]) ^ (2 * m + 3 + 1)) = 1 := (Even.neg_one_pow ⟨m + 2, by ring⟩)
    rw [twWindow_natCast, hblock, he, one_mul, twTransferOp_natCast m hm, ← famDet_eq_twDet]
    exact specialize_famTransferOp_mul_eq m hm

end AJConjecture
